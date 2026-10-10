import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw21248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw21248step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21248step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw21248step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21248 raw21248Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw21248 raw21248Labels = mixedMoment B raw21248step0 raw21248step0Labels := by
      have hz : ∀ j, raw21248 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21248step0 = (fun i j => raw21248 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21248step0 raw21248; decide +kernel
      have hl : raw21248step0Labels = raw21248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21248 raw21248Labels permutation434 hz
    mixedMoment B raw21248step0 raw21248step0Labels = mixedMoment B raw21248step1 raw21248step1Labels := by
      have ha : raw21248step1 = (fun i j => raw21248step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21248step1 raw21248step0; decide +kernel
      have hl : raw21248step1Labels = raw21248step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21248step0 raw21248step0Labels permutation32 permutation3
    mixedMoment B raw21248step1 raw21248step1Labels = mixedMoment B raw21248step2 raw21248step2Labels := by
      have ha : raw21248step2 = raw21248step1 := by apply Matrix.ext; unfold raw21248step2 raw21248step1; decide +kernel
      have hl : raw21248step1Labels = labelEmbedding6 ∘ raw21248step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21248step1 raw21248step1Labels raw21248step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4461 node4461Labels := by rfl

def raw21249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21249step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21249step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21249step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21249step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21249 raw21249Labels = mixedMoment B node4105 node4105Labels := by
  calc
    mixedMoment B raw21249 raw21249Labels = mixedMoment B raw21249step0 raw21249step0Labels := by
      have hz : ∀ j, raw21249 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21249step0 = (fun i j => raw21249 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21249step0 raw21249; decide +kernel
      have hl : raw21249step0Labels = raw21249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21249 raw21249Labels permutation346 hz
    mixedMoment B raw21249step0 raw21249step0Labels = mixedMoment B raw21249step1 raw21249step1Labels := by
      have ha : raw21249step1 = (fun i j => raw21249step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21249step1 raw21249step0; decide +kernel
      have hl : raw21249step1Labels = raw21249step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21249step0 raw21249step0Labels permutation32 permutation3
    mixedMoment B raw21249step1 raw21249step1Labels = mixedMoment B raw21249step2 raw21249step2Labels := by
      have ha : raw21249step2 = raw21249step1 := by apply Matrix.ext; unfold raw21249step2 raw21249step1; decide +kernel
      have hl : raw21249step1Labels = labelEmbedding6 ∘ raw21249step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21249step1 raw21249step1Labels raw21249step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4105 node4105Labels := by rfl

def raw21250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21250step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21250step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21250step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21250 raw21250Labels = mixedMoment B node4352 node4352Labels := by
  calc
    mixedMoment B raw21250 raw21250Labels = mixedMoment B raw21250step0 raw21250step0Labels := by
      have hz : ∀ j, raw21250 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21250step0 = (fun i j => raw21250 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21250step0 raw21250; decide +kernel
      have hl : raw21250step0Labels = raw21250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21250 raw21250Labels permutation346 hz
    mixedMoment B raw21250step0 raw21250step0Labels = mixedMoment B raw21250step1 raw21250step1Labels := by
      have ha : raw21250step1 = (fun i j => raw21250step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21250step1 raw21250step0; decide +kernel
      have hl : raw21250step1Labels = raw21250step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21250step0 raw21250step0Labels permutation32 permutation3
    mixedMoment B raw21250step1 raw21250step1Labels = mixedMoment B raw21250step2 raw21250step2Labels := by
      have ha : raw21250step2 = raw21250step1 := by apply Matrix.ext; unfold raw21250step2 raw21250step1; decide +kernel
      have hl : raw21250step1Labels = labelEmbedding6 ∘ raw21250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21250step1 raw21250step1Labels raw21250step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4352 node4352Labels := by rfl

def raw21251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21251step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21251step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21251step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21251step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21251 raw21251Labels = mixedMoment B node4290 node4290Labels := by
  calc
    mixedMoment B raw21251 raw21251Labels = mixedMoment B raw21251step0 raw21251step0Labels := by
      have ha : raw21251step0 = (fun i j => raw21251 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21251step0 raw21251; decide +kernel
      have hl : raw21251step0Labels = raw21251Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21251 raw21251Labels permutation176 permutation3
    mixedMoment B raw21251step0 raw21251step0Labels = mixedMoment B raw21251step1 raw21251step1Labels := by
      have ha : raw21251step1 = raw21251step0 := by apply Matrix.ext; unfold raw21251step1 raw21251step0; decide +kernel
      have hl : raw21251step0Labels = labelEmbedding6 ∘ raw21251step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21251step0 raw21251step0Labels raw21251step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4290 node4290Labels := by rfl

def raw21252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21252step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21252step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21252step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21252step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21252step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21252step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21252 raw21252Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw21252 raw21252Labels = mixedMoment B raw21252step0 raw21252step0Labels := by
      have hz : ∀ j, raw21252 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21252step0 = (fun i j => raw21252 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21252step0 raw21252; decide +kernel
      have hl : raw21252step0Labels = raw21252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21252 raw21252Labels permutation520 hz
    mixedMoment B raw21252step0 raw21252step0Labels = mixedMoment B raw21252step1 raw21252step1Labels := by
      have hz : ∀ j, raw21252step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21252step1 = (fun i j => raw21252step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21252step1 raw21252step0; decide +kernel
      have hl : raw21252step1Labels = raw21252step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21252step0 raw21252step0Labels permutation80 hz
    mixedMoment B raw21252step1 raw21252step1Labels = mixedMoment B raw21252step2 raw21252step2Labels := by
      have ha : raw21252step2 = (fun i j => raw21252step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21252step2 raw21252step1; decide +kernel
      have hl : raw21252step2Labels = raw21252step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21252step1 raw21252step1Labels permutation8 permutation3
    mixedMoment B raw21252step2 raw21252step2Labels = mixedMoment B raw21252step3 raw21252step3Labels := by
      have ha : raw21252step3 = raw21252step2 := by apply Matrix.ext; unfold raw21252step3 raw21252step2; decide +kernel
      have hl : raw21252step2Labels = labelEmbedding6 ∘ raw21252step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21252step2 raw21252step2Labels raw21252step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw21253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21253step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21253step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -2, 0], ![3, -1, -2]]
def raw21253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21253step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw21253step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21253step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw21253step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21253 raw21253Labels = mixedMoment B node4111 node4111Labels := by
  calc
    mixedMoment B raw21253 raw21253Labels = mixedMoment B raw21253step0 raw21253step0Labels := by
      have hz : ∀ j, raw21253 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21253step0 = (fun i j => raw21253 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21253step0 raw21253; decide +kernel
      have hl : raw21253step0Labels = raw21253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21253 raw21253Labels permutation434 hz
    mixedMoment B raw21253step0 raw21253step0Labels = mixedMoment B raw21253step1 raw21253step1Labels := by
      have hz : ∀ j, raw21253step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21253step1 = (fun i j => raw21253step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21253step1 raw21253step0; decide +kernel
      have hl : raw21253step1Labels = raw21253step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21253step0 raw21253step0Labels permutation80 hz
    mixedMoment B raw21253step1 raw21253step1Labels = mixedMoment B raw21253step2 raw21253step2Labels := by
      have ha : raw21253step2 = (fun i j => raw21253step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21253step2 raw21253step1; decide +kernel
      have hl : raw21253step2Labels = raw21253step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21253step1 raw21253step1Labels permutation8 permutation3
    mixedMoment B raw21253step2 raw21253step2Labels = mixedMoment B raw21253step3 raw21253step3Labels := by
      have ha : raw21253step3 = raw21253step2 := by apply Matrix.ext; unfold raw21253step3 raw21253step2; decide +kernel
      have hl : raw21253step2Labels = labelEmbedding6 ∘ raw21253step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21253step2 raw21253step2Labels raw21253step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4111 node4111Labels := by rfl

def raw21254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21254step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21254step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -2, 0], ![3, -1, -2]]
def raw21254step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21254step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21254step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21254step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21254step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21254 raw21254Labels = mixedMoment B node4361 node4361Labels := by
  calc
    mixedMoment B raw21254 raw21254Labels = mixedMoment B raw21254step0 raw21254step0Labels := by
      have hz : ∀ j, raw21254 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21254step0 = (fun i j => raw21254 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21254step0 raw21254; decide +kernel
      have hl : raw21254step0Labels = raw21254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21254 raw21254Labels permutation434 hz
    mixedMoment B raw21254step0 raw21254step0Labels = mixedMoment B raw21254step1 raw21254step1Labels := by
      have hz : ∀ j, raw21254step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21254step1 = (fun i j => raw21254step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21254step1 raw21254step0; decide +kernel
      have hl : raw21254step1Labels = raw21254step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21254step0 raw21254step0Labels permutation80 hz
    mixedMoment B raw21254step1 raw21254step1Labels = mixedMoment B raw21254step2 raw21254step2Labels := by
      have ha : raw21254step2 = (fun i j => raw21254step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21254step2 raw21254step1; decide +kernel
      have hl : raw21254step2Labels = raw21254step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21254step1 raw21254step1Labels permutation8 permutation3
    mixedMoment B raw21254step2 raw21254step2Labels = mixedMoment B raw21254step3 raw21254step3Labels := by
      have ha : raw21254step3 = raw21254step2 := by apply Matrix.ext; unfold raw21254step3 raw21254step2; decide +kernel
      have hl : raw21254step2Labels = labelEmbedding6 ∘ raw21254step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21254step2 raw21254step2Labels raw21254step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4361 node4361Labels := by rfl

def raw21255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw21255step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21255step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw21255step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21255 raw21255Labels = mixedMoment B node4296 node4296Labels := by
  calc
    mixedMoment B raw21255 raw21255Labels = mixedMoment B raw21255step0 raw21255step0Labels := by
      have hz : ∀ j, raw21255 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21255step0 = (fun i j => raw21255 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21255step0 raw21255; decide +kernel
      have hl : raw21255step0Labels = raw21255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21255 raw21255Labels permutation434 hz
    mixedMoment B raw21255step0 raw21255step0Labels = mixedMoment B raw21255step1 raw21255step1Labels := by
      have ha : raw21255step1 = (fun i j => raw21255step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21255step1 raw21255step0; decide +kernel
      have hl : raw21255step1Labels = raw21255step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21255step0 raw21255step0Labels permutation38 permutation3
    mixedMoment B raw21255step1 raw21255step1Labels = mixedMoment B raw21255step2 raw21255step2Labels := by
      have ha : raw21255step2 = raw21255step1 := by apply Matrix.ext; unfold raw21255step2 raw21255step1; decide +kernel
      have hl : raw21255step1Labels = labelEmbedding6 ∘ raw21255step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21255step1 raw21255step1Labels raw21255step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4296 node4296Labels := by rfl

def raw21256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21256step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw21256step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw21256step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21256 raw21256Labels = mixedMoment B node4296 node4296Labels := by
  calc
    mixedMoment B raw21256 raw21256Labels = mixedMoment B raw21256step0 raw21256step0Labels := by
      have hz : ∀ j, raw21256 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21256step0 = (fun i j => raw21256 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21256step0 raw21256; decide +kernel
      have hl : raw21256step0Labels = raw21256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21256 raw21256Labels permutation346 hz
    mixedMoment B raw21256step0 raw21256step0Labels = mixedMoment B raw21256step1 raw21256step1Labels := by
      have ha : raw21256step1 = (fun i j => raw21256step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21256step1 raw21256step0; decide +kernel
      have hl : raw21256step1Labels = raw21256step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21256step0 raw21256step0Labels permutation38 permutation3
    mixedMoment B raw21256step1 raw21256step1Labels = mixedMoment B raw21256step2 raw21256step2Labels := by
      have ha : raw21256step2 = raw21256step1 := by apply Matrix.ext; unfold raw21256step2 raw21256step1; decide +kernel
      have hl : raw21256step1Labels = labelEmbedding6 ∘ raw21256step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21256step1 raw21256step1Labels raw21256step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4296 node4296Labels := by rfl

def raw21257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw21257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw21257step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21257step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw21257step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21257step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw21257step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21257step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw21257step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21257 raw21257Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw21257 raw21257Labels = mixedMoment B raw21257step0 raw21257step0Labels := by
      have hz : ∀ j, raw21257 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21257step0 = (fun i j => raw21257 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21257step0 raw21257; decide +kernel
      have hl : raw21257step0Labels = raw21257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21257 raw21257Labels permutation434 hz
    mixedMoment B raw21257step0 raw21257step0Labels = mixedMoment B raw21257step1 raw21257step1Labels := by
      have hz : ∀ j, raw21257step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21257step1 = (fun i j => raw21257step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21257step1 raw21257step0; decide +kernel
      have hl : raw21257step1Labels = raw21257step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21257step0 raw21257step0Labels permutation80 hz
    mixedMoment B raw21257step1 raw21257step1Labels = mixedMoment B raw21257step2 raw21257step2Labels := by
      have ha : raw21257step2 = (fun i j => raw21257step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21257step2 raw21257step1; decide +kernel
      have hl : raw21257step2Labels = raw21257step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21257step1 raw21257step1Labels permutation9 permutation3
    mixedMoment B raw21257step2 raw21257step2Labels = mixedMoment B raw21257step3 raw21257step3Labels := by
      have ha : raw21257step3 = raw21257step2 := by apply Matrix.ext; unfold raw21257step3 raw21257step2; decide +kernel
      have hl : raw21257step2Labels = labelEmbedding6 ∘ raw21257step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21257step2 raw21257step2Labels raw21257step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

def raw21258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21258step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21258step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![4, -2, -2]]
def raw21258step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21258step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw21258step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21258step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw21258step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21258 raw21258Labels = mixedMoment B node4108 node4108Labels := by
  calc
    mixedMoment B raw21258 raw21258Labels = mixedMoment B raw21258step0 raw21258step0Labels := by
      have hz : ∀ j, raw21258 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21258step0 = (fun i j => raw21258 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21258step0 raw21258; decide +kernel
      have hl : raw21258step0Labels = raw21258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21258 raw21258Labels permutation434 hz
    mixedMoment B raw21258step0 raw21258step0Labels = mixedMoment B raw21258step1 raw21258step1Labels := by
      have hz : ∀ j, raw21258step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21258step1 = (fun i j => raw21258step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21258step1 raw21258step0; decide +kernel
      have hl : raw21258step1Labels = raw21258step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21258step0 raw21258step0Labels permutation80 hz
    mixedMoment B raw21258step1 raw21258step1Labels = mixedMoment B raw21258step2 raw21258step2Labels := by
      have ha : raw21258step2 = (fun i j => raw21258step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21258step2 raw21258step1; decide +kernel
      have hl : raw21258step2Labels = raw21258step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21258step1 raw21258step1Labels permutation8 permutation3
    mixedMoment B raw21258step2 raw21258step2Labels = mixedMoment B raw21258step3 raw21258step3Labels := by
      have ha : raw21258step3 = raw21258step2 := by apply Matrix.ext; unfold raw21258step3 raw21258step2; decide +kernel
      have hl : raw21258step2Labels = labelEmbedding6 ∘ raw21258step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21258step2 raw21258step2Labels raw21258step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4108 node4108Labels := by rfl

def raw21259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21259step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![4, -2, -2]]
def raw21259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21259step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21259step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21259step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21259step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21259 raw21259Labels = mixedMoment B node4356 node4356Labels := by
  calc
    mixedMoment B raw21259 raw21259Labels = mixedMoment B raw21259step0 raw21259step0Labels := by
      have hz : ∀ j, raw21259 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21259step0 = (fun i j => raw21259 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21259step0 raw21259; decide +kernel
      have hl : raw21259step0Labels = raw21259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21259 raw21259Labels permutation434 hz
    mixedMoment B raw21259step0 raw21259step0Labels = mixedMoment B raw21259step1 raw21259step1Labels := by
      have hz : ∀ j, raw21259step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21259step1 = (fun i j => raw21259step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21259step1 raw21259step0; decide +kernel
      have hl : raw21259step1Labels = raw21259step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21259step0 raw21259step0Labels permutation80 hz
    mixedMoment B raw21259step1 raw21259step1Labels = mixedMoment B raw21259step2 raw21259step2Labels := by
      have ha : raw21259step2 = (fun i j => raw21259step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21259step2 raw21259step1; decide +kernel
      have hl : raw21259step2Labels = raw21259step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21259step1 raw21259step1Labels permutation8 permutation3
    mixedMoment B raw21259step2 raw21259step2Labels = mixedMoment B raw21259step3 raw21259step3Labels := by
      have ha : raw21259step3 = raw21259step2 := by apply Matrix.ext; unfold raw21259step3 raw21259step2; decide +kernel
      have hl : raw21259step2Labels = labelEmbedding6 ∘ raw21259step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21259step2 raw21259step2Labels raw21259step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4356 node4356Labels := by rfl

def raw21260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw21260step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21260step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw21260step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21260 raw21260Labels = mixedMoment B node4293 node4293Labels := by
  calc
    mixedMoment B raw21260 raw21260Labels = mixedMoment B raw21260step0 raw21260step0Labels := by
      have hz : ∀ j, raw21260 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21260step0 = (fun i j => raw21260 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21260step0 raw21260; decide +kernel
      have hl : raw21260step0Labels = raw21260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21260 raw21260Labels permutation434 hz
    mixedMoment B raw21260step0 raw21260step0Labels = mixedMoment B raw21260step1 raw21260step1Labels := by
      have ha : raw21260step1 = (fun i j => raw21260step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21260step1 raw21260step0; decide +kernel
      have hl : raw21260step1Labels = raw21260step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21260step0 raw21260step0Labels permutation38 permutation3
    mixedMoment B raw21260step1 raw21260step1Labels = mixedMoment B raw21260step2 raw21260step2Labels := by
      have ha : raw21260step2 = raw21260step1 := by apply Matrix.ext; unfold raw21260step2 raw21260step1; decide +kernel
      have hl : raw21260step1Labels = labelEmbedding6 ∘ raw21260step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21260step1 raw21260step1Labels raw21260step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4293 node4293Labels := by rfl

def raw21261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw21261step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21261step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw21261step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21261 raw21261Labels = mixedMoment B node4293 node4293Labels := by
  calc
    mixedMoment B raw21261 raw21261Labels = mixedMoment B raw21261step0 raw21261step0Labels := by
      have hz : ∀ j, raw21261 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21261step0 = (fun i j => raw21261 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21261step0 raw21261; decide +kernel
      have hl : raw21261step0Labels = raw21261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21261 raw21261Labels permutation346 hz
    mixedMoment B raw21261step0 raw21261step0Labels = mixedMoment B raw21261step1 raw21261step1Labels := by
      have ha : raw21261step1 = (fun i j => raw21261step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21261step1 raw21261step0; decide +kernel
      have hl : raw21261step1Labels = raw21261step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21261step0 raw21261step0Labels permutation38 permutation3
    mixedMoment B raw21261step1 raw21261step1Labels = mixedMoment B raw21261step2 raw21261step2Labels := by
      have ha : raw21261step2 = raw21261step1 := by apply Matrix.ext; unfold raw21261step2 raw21261step1; decide +kernel
      have hl : raw21261step1Labels = labelEmbedding6 ∘ raw21261step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21261step1 raw21261step1Labels raw21261step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4293 node4293Labels := by rfl

def raw21262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw21262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw21262step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21262step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![4, -2, -2]]
def raw21262step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21262step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![4, -2, -2]]
def raw21262step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21262step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw21262step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw21262step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw21262step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21262 raw21262Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw21262 raw21262Labels = mixedMoment B raw21262step0 raw21262step0Labels := by
      have hz : ∀ j, raw21262 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21262step0 = (fun i j => raw21262 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21262step0 raw21262; decide +kernel
      have hl : raw21262step0Labels = raw21262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21262 raw21262Labels permutation520 hz
    mixedMoment B raw21262step0 raw21262step0Labels = mixedMoment B raw21262step1 raw21262step1Labels := by
      have hz : ∀ j, raw21262step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21262step1 = (fun i j => raw21262step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21262step1 raw21262step0; decide +kernel
      have hl : raw21262step1Labels = raw21262step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21262step0 raw21262step0Labels permutation104 hz
    mixedMoment B raw21262step1 raw21262step1Labels = mixedMoment B raw21262step2 raw21262step2Labels := by
      have hz : ∀ j, raw21262step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21262step2 = (fun i j => raw21262step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21262step2 raw21262step1; decide +kernel
      have hl : raw21262step2Labels = raw21262step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21262step1 raw21262step1Labels permutation20 hz
    mixedMoment B raw21262step2 raw21262step2Labels = mixedMoment B raw21262step3 raw21262step3Labels := by
      have ha : raw21262step3 = (fun i j => raw21262step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21262step3 raw21262step2; decide +kernel
      have hl : raw21262step3Labels = raw21262step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21262step2 raw21262step2Labels permutation2 permutation3
    mixedMoment B raw21262step3 raw21262step3Labels = mixedMoment B raw21262step4 raw21262step4Labels := by
      have ha : raw21262step4 = raw21262step3 := by apply Matrix.ext; unfold raw21262step4 raw21262step3; decide +kernel
      have hl : raw21262step3Labels = labelEmbedding6 ∘ raw21262step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21262step3 raw21262step3Labels raw21262step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

def raw21263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21263Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21263step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21263step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21263step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw21263step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21263 raw21263Labels = mixedMoment B node2601 node2601Labels := by
  calc
    mixedMoment B raw21263 raw21263Labels = mixedMoment B raw21263step0 raw21263step0Labels := by
      have hz : ∀ j, raw21263 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21263step0 = (fun i j => raw21263 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21263step0 raw21263; decide +kernel
      have hl : raw21263step0Labels = raw21263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21263 raw21263Labels permutation434 hz
    mixedMoment B raw21263step0 raw21263step0Labels = mixedMoment B raw21263step1 raw21263step1Labels := by
      have hz : ∀ j, raw21263step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21263step1 = (fun i j => raw21263step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21263step1 raw21263step0; decide +kernel
      have hl : raw21263step1Labels = raw21263step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21263step0 raw21263step0Labels permutation80 hz
    mixedMoment B raw21263step1 raw21263step1Labels = mixedMoment B raw21263step2 raw21263step2Labels := by
      have ha : raw21263step2 = (fun i j => raw21263step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21263step2 raw21263step1; decide +kernel
      have hl : raw21263step2Labels = raw21263step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21263step1 raw21263step1Labels permutation8 permutation3
    _ = mixedMoment B node2601 node2601Labels := by rfl

def raw21264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21264Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21264step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21264step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21264 raw21264Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw21264 raw21264Labels = mixedMoment B raw21264step0 raw21264step0Labels := by
      have hz : ∀ j, raw21264 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21264step0 = (fun i j => raw21264 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21264step0 raw21264; decide +kernel
      have hl : raw21264step0Labels = raw21264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21264 raw21264Labels permutation434 hz
    mixedMoment B raw21264step0 raw21264step0Labels = mixedMoment B raw21264step1 raw21264step1Labels := by
      have ha : raw21264step1 = (fun i j => raw21264step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21264step1 raw21264step0; decide +kernel
      have hl : raw21264step1Labels = raw21264step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21264step0 raw21264step0Labels permutation38 permutation3
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw21265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21265Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21265step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21265step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21265 raw21265Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw21265 raw21265Labels = mixedMoment B raw21265step0 raw21265step0Labels := by
      have hz : ∀ j, raw21265 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21265step0 = (fun i j => raw21265 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21265step0 raw21265; decide +kernel
      have hl : raw21265step0Labels = raw21265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21265 raw21265Labels permutation346 hz
    mixedMoment B raw21265step0 raw21265step0Labels = mixedMoment B raw21265step1 raw21265step1Labels := by
      have ha : raw21265step1 = (fun i j => raw21265step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21265step1 raw21265step0; decide +kernel
      have hl : raw21265step1Labels = raw21265step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21265step0 raw21265step0Labels permutation38 permutation3
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw21266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21266Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21266step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21266step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw21266step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21266step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![3, -1, -2]]
def raw21266step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21266step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw21266step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21266 raw21266Labels = mixedMoment B node2770 node2770Labels := by
  calc
    mixedMoment B raw21266 raw21266Labels = mixedMoment B raw21266step0 raw21266step0Labels := by
      have hz : ∀ j, raw21266 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21266step0 = (fun i j => raw21266 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21266step0 raw21266; decide +kernel
      have hl : raw21266step0Labels = raw21266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21266 raw21266Labels permutation520 hz
    mixedMoment B raw21266step0 raw21266step0Labels = mixedMoment B raw21266step1 raw21266step1Labels := by
      have hz : ∀ j, raw21266step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21266step1 = (fun i j => raw21266step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21266step1 raw21266step0; decide +kernel
      have hl : raw21266step1Labels = raw21266step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21266step0 raw21266step0Labels permutation104 hz
    mixedMoment B raw21266step1 raw21266step1Labels = mixedMoment B raw21266step2 raw21266step2Labels := by
      have hz : ∀ j, raw21266step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21266step2 = (fun i j => raw21266step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21266step2 raw21266step1; decide +kernel
      have hl : raw21266step2Labels = raw21266step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21266step1 raw21266step1Labels permutation20 hz
    mixedMoment B raw21266step2 raw21266step2Labels = mixedMoment B raw21266step3 raw21266step3Labels := by
      have ha : raw21266step3 = (fun i j => raw21266step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21266step3 raw21266step2; decide +kernel
      have hl : raw21266step3Labels = raw21266step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21266step2 raw21266step2Labels permutation2 permutation3
    _ = mixedMoment B node2770 node2770Labels := by rfl

def raw21267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21267Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21267step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21267step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21267step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21267step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21267step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21267 raw21267Labels = mixedMoment B node559 node559Labels := by
  calc
    mixedMoment B raw21267 raw21267Labels = mixedMoment B raw21267step0 raw21267step0Labels := by
      have hz : ∀ j, raw21267 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21267step0 = (fun i j => raw21267 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21267step0 raw21267; decide +kernel
      have hl : raw21267step0Labels = raw21267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21267 raw21267Labels permutation434 hz
    mixedMoment B raw21267step0 raw21267step0Labels = mixedMoment B raw21267step1 raw21267step1Labels := by
      have hz : ∀ j, raw21267step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21267step1 = (fun i j => raw21267step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21267step1 raw21267step0; decide +kernel
      have hl : raw21267step1Labels = raw21267step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21267step0 raw21267step0Labels permutation80 hz
    mixedMoment B raw21267step1 raw21267step1Labels = mixedMoment B raw21267step2 raw21267step2Labels := by
      have ha : raw21267step2 = (fun i j => raw21267step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21267step2 raw21267step1; decide +kernel
      have hl : raw21267step2Labels = raw21267step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21267step1 raw21267step1Labels permutation10 permutation3
    _ = mixedMoment B node559 node559Labels := by rfl

def raw21268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21268Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21268step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21268step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21268 raw21268Labels = mixedMoment B node887 node887Labels := by
  calc
    mixedMoment B raw21268 raw21268Labels = mixedMoment B raw21268step0 raw21268step0Labels := by
      have hz : ∀ j, raw21268 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21268step0 = (fun i j => raw21268 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21268step0 raw21268; decide +kernel
      have hl : raw21268step0Labels = raw21268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21268 raw21268Labels permutation434 hz
    mixedMoment B raw21268step0 raw21268step0Labels = mixedMoment B raw21268step1 raw21268step1Labels := by
      have ha : raw21268step1 = (fun i j => raw21268step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21268step1 raw21268step0; decide +kernel
      have hl : raw21268step1Labels = raw21268step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21268step0 raw21268step0Labels permutation40 permutation3
    _ = mixedMoment B node887 node887Labels := by rfl

def raw21269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21269Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21269step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21269step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21269step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21269 raw21269Labels = mixedMoment B node887 node887Labels := by
  calc
    mixedMoment B raw21269 raw21269Labels = mixedMoment B raw21269step0 raw21269step0Labels := by
      have hz : ∀ j, raw21269 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21269step0 = (fun i j => raw21269 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21269step0 raw21269; decide +kernel
      have hl : raw21269step0Labels = raw21269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21269 raw21269Labels permutation346 hz
    mixedMoment B raw21269step0 raw21269step0Labels = mixedMoment B raw21269step1 raw21269step1Labels := by
      have ha : raw21269step1 = (fun i j => raw21269step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21269step1 raw21269step0; decide +kernel
      have hl : raw21269step1Labels = raw21269step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21269step0 raw21269step0Labels permutation40 permutation3
    _ = mixedMoment B node887 node887Labels := by rfl

def raw21270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21270Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21270step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21270step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![3, -1, -2]]
def raw21270step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21270step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![3, -1, -2]]
def raw21270step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21270step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw21270step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21270 raw21270Labels = mixedMoment B node1091 node1091Labels := by
  calc
    mixedMoment B raw21270 raw21270Labels = mixedMoment B raw21270step0 raw21270step0Labels := by
      have hz : ∀ j, raw21270 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21270step0 = (fun i j => raw21270 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21270step0 raw21270; decide +kernel
      have hl : raw21270step0Labels = raw21270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21270 raw21270Labels permutation520 hz
    mixedMoment B raw21270step0 raw21270step0Labels = mixedMoment B raw21270step1 raw21270step1Labels := by
      have hz : ∀ j, raw21270step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21270step1 = (fun i j => raw21270step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21270step1 raw21270step0; decide +kernel
      have hl : raw21270step1Labels = raw21270step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21270step0 raw21270step0Labels permutation104 hz
    mixedMoment B raw21270step1 raw21270step1Labels = mixedMoment B raw21270step2 raw21270step2Labels := by
      have hz : ∀ j, raw21270step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21270step2 = (fun i j => raw21270step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21270step2 raw21270step1; decide +kernel
      have hl : raw21270step2Labels = raw21270step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21270step1 raw21270step1Labels permutation20 hz
    mixedMoment B raw21270step2 raw21270step2Labels = mixedMoment B raw21270step3 raw21270step3Labels := by
      have ha : raw21270step3 = (fun i j => raw21270step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21270step3 raw21270step2; decide +kernel
      have hl : raw21270step3Labels = raw21270step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21270step2 raw21270step2Labels permutation2 permutation3
    _ = mixedMoment B node1091 node1091Labels := by rfl

def raw21271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21271Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21271step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21271step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21271step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21271step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw21271step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21271 raw21271Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw21271 raw21271Labels = mixedMoment B raw21271step0 raw21271step0Labels := by
      have hz : ∀ j, raw21271 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21271step0 = (fun i j => raw21271 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21271step0 raw21271; decide +kernel
      have hl : raw21271step0Labels = raw21271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21271 raw21271Labels permutation434 hz
    mixedMoment B raw21271step0 raw21271step0Labels = mixedMoment B raw21271step1 raw21271step1Labels := by
      have hz : ∀ j, raw21271step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21271step1 = (fun i j => raw21271step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21271step1 raw21271step0; decide +kernel
      have hl : raw21271step1Labels = raw21271step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21271step0 raw21271step0Labels permutation80 hz
    mixedMoment B raw21271step1 raw21271step1Labels = mixedMoment B raw21271step2 raw21271step2Labels := by
      have ha : raw21271step2 = (fun i j => raw21271step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21271step2 raw21271step1; decide +kernel
      have hl : raw21271step2Labels = raw21271step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21271step1 raw21271step1Labels permutation10 permutation3
    _ = mixedMoment B node1087 node1087Labels := by rfl

def raw21272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21272Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21272step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21272 raw21272Labels = mixedMoment B node542 node542Labels := by
  calc
    mixedMoment B raw21272 raw21272Labels = mixedMoment B raw21272step0 raw21272step0Labels := by
      have hz : ∀ j, raw21272 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21272step0 = (fun i j => raw21272 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21272step0 raw21272; decide +kernel
      have hl : raw21272step0Labels = raw21272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21272 raw21272Labels permutation434 hz
    mixedMoment B raw21272step0 raw21272step0Labels = mixedMoment B raw21272step1 raw21272step1Labels := by
      have ha : raw21272step1 = (fun i j => raw21272step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21272step1 raw21272step0; decide +kernel
      have hl : raw21272step1Labels = raw21272step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21272step0 raw21272step0Labels permutation32 permutation3
    _ = mixedMoment B node542 node542Labels := by rfl

def raw21273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21273Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21273step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21273step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21273 raw21273Labels = mixedMoment B node930 node930Labels := by
  calc
    mixedMoment B raw21273 raw21273Labels = mixedMoment B raw21273step0 raw21273step0Labels := by
      have hz : ∀ j, raw21273 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21273step0 = (fun i j => raw21273 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21273step0 raw21273; decide +kernel
      have hl : raw21273step0Labels = raw21273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21273 raw21273Labels permutation434 hz
    mixedMoment B raw21273step0 raw21273step0Labels = mixedMoment B raw21273step1 raw21273step1Labels := by
      have ha : raw21273step1 = (fun i j => raw21273step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21273step1 raw21273step0; decide +kernel
      have hl : raw21273step1Labels = raw21273step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21273step0 raw21273step0Labels permutation32 permutation3
    _ = mixedMoment B node930 node930Labels := by rfl

def raw21274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21274Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21274step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21274 raw21274Labels = mixedMoment B node868 node868Labels := by
  calc
    mixedMoment B raw21274 raw21274Labels = mixedMoment B raw21274step0 raw21274step0Labels := by
      have ha : raw21274step0 = (fun i j => raw21274 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21274step0 raw21274; decide +kernel
      have hl : raw21274step0Labels = raw21274Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21274 raw21274Labels permutation200 permutation3
    _ = mixedMoment B node868 node868Labels := by rfl

def raw21275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21275Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21275step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21275step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21275step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21275step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21275step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21275 raw21275Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw21275 raw21275Labels = mixedMoment B raw21275step0 raw21275step0Labels := by
      have hz : ∀ j, raw21275 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21275step0 = (fun i j => raw21275 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21275step0 raw21275; decide +kernel
      have hl : raw21275step0Labels = raw21275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21275 raw21275Labels permutation520 hz
    mixedMoment B raw21275step0 raw21275step0Labels = mixedMoment B raw21275step1 raw21275step1Labels := by
      have hz : ∀ j, raw21275step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21275step1 = (fun i j => raw21275step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21275step1 raw21275step0; decide +kernel
      have hl : raw21275step1Labels = raw21275step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21275step0 raw21275step0Labels permutation104 hz
    mixedMoment B raw21275step1 raw21275step1Labels = mixedMoment B raw21275step2 raw21275step2Labels := by
      have ha : raw21275step2 = (fun i j => raw21275step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21275step2 raw21275step1; decide +kernel
      have hl : raw21275step2Labels = raw21275step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21275step1 raw21275step1Labels permutation8 permutation3
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw21276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21276Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21276step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw21276step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21276 raw21276Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw21276 raw21276Labels = mixedMoment B raw21276step0 raw21276step0Labels := by
      have hz : ∀ j, raw21276 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21276step0 = (fun i j => raw21276 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21276step0 raw21276; decide +kernel
      have hl : raw21276step0Labels = raw21276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21276 raw21276Labels permutation434 hz
    mixedMoment B raw21276step0 raw21276step0Labels = mixedMoment B raw21276step1 raw21276step1Labels := by
      have ha : raw21276step1 = (fun i j => raw21276step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21276step1 raw21276step0; decide +kernel
      have hl : raw21276step1Labels = raw21276step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21276step0 raw21276step0Labels permutation32 permutation3
    _ = mixedMoment B node1044 node1044Labels := by rfl

def raw21277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21277Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21277step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21277step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21277 raw21277Labels = mixedMoment B node542 node542Labels := by
  calc
    mixedMoment B raw21277 raw21277Labels = mixedMoment B raw21277step0 raw21277step0Labels := by
      have hz : ∀ j, raw21277 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21277step0 = (fun i j => raw21277 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21277step0 raw21277; decide +kernel
      have hl : raw21277step0Labels = raw21277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21277 raw21277Labels permutation346 hz
    mixedMoment B raw21277step0 raw21277step0Labels = mixedMoment B raw21277step1 raw21277step1Labels := by
      have ha : raw21277step1 = (fun i j => raw21277step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21277step1 raw21277step0; decide +kernel
      have hl : raw21277step1Labels = raw21277step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21277step0 raw21277step0Labels permutation32 permutation3
    _ = mixedMoment B node542 node542Labels := by rfl

def raw21278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21278Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21278step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21278step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21278 raw21278Labels = mixedMoment B node930 node930Labels := by
  calc
    mixedMoment B raw21278 raw21278Labels = mixedMoment B raw21278step0 raw21278step0Labels := by
      have hz : ∀ j, raw21278 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21278step0 = (fun i j => raw21278 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21278step0 raw21278; decide +kernel
      have hl : raw21278step0Labels = raw21278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21278 raw21278Labels permutation346 hz
    mixedMoment B raw21278step0 raw21278step0Labels = mixedMoment B raw21278step1 raw21278step1Labels := by
      have ha : raw21278step1 = (fun i j => raw21278step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21278step1 raw21278step0; decide +kernel
      have hl : raw21278step1Labels = raw21278step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21278step0 raw21278step0Labels permutation32 permutation3
    _ = mixedMoment B node930 node930Labels := by rfl

def raw21279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21279Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21279step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21279 raw21279Labels = mixedMoment B node868 node868Labels := by
  calc
    mixedMoment B raw21279 raw21279Labels = mixedMoment B raw21279step0 raw21279step0Labels := by
      have ha : raw21279step0 = (fun i j => raw21279 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21279step0 raw21279; decide +kernel
      have hl : raw21279step0Labels = raw21279Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21279 raw21279Labels permutation176 permutation3
    _ = mixedMoment B node868 node868Labels := by rfl

def raw21280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw21280Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21280step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21280step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21280step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21280step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21280step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21280 raw21280Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw21280 raw21280Labels = mixedMoment B raw21280step0 raw21280step0Labels := by
      have hz : ∀ j, raw21280 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21280step0 = (fun i j => raw21280 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21280step0 raw21280; decide +kernel
      have hl : raw21280step0Labels = raw21280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21280 raw21280Labels permutation520 hz
    mixedMoment B raw21280step0 raw21280step0Labels = mixedMoment B raw21280step1 raw21280step1Labels := by
      have hz : ∀ j, raw21280step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21280step1 = (fun i j => raw21280step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21280step1 raw21280step0; decide +kernel
      have hl : raw21280step1Labels = raw21280step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21280step0 raw21280step0Labels permutation80 hz
    mixedMoment B raw21280step1 raw21280step1Labels = mixedMoment B raw21280step2 raw21280step2Labels := by
      have ha : raw21280step2 = (fun i j => raw21280step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21280step2 raw21280step1; decide +kernel
      have hl : raw21280step2Labels = raw21280step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21280step1 raw21280step1Labels permutation8 permutation3
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw21281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21281Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21281step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21281step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -2, 0], ![3, -1, -2]]
def raw21281step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21281step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw21281step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21281 raw21281Labels = mixedMoment B node548 node548Labels := by
  calc
    mixedMoment B raw21281 raw21281Labels = mixedMoment B raw21281step0 raw21281step0Labels := by
      have hz : ∀ j, raw21281 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21281step0 = (fun i j => raw21281 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21281step0 raw21281; decide +kernel
      have hl : raw21281step0Labels = raw21281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21281 raw21281Labels permutation434 hz
    mixedMoment B raw21281step0 raw21281step0Labels = mixedMoment B raw21281step1 raw21281step1Labels := by
      have hz : ∀ j, raw21281step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21281step1 = (fun i j => raw21281step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21281step1 raw21281step0; decide +kernel
      have hl : raw21281step1Labels = raw21281step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21281step0 raw21281step0Labels permutation80 hz
    mixedMoment B raw21281step1 raw21281step1Labels = mixedMoment B raw21281step2 raw21281step2Labels := by
      have ha : raw21281step2 = (fun i j => raw21281step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21281step2 raw21281step1; decide +kernel
      have hl : raw21281step2Labels = raw21281step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21281step1 raw21281step1Labels permutation8 permutation3
    _ = mixedMoment B node548 node548Labels := by rfl

def raw21282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21282Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21282step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -2, 0], ![3, -1, -2]]
def raw21282step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21282step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw21282step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21282 raw21282Labels = mixedMoment B node939 node939Labels := by
  calc
    mixedMoment B raw21282 raw21282Labels = mixedMoment B raw21282step0 raw21282step0Labels := by
      have hz : ∀ j, raw21282 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21282step0 = (fun i j => raw21282 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21282step0 raw21282; decide +kernel
      have hl : raw21282step0Labels = raw21282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21282 raw21282Labels permutation434 hz
    mixedMoment B raw21282step0 raw21282step0Labels = mixedMoment B raw21282step1 raw21282step1Labels := by
      have hz : ∀ j, raw21282step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21282step1 = (fun i j => raw21282step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21282step1 raw21282step0; decide +kernel
      have hl : raw21282step1Labels = raw21282step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21282step0 raw21282step0Labels permutation80 hz
    mixedMoment B raw21282step1 raw21282step1Labels = mixedMoment B raw21282step2 raw21282step2Labels := by
      have ha : raw21282step2 = (fun i j => raw21282step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21282step2 raw21282step1; decide +kernel
      have hl : raw21282step2Labels = raw21282step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21282step1 raw21282step1Labels permutation8 permutation3
    _ = mixedMoment B node939 node939Labels := by rfl

def raw21283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21283Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21283step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw21283step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21283 raw21283Labels = mixedMoment B node874 node874Labels := by
  calc
    mixedMoment B raw21283 raw21283Labels = mixedMoment B raw21283step0 raw21283step0Labels := by
      have hz : ∀ j, raw21283 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21283step0 = (fun i j => raw21283 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21283step0 raw21283; decide +kernel
      have hl : raw21283step0Labels = raw21283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21283 raw21283Labels permutation434 hz
    mixedMoment B raw21283step0 raw21283step0Labels = mixedMoment B raw21283step1 raw21283step1Labels := by
      have ha : raw21283step1 = (fun i j => raw21283step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21283step1 raw21283step0; decide +kernel
      have hl : raw21283step1Labels = raw21283step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21283step0 raw21283step0Labels permutation38 permutation3
    _ = mixedMoment B node874 node874Labels := by rfl

def raw21284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21284Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw21284step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21284step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw21284step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21284 raw21284Labels = mixedMoment B node874 node874Labels := by
  calc
    mixedMoment B raw21284 raw21284Labels = mixedMoment B raw21284step0 raw21284step0Labels := by
      have hz : ∀ j, raw21284 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21284step0 = (fun i j => raw21284 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21284step0 raw21284; decide +kernel
      have hl : raw21284step0Labels = raw21284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21284 raw21284Labels permutation346 hz
    mixedMoment B raw21284step0 raw21284step0Labels = mixedMoment B raw21284step1 raw21284step1Labels := by
      have ha : raw21284step1 = (fun i j => raw21284step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21284step1 raw21284step0; decide +kernel
      have hl : raw21284step1Labels = raw21284step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21284step0 raw21284step0Labels permutation38 permutation3
    _ = mixedMoment B node874 node874Labels := by rfl

def raw21285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw21285Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw21285step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21285step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw21285step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21285step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw21285step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21285 raw21285Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw21285 raw21285Labels = mixedMoment B raw21285step0 raw21285step0Labels := by
      have hz : ∀ j, raw21285 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21285step0 = (fun i j => raw21285 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21285step0 raw21285; decide +kernel
      have hl : raw21285step0Labels = raw21285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21285 raw21285Labels permutation434 hz
    mixedMoment B raw21285step0 raw21285step0Labels = mixedMoment B raw21285step1 raw21285step1Labels := by
      have hz : ∀ j, raw21285step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21285step1 = (fun i j => raw21285step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21285step1 raw21285step0; decide +kernel
      have hl : raw21285step1Labels = raw21285step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21285step0 raw21285step0Labels permutation80 hz
    mixedMoment B raw21285step1 raw21285step1Labels = mixedMoment B raw21285step2 raw21285step2Labels := by
      have ha : raw21285step2 = (fun i j => raw21285step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21285step2 raw21285step1; decide +kernel
      have hl : raw21285step2Labels = raw21285step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21285step1 raw21285step1Labels permutation9 permutation3
    _ = mixedMoment B node1049 node1049Labels := by rfl

def raw21286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21286Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21286step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21286step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![4, -2, -2]]
def raw21286step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21286step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw21286step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21286 raw21286Labels = mixedMoment B node545 node545Labels := by
  calc
    mixedMoment B raw21286 raw21286Labels = mixedMoment B raw21286step0 raw21286step0Labels := by
      have hz : ∀ j, raw21286 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21286step0 = (fun i j => raw21286 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21286step0 raw21286; decide +kernel
      have hl : raw21286step0Labels = raw21286Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21286 raw21286Labels permutation434 hz
    mixedMoment B raw21286step0 raw21286step0Labels = mixedMoment B raw21286step1 raw21286step1Labels := by
      have hz : ∀ j, raw21286step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21286step1 = (fun i j => raw21286step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21286step1 raw21286step0; decide +kernel
      have hl : raw21286step1Labels = raw21286step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21286step0 raw21286step0Labels permutation80 hz
    mixedMoment B raw21286step1 raw21286step1Labels = mixedMoment B raw21286step2 raw21286step2Labels := by
      have ha : raw21286step2 = (fun i j => raw21286step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21286step2 raw21286step1; decide +kernel
      have hl : raw21286step2Labels = raw21286step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21286step1 raw21286step1Labels permutation8 permutation3
    _ = mixedMoment B node545 node545Labels := by rfl

def raw21287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21287Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21287step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21287step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![4, -2, -2]]
def raw21287step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21287step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw21287step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21287 raw21287Labels = mixedMoment B node934 node934Labels := by
  calc
    mixedMoment B raw21287 raw21287Labels = mixedMoment B raw21287step0 raw21287step0Labels := by
      have hz : ∀ j, raw21287 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21287step0 = (fun i j => raw21287 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21287step0 raw21287; decide +kernel
      have hl : raw21287step0Labels = raw21287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21287 raw21287Labels permutation434 hz
    mixedMoment B raw21287step0 raw21287step0Labels = mixedMoment B raw21287step1 raw21287step1Labels := by
      have hz : ∀ j, raw21287step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21287step1 = (fun i j => raw21287step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21287step1 raw21287step0; decide +kernel
      have hl : raw21287step1Labels = raw21287step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21287step0 raw21287step0Labels permutation80 hz
    mixedMoment B raw21287step1 raw21287step1Labels = mixedMoment B raw21287step2 raw21287step2Labels := by
      have ha : raw21287step2 = (fun i j => raw21287step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21287step2 raw21287step1; decide +kernel
      have hl : raw21287step2Labels = raw21287step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21287step1 raw21287step1Labels permutation8 permutation3
    _ = mixedMoment B node934 node934Labels := by rfl

def raw21288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21288Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21288step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw21288step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21288 raw21288Labels = mixedMoment B node871 node871Labels := by
  calc
    mixedMoment B raw21288 raw21288Labels = mixedMoment B raw21288step0 raw21288step0Labels := by
      have hz : ∀ j, raw21288 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21288step0 = (fun i j => raw21288 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21288step0 raw21288; decide +kernel
      have hl : raw21288step0Labels = raw21288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21288 raw21288Labels permutation434 hz
    mixedMoment B raw21288step0 raw21288step0Labels = mixedMoment B raw21288step1 raw21288step1Labels := by
      have ha : raw21288step1 = (fun i j => raw21288step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21288step1 raw21288step0; decide +kernel
      have hl : raw21288step1Labels = raw21288step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21288step0 raw21288step0Labels permutation38 permutation3
    _ = mixedMoment B node871 node871Labels := by rfl

def raw21289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21289Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw21289step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw21289step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21289 raw21289Labels = mixedMoment B node871 node871Labels := by
  calc
    mixedMoment B raw21289 raw21289Labels = mixedMoment B raw21289step0 raw21289step0Labels := by
      have hz : ∀ j, raw21289 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21289step0 = (fun i j => raw21289 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21289step0 raw21289; decide +kernel
      have hl : raw21289step0Labels = raw21289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21289 raw21289Labels permutation346 hz
    mixedMoment B raw21289step0 raw21289step0Labels = mixedMoment B raw21289step1 raw21289step1Labels := by
      have ha : raw21289step1 = (fun i j => raw21289step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21289step1 raw21289step0; decide +kernel
      have hl : raw21289step1Labels = raw21289step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21289step0 raw21289step0Labels permutation38 permutation3
    _ = mixedMoment B node871 node871Labels := by rfl

def raw21290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw21290Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw21290step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21290step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![4, -2, -2]]
def raw21290step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21290step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![4, -2, -2]]
def raw21290step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21290step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw21290step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21290 raw21290Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw21290 raw21290Labels = mixedMoment B raw21290step0 raw21290step0Labels := by
      have hz : ∀ j, raw21290 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21290step0 = (fun i j => raw21290 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21290step0 raw21290; decide +kernel
      have hl : raw21290step0Labels = raw21290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21290 raw21290Labels permutation520 hz
    mixedMoment B raw21290step0 raw21290step0Labels = mixedMoment B raw21290step1 raw21290step1Labels := by
      have hz : ∀ j, raw21290step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw21290step1 = (fun i j => raw21290step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw21290step1 raw21290step0; decide +kernel
      have hl : raw21290step1Labels = raw21290step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21290step0 raw21290step0Labels permutation104 hz
    mixedMoment B raw21290step1 raw21290step1Labels = mixedMoment B raw21290step2 raw21290step2Labels := by
      have hz : ∀ j, raw21290step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw21290step2 = (fun i j => raw21290step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw21290step2 raw21290step1; decide +kernel
      have hl : raw21290step2Labels = raw21290step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21290step1 raw21290step1Labels permutation20 hz
    mixedMoment B raw21290step2 raw21290step2Labels = mixedMoment B raw21290step3 raw21290step3Labels := by
      have ha : raw21290step3 = (fun i j => raw21290step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw21290step3 raw21290step2; decide +kernel
      have hl : raw21290step3Labels = raw21290step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21290step2 raw21290step2Labels permutation2 permutation3
    _ = mixedMoment B node1051 node1051Labels := by rfl

def raw21291 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21291step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw21291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21291step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21291 raw21291Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw21291 raw21291Labels = mixedMoment B raw21291step0 raw21291step0Labels := by
      have hz : ∀ j, raw21291 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21291step0 = (fun i j => raw21291 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21291step0 raw21291; decide +kernel
      have hl : raw21291step0Labels = raw21291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21291 raw21291Labels permutation434 hz
    mixedMoment B raw21291step0 raw21291step0Labels = mixedMoment B raw21291step1 raw21291step1Labels := by
      have ha : raw21291step1 = (fun i j => raw21291step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21291step1 raw21291step0; decide +kernel
      have hl : raw21291step1Labels = raw21291step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21291step0 raw21291step0Labels permutation32 permutation7
    mixedMoment B raw21291step1 raw21291step1Labels = mixedMoment B raw21291step2 raw21291step2Labels := by
      have ha : raw21291step2 = raw21291step1 := by apply Matrix.ext; unfold raw21291step2 raw21291step1; decide +kernel
      have hl : raw21291step1Labels = labelEmbedding10 ∘ raw21291step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21291step1 raw21291step1Labels raw21291step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw21292 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21292step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21292step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21292step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21292step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw21292step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21292step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21292 raw21292Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw21292 raw21292Labels = mixedMoment B raw21292step0 raw21292step0Labels := by
      have hz : ∀ j, raw21292 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21292step0 = (fun i j => raw21292 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21292step0 raw21292; decide +kernel
      have hl : raw21292step0Labels = raw21292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21292 raw21292Labels permutation434 hz
    mixedMoment B raw21292step0 raw21292step0Labels = mixedMoment B raw21292step1 raw21292step1Labels := by
      have hz : ∀ j, raw21292step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21292step1 = (fun i j => raw21292step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21292step1 raw21292step0; decide +kernel
      have hl : raw21292step1Labels = raw21292step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21292step0 raw21292step0Labels permutation80 hz
    mixedMoment B raw21292step1 raw21292step1Labels = mixedMoment B raw21292step2 raw21292step2Labels := by
      have ha : raw21292step2 = (fun i j => raw21292step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21292step2 raw21292step1; decide +kernel
      have hl : raw21292step2Labels = raw21292step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21292step1 raw21292step1Labels permutation8 permutation7
    mixedMoment B raw21292step2 raw21292step2Labels = mixedMoment B raw21292step3 raw21292step3Labels := by
      have ha : raw21292step3 = raw21292step2 := by apply Matrix.ext; unfold raw21292step3 raw21292step2; decide +kernel
      have hl : raw21292step2Labels = labelEmbedding10 ∘ raw21292step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21292step2 raw21292step2Labels raw21292step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4605 node4605Labels := by rfl

def raw21293 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21293step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21293step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21293step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw21293step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21293step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw21293step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21293 raw21293Labels = mixedMoment B node4276 node4276Labels := by
  calc
    mixedMoment B raw21293 raw21293Labels = mixedMoment B raw21293step0 raw21293step0Labels := by
      have hz : ∀ j, raw21293 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21293step0 = (fun i j => raw21293 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21293step0 raw21293; decide +kernel
      have hl : raw21293step0Labels = raw21293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21293 raw21293Labels permutation434 hz
    mixedMoment B raw21293step0 raw21293step0Labels = mixedMoment B raw21293step1 raw21293step1Labels := by
      have hz : ∀ j, raw21293step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21293step1 = (fun i j => raw21293step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21293step1 raw21293step0; decide +kernel
      have hl : raw21293step1Labels = raw21293step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21293step0 raw21293step0Labels permutation80 hz
    mixedMoment B raw21293step1 raw21293step1Labels = mixedMoment B raw21293step2 raw21293step2Labels := by
      have ha : raw21293step2 = (fun i j => raw21293step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21293step2 raw21293step1; decide +kernel
      have hl : raw21293step2Labels = raw21293step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21293step1 raw21293step1Labels permutation8 permutation6
    mixedMoment B raw21293step2 raw21293step2Labels = mixedMoment B raw21293step3 raw21293step3Labels := by
      have ha : raw21293step3 = raw21293step2 := by apply Matrix.ext; unfold raw21293step3 raw21293step2; decide +kernel
      have hl : raw21293step2Labels = labelEmbedding9 ∘ raw21293step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21293step2 raw21293step2Labels raw21293step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4276 node4276Labels := by rfl

def raw21294 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw21294step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw21294step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21294 raw21294Labels = mixedMoment B node4410 node4410Labels := by
  calc
    mixedMoment B raw21294 raw21294Labels = mixedMoment B raw21294step0 raw21294step0Labels := by
      have hz : ∀ j, raw21294 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21294step0 = (fun i j => raw21294 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21294step0 raw21294; decide +kernel
      have hl : raw21294step0Labels = raw21294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21294 raw21294Labels permutation434 hz
    mixedMoment B raw21294step0 raw21294step0Labels = mixedMoment B raw21294step1 raw21294step1Labels := by
      have ha : raw21294step1 = (fun i j => raw21294step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21294step1 raw21294step0; decide +kernel
      have hl : raw21294step1Labels = raw21294step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21294step0 raw21294step0Labels permutation38 permutation6
    mixedMoment B raw21294step1 raw21294step1Labels = mixedMoment B raw21294step2 raw21294step2Labels := by
      have ha : raw21294step2 = raw21294step1 := by apply Matrix.ext; unfold raw21294step2 raw21294step1; decide +kernel
      have hl : raw21294step1Labels = labelEmbedding9 ∘ raw21294step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21294step1 raw21294step1Labels raw21294step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4410 node4410Labels := by rfl

def raw21295 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21295step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw21295step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21295step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw21295step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21295 raw21295Labels = mixedMoment B node4410 node4410Labels := by
  calc
    mixedMoment B raw21295 raw21295Labels = mixedMoment B raw21295step0 raw21295step0Labels := by
      have hz : ∀ j, raw21295 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21295step0 = (fun i j => raw21295 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21295step0 raw21295; decide +kernel
      have hl : raw21295step0Labels = raw21295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21295 raw21295Labels permutation346 hz
    mixedMoment B raw21295step0 raw21295step0Labels = mixedMoment B raw21295step1 raw21295step1Labels := by
      have ha : raw21295step1 = (fun i j => raw21295step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21295step1 raw21295step0; decide +kernel
      have hl : raw21295step1Labels = raw21295step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21295step0 raw21295step0Labels permutation38 permutation6
    mixedMoment B raw21295step1 raw21295step1Labels = mixedMoment B raw21295step2 raw21295step2Labels := by
      have ha : raw21295step2 = raw21295step1 := by apply Matrix.ext; unfold raw21295step2 raw21295step1; decide +kernel
      have hl : raw21295step1Labels = labelEmbedding9 ∘ raw21295step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21295step1 raw21295step1Labels raw21295step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4410 node4410Labels := by rfl

def raw21296 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21296step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21296step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21296step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21296step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw21296step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21296step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw21296step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21296 raw21296Labels = mixedMoment B node4476 node4476Labels := by
  calc
    mixedMoment B raw21296 raw21296Labels = mixedMoment B raw21296step0 raw21296step0Labels := by
      have hz : ∀ j, raw21296 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21296step0 = (fun i j => raw21296 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21296step0 raw21296; decide +kernel
      have hl : raw21296step0Labels = raw21296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21296 raw21296Labels permutation434 hz
    mixedMoment B raw21296step0 raw21296step0Labels = mixedMoment B raw21296step1 raw21296step1Labels := by
      have hz : ∀ j, raw21296step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21296step1 = (fun i j => raw21296step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21296step1 raw21296step0; decide +kernel
      have hl : raw21296step1Labels = raw21296step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21296step0 raw21296step0Labels permutation80 hz
    mixedMoment B raw21296step1 raw21296step1Labels = mixedMoment B raw21296step2 raw21296step2Labels := by
      have ha : raw21296step2 = (fun i j => raw21296step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21296step2 raw21296step1; decide +kernel
      have hl : raw21296step2Labels = raw21296step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21296step1 raw21296step1Labels permutation8 permutation6
    mixedMoment B raw21296step2 raw21296step2Labels = mixedMoment B raw21296step3 raw21296step3Labels := by
      have ha : raw21296step3 = raw21296step2 := by apply Matrix.ext; unfold raw21296step3 raw21296step2; decide +kernel
      have hl : raw21296step2Labels = labelEmbedding9 ∘ raw21296step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21296step2 raw21296step2Labels raw21296step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4476 node4476Labels := by rfl

def raw21297 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21297step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw21297step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21297step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw21297step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21297 raw21297Labels = mixedMoment B node4478 node4478Labels := by
  calc
    mixedMoment B raw21297 raw21297Labels = mixedMoment B raw21297step0 raw21297step0Labels := by
      have hz : ∀ j, raw21297 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21297step0 = (fun i j => raw21297 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21297step0 raw21297; decide +kernel
      have hl : raw21297step0Labels = raw21297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21297 raw21297Labels permutation434 hz
    mixedMoment B raw21297step0 raw21297step0Labels = mixedMoment B raw21297step1 raw21297step1Labels := by
      have hz : ∀ j, raw21297step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21297step1 = (fun i j => raw21297step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21297step1 raw21297step0; decide +kernel
      have hl : raw21297step1Labels = raw21297step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21297step0 raw21297step0Labels permutation80 hz
    mixedMoment B raw21297step1 raw21297step1Labels = mixedMoment B raw21297step2 raw21297step2Labels := by
      have ha : raw21297step2 = (fun i j => raw21297step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21297step2 raw21297step1; decide +kernel
      have hl : raw21297step2Labels = raw21297step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21297step1 raw21297step1Labels permutation8 permutation6
    mixedMoment B raw21297step2 raw21297step2Labels = mixedMoment B raw21297step3 raw21297step3Labels := by
      have ha : raw21297step3 = raw21297step2 := by apply Matrix.ext; unfold raw21297step3 raw21297step2; decide +kernel
      have hl : raw21297step2Labels = labelEmbedding9 ∘ raw21297step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21297step2 raw21297step2Labels raw21297step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4478 node4478Labels := by rfl

def raw21298 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21298step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21298step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21298step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21298step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21298 raw21298Labels = mixedMoment B node4253 node4253Labels := by
  calc
    mixedMoment B raw21298 raw21298Labels = mixedMoment B raw21298step0 raw21298step0Labels := by
      have hz : ∀ j, raw21298 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21298step0 = (fun i j => raw21298 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21298step0 raw21298; decide +kernel
      have hl : raw21298step0Labels = raw21298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21298 raw21298Labels permutation434 hz
    mixedMoment B raw21298step0 raw21298step0Labels = mixedMoment B raw21298step1 raw21298step1Labels := by
      have ha : raw21298step1 = (fun i j => raw21298step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21298step1 raw21298step0; decide +kernel
      have hl : raw21298step1Labels = raw21298step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21298step0 raw21298step0Labels permutation32 permutation6
    mixedMoment B raw21298step1 raw21298step1Labels = mixedMoment B raw21298step2 raw21298step2Labels := by
      have ha : raw21298step2 = raw21298step1 := by apply Matrix.ext; unfold raw21298step2 raw21298step1; decide +kernel
      have hl : raw21298step1Labels = labelEmbedding9 ∘ raw21298step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21298step1 raw21298step1Labels raw21298step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4253 node4253Labels := by rfl

def raw21299 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21299step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21299step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21299step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21299step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21299step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21299step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21299 raw21299Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw21299 raw21299Labels = mixedMoment B raw21299step0 raw21299step0Labels := by
      have hz : ∀ j, raw21299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21299step0 = (fun i j => raw21299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21299step0 raw21299; decide +kernel
      have hl : raw21299step0Labels = raw21299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21299 raw21299Labels permutation434 hz
    mixedMoment B raw21299step0 raw21299step0Labels = mixedMoment B raw21299step1 raw21299step1Labels := by
      have hz : ∀ j, raw21299step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21299step1 = (fun i j => raw21299step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21299step1 raw21299step0; decide +kernel
      have hl : raw21299step1Labels = raw21299step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21299step0 raw21299step0Labels permutation56 hz
    mixedMoment B raw21299step1 raw21299step1Labels = mixedMoment B raw21299step2 raw21299step2Labels := by
      have ha : raw21299step2 = (fun i j => raw21299step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21299step2 raw21299step1; decide +kernel
      have hl : raw21299step2Labels = raw21299step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21299step1 raw21299step1Labels permutation8 permutation6
    mixedMoment B raw21299step2 raw21299step2Labels = mixedMoment B raw21299step3 raw21299step3Labels := by
      have ha : raw21299step3 = raw21299step2 := by apply Matrix.ext; unfold raw21299step3 raw21299step2; decide +kernel
      have hl : raw21299step2Labels = labelEmbedding9 ∘ raw21299step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21299step2 raw21299step2Labels raw21299step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw21300 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21300step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21300step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21300step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21300 raw21300Labels = mixedMoment B node4391 node4391Labels := by
  calc
    mixedMoment B raw21300 raw21300Labels = mixedMoment B raw21300step0 raw21300step0Labels := by
      have ha : raw21300step0 = (fun i j => raw21300 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21300step0 raw21300; decide +kernel
      have hl : raw21300step0Labels = raw21300Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21300 raw21300Labels permutation200 permutation6
    mixedMoment B raw21300step0 raw21300step0Labels = mixedMoment B raw21300step1 raw21300step1Labels := by
      have ha : raw21300step1 = raw21300step0 := by apply Matrix.ext; unfold raw21300step1 raw21300step0; decide +kernel
      have hl : raw21300step0Labels = labelEmbedding9 ∘ raw21300step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21300step0 raw21300step0Labels raw21300step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4391 node4391Labels := by rfl

def raw21301 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21301step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21301step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21301step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21301step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21301 raw21301Labels = mixedMoment B node4440 node4440Labels := by
  calc
    mixedMoment B raw21301 raw21301Labels = mixedMoment B raw21301step0 raw21301step0Labels := by
      have hz : ∀ j, raw21301 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21301step0 = (fun i j => raw21301 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21301step0 raw21301; decide +kernel
      have hl : raw21301step0Labels = raw21301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21301 raw21301Labels permutation434 hz
    mixedMoment B raw21301step0 raw21301step0Labels = mixedMoment B raw21301step1 raw21301step1Labels := by
      have ha : raw21301step1 = (fun i j => raw21301step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21301step1 raw21301step0; decide +kernel
      have hl : raw21301step1Labels = raw21301step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21301step0 raw21301step0Labels permutation32 permutation6
    mixedMoment B raw21301step1 raw21301step1Labels = mixedMoment B raw21301step2 raw21301step2Labels := by
      have ha : raw21301step2 = raw21301step1 := by apply Matrix.ext; unfold raw21301step2 raw21301step1; decide +kernel
      have hl : raw21301step1Labels = labelEmbedding9 ∘ raw21301step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21301step1 raw21301step1Labels raw21301step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4440 node4440Labels := by rfl

def raw21302 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21302step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21302step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21302step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21302step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21302 raw21302Labels = mixedMoment B node4442 node4442Labels := by
  calc
    mixedMoment B raw21302 raw21302Labels = mixedMoment B raw21302step0 raw21302step0Labels := by
      have hz : ∀ j, raw21302 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21302step0 = (fun i j => raw21302 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21302step0 raw21302; decide +kernel
      have hl : raw21302step0Labels = raw21302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21302 raw21302Labels permutation434 hz
    mixedMoment B raw21302step0 raw21302step0Labels = mixedMoment B raw21302step1 raw21302step1Labels := by
      have ha : raw21302step1 = (fun i j => raw21302step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21302step1 raw21302step0; decide +kernel
      have hl : raw21302step1Labels = raw21302step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21302step0 raw21302step0Labels permutation32 permutation6
    mixedMoment B raw21302step1 raw21302step1Labels = mixedMoment B raw21302step2 raw21302step2Labels := by
      have ha : raw21302step2 = raw21302step1 := by apply Matrix.ext; unfold raw21302step2 raw21302step1; decide +kernel
      have hl : raw21302step1Labels = labelEmbedding9 ∘ raw21302step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21302step1 raw21302step1Labels raw21302step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4442 node4442Labels := by rfl

def raw21303 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21303step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21303step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21303step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21303step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21303step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21303 raw21303Labels = mixedMoment B node4253 node4253Labels := by
  calc
    mixedMoment B raw21303 raw21303Labels = mixedMoment B raw21303step0 raw21303step0Labels := by
      have hz : ∀ j, raw21303 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21303step0 = (fun i j => raw21303 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21303step0 raw21303; decide +kernel
      have hl : raw21303step0Labels = raw21303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21303 raw21303Labels permutation346 hz
    mixedMoment B raw21303step0 raw21303step0Labels = mixedMoment B raw21303step1 raw21303step1Labels := by
      have ha : raw21303step1 = (fun i j => raw21303step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21303step1 raw21303step0; decide +kernel
      have hl : raw21303step1Labels = raw21303step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21303step0 raw21303step0Labels permutation32 permutation6
    mixedMoment B raw21303step1 raw21303step1Labels = mixedMoment B raw21303step2 raw21303step2Labels := by
      have ha : raw21303step2 = raw21303step1 := by apply Matrix.ext; unfold raw21303step2 raw21303step1; decide +kernel
      have hl : raw21303step1Labels = labelEmbedding9 ∘ raw21303step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21303step1 raw21303step1Labels raw21303step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4253 node4253Labels := by rfl

def raw21304 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21304step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21304step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21304step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21304step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21304step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21304step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21304 raw21304Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw21304 raw21304Labels = mixedMoment B raw21304step0 raw21304step0Labels := by
      have hz : ∀ j, raw21304 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21304step0 = (fun i j => raw21304 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21304step0 raw21304; decide +kernel
      have hl : raw21304step0Labels = raw21304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21304 raw21304Labels permutation346 hz
    mixedMoment B raw21304step0 raw21304step0Labels = mixedMoment B raw21304step1 raw21304step1Labels := by
      have hz : ∀ j, raw21304step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21304step1 = (fun i j => raw21304step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21304step1 raw21304step0; decide +kernel
      have hl : raw21304step1Labels = raw21304step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21304step0 raw21304step0Labels permutation56 hz
    mixedMoment B raw21304step1 raw21304step1Labels = mixedMoment B raw21304step2 raw21304step2Labels := by
      have ha : raw21304step2 = (fun i j => raw21304step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21304step2 raw21304step1; decide +kernel
      have hl : raw21304step2Labels = raw21304step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21304step1 raw21304step1Labels permutation8 permutation6
    mixedMoment B raw21304step2 raw21304step2Labels = mixedMoment B raw21304step3 raw21304step3Labels := by
      have ha : raw21304step3 = raw21304step2 := by apply Matrix.ext; unfold raw21304step3 raw21304step2; decide +kernel
      have hl : raw21304step2Labels = labelEmbedding9 ∘ raw21304step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21304step2 raw21304step2Labels raw21304step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw21305 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21305step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21305step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21305step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21305 raw21305Labels = mixedMoment B node4391 node4391Labels := by
  calc
    mixedMoment B raw21305 raw21305Labels = mixedMoment B raw21305step0 raw21305step0Labels := by
      have ha : raw21305step0 = (fun i j => raw21305 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21305step0 raw21305; decide +kernel
      have hl : raw21305step0Labels = raw21305Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21305 raw21305Labels permutation176 permutation6
    mixedMoment B raw21305step0 raw21305step0Labels = mixedMoment B raw21305step1 raw21305step1Labels := by
      have ha : raw21305step1 = raw21305step0 := by apply Matrix.ext; unfold raw21305step1 raw21305step0; decide +kernel
      have hl : raw21305step0Labels = labelEmbedding9 ∘ raw21305step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21305step0 raw21305step0Labels raw21305step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4391 node4391Labels := by rfl

def raw21306 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21306step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21306step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21306step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21306step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21306 raw21306Labels = mixedMoment B node4440 node4440Labels := by
  calc
    mixedMoment B raw21306 raw21306Labels = mixedMoment B raw21306step0 raw21306step0Labels := by
      have hz : ∀ j, raw21306 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21306step0 = (fun i j => raw21306 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21306step0 raw21306; decide +kernel
      have hl : raw21306step0Labels = raw21306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21306 raw21306Labels permutation346 hz
    mixedMoment B raw21306step0 raw21306step0Labels = mixedMoment B raw21306step1 raw21306step1Labels := by
      have ha : raw21306step1 = (fun i j => raw21306step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21306step1 raw21306step0; decide +kernel
      have hl : raw21306step1Labels = raw21306step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21306step0 raw21306step0Labels permutation32 permutation6
    mixedMoment B raw21306step1 raw21306step1Labels = mixedMoment B raw21306step2 raw21306step2Labels := by
      have ha : raw21306step2 = raw21306step1 := by apply Matrix.ext; unfold raw21306step2 raw21306step1; decide +kernel
      have hl : raw21306step1Labels = labelEmbedding9 ∘ raw21306step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21306step1 raw21306step1Labels raw21306step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4440 node4440Labels := by rfl

def raw21307 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21307step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21307step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21307step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21307step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21307 raw21307Labels = mixedMoment B node4442 node4442Labels := by
  calc
    mixedMoment B raw21307 raw21307Labels = mixedMoment B raw21307step0 raw21307step0Labels := by
      have hz : ∀ j, raw21307 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21307step0 = (fun i j => raw21307 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21307step0 raw21307; decide +kernel
      have hl : raw21307step0Labels = raw21307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21307 raw21307Labels permutation346 hz
    mixedMoment B raw21307step0 raw21307step0Labels = mixedMoment B raw21307step1 raw21307step1Labels := by
      have ha : raw21307step1 = (fun i j => raw21307step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21307step1 raw21307step0; decide +kernel
      have hl : raw21307step1Labels = raw21307step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21307step0 raw21307step0Labels permutation32 permutation6
    mixedMoment B raw21307step1 raw21307step1Labels = mixedMoment B raw21307step2 raw21307step2Labels := by
      have ha : raw21307step2 = raw21307step1 := by apply Matrix.ext; unfold raw21307step2 raw21307step1; decide +kernel
      have hl : raw21307step1Labels = labelEmbedding9 ∘ raw21307step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21307step1 raw21307step1Labels raw21307step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4442 node4442Labels := by rfl

def raw21308 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21308step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21308step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21308step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21308step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21308step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21308step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21308step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21308 raw21308Labels = mixedMoment B node4270 node4270Labels := by
  calc
    mixedMoment B raw21308 raw21308Labels = mixedMoment B raw21308step0 raw21308step0Labels := by
      have hz : ∀ j, raw21308 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21308step0 = (fun i j => raw21308 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21308step0 raw21308; decide +kernel
      have hl : raw21308step0Labels = raw21308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21308 raw21308Labels permutation434 hz
    mixedMoment B raw21308step0 raw21308step0Labels = mixedMoment B raw21308step1 raw21308step1Labels := by
      have hz : ∀ j, raw21308step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21308step1 = (fun i j => raw21308step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21308step1 raw21308step0; decide +kernel
      have hl : raw21308step1Labels = raw21308step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21308step0 raw21308step0Labels permutation80 hz
    mixedMoment B raw21308step1 raw21308step1Labels = mixedMoment B raw21308step2 raw21308step2Labels := by
      have ha : raw21308step2 = (fun i j => raw21308step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21308step2 raw21308step1; decide +kernel
      have hl : raw21308step2Labels = raw21308step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21308step1 raw21308step1Labels permutation8 permutation6
    mixedMoment B raw21308step2 raw21308step2Labels = mixedMoment B raw21308step3 raw21308step3Labels := by
      have ha : raw21308step3 = raw21308step2 := by apply Matrix.ext; unfold raw21308step3 raw21308step2; decide +kernel
      have hl : raw21308step2Labels = labelEmbedding9 ∘ raw21308step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21308step2 raw21308step2Labels raw21308step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4270 node4270Labels := by rfl

def raw21309 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21309step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21309step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21309step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21309step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-2, -1, 3]]
def raw21309step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21309step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw21309step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21309step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw21309step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21309 raw21309Labels = mixedMoment B node4507 node4507Labels := by
  calc
    mixedMoment B raw21309 raw21309Labels = mixedMoment B raw21309step0 raw21309step0Labels := by
      have hz : ∀ j, raw21309 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21309step0 = (fun i j => raw21309 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21309step0 raw21309; decide +kernel
      have hl : raw21309step0Labels = raw21309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21309 raw21309Labels permutation434 hz
    mixedMoment B raw21309step0 raw21309step0Labels = mixedMoment B raw21309step1 raw21309step1Labels := by
      have hz : ∀ j, raw21309step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21309step1 = (fun i j => raw21309step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21309step1 raw21309step0; decide +kernel
      have hl : raw21309step1Labels = raw21309step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21309step0 raw21309step0Labels permutation80 hz
    mixedMoment B raw21309step1 raw21309step1Labels = mixedMoment B raw21309step2 raw21309step2Labels := by
      have hz : ∀ j, raw21309step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21309step2 = (fun i j => raw21309step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21309step2 raw21309step1; decide +kernel
      have hl : raw21309step2Labels = raw21309step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21309step1 raw21309step1Labels permutation14 hz
    mixedMoment B raw21309step2 raw21309step2Labels = mixedMoment B raw21309step3 raw21309step3Labels := by
      have ha : raw21309step3 = (fun i j => raw21309step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21309step3 raw21309step2; decide +kernel
      have hl : raw21309step3Labels = raw21309step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21309step2 raw21309step2Labels permutation2 permutation6
    mixedMoment B raw21309step3 raw21309step3Labels = mixedMoment B raw21309step4 raw21309step4Labels := by
      have ha : raw21309step4 = raw21309step3 := by apply Matrix.ext; unfold raw21309step4 raw21309step3; decide +kernel
      have hl : raw21309step3Labels = labelEmbedding9 ∘ raw21309step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21309step3 raw21309step3Labels raw21309step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4507 node4507Labels := by rfl

def raw21310 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21310step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21310step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21310step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21310step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21310 raw21310Labels = mixedMoment B node4402 node4402Labels := by
  calc
    mixedMoment B raw21310 raw21310Labels = mixedMoment B raw21310step0 raw21310step0Labels := by
      have hz : ∀ j, raw21310 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21310step0 = (fun i j => raw21310 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21310step0 raw21310; decide +kernel
      have hl : raw21310step0Labels = raw21310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21310 raw21310Labels permutation434 hz
    mixedMoment B raw21310step0 raw21310step0Labels = mixedMoment B raw21310step1 raw21310step1Labels := by
      have ha : raw21310step1 = (fun i j => raw21310step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21310step1 raw21310step0; decide +kernel
      have hl : raw21310step1Labels = raw21310step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21310step0 raw21310step0Labels permutation38 permutation6
    mixedMoment B raw21310step1 raw21310step1Labels = mixedMoment B raw21310step2 raw21310step2Labels := by
      have ha : raw21310step2 = raw21310step1 := by apply Matrix.ext; unfold raw21310step2 raw21310step1; decide +kernel
      have hl : raw21310step1Labels = labelEmbedding9 ∘ raw21310step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21310step1 raw21310step1Labels raw21310step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4402 node4402Labels := by rfl

def raw21311 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21311step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21311step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21311step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21311step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21311 raw21311Labels = mixedMoment B node4402 node4402Labels := by
  calc
    mixedMoment B raw21311 raw21311Labels = mixedMoment B raw21311step0 raw21311step0Labels := by
      have hz : ∀ j, raw21311 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21311step0 = (fun i j => raw21311 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21311step0 raw21311; decide +kernel
      have hl : raw21311step0Labels = raw21311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21311 raw21311Labels permutation346 hz
    mixedMoment B raw21311step0 raw21311step0Labels = mixedMoment B raw21311step1 raw21311step1Labels := by
      have ha : raw21311step1 = (fun i j => raw21311step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21311step1 raw21311step0; decide +kernel
      have hl : raw21311step1Labels = raw21311step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21311step0 raw21311step0Labels permutation38 permutation6
    mixedMoment B raw21311step1 raw21311step1Labels = mixedMoment B raw21311step2 raw21311step2Labels := by
      have ha : raw21311step2 = raw21311step1 := by apply Matrix.ext; unfold raw21311step2 raw21311step1; decide +kernel
      have hl : raw21311step1Labels = labelEmbedding9 ∘ raw21311step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21311step1 raw21311step1Labels raw21311step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4402 node4402Labels := by rfl

def raw21312 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21312step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21312step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21312step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21312step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw21312step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21312step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw21312step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21312 raw21312Labels = mixedMoment B node4464 node4464Labels := by
  calc
    mixedMoment B raw21312 raw21312Labels = mixedMoment B raw21312step0 raw21312step0Labels := by
      have hz : ∀ j, raw21312 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21312step0 = (fun i j => raw21312 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21312step0 raw21312; decide +kernel
      have hl : raw21312step0Labels = raw21312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21312 raw21312Labels permutation434 hz
    mixedMoment B raw21312step0 raw21312step0Labels = mixedMoment B raw21312step1 raw21312step1Labels := by
      have hz : ∀ j, raw21312step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21312step1 = (fun i j => raw21312step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21312step1 raw21312step0; decide +kernel
      have hl : raw21312step1Labels = raw21312step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21312step0 raw21312step0Labels permutation80 hz
    mixedMoment B raw21312step1 raw21312step1Labels = mixedMoment B raw21312step2 raw21312step2Labels := by
      have ha : raw21312step2 = (fun i j => raw21312step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21312step2 raw21312step1; decide +kernel
      have hl : raw21312step2Labels = raw21312step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21312step1 raw21312step1Labels permutation8 permutation6
    mixedMoment B raw21312step2 raw21312step2Labels = mixedMoment B raw21312step3 raw21312step3Labels := by
      have ha : raw21312step3 = raw21312step2 := by apply Matrix.ext; unfold raw21312step3 raw21312step2; decide +kernel
      have hl : raw21312step2Labels = labelEmbedding9 ∘ raw21312step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21312step2 raw21312step2Labels raw21312step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4464 node4464Labels := by rfl

def raw21313 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21313step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21313step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21313step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21313step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21313step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21313step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21313step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21313 raw21313Labels = mixedMoment B node4269 node4269Labels := by
  calc
    mixedMoment B raw21313 raw21313Labels = mixedMoment B raw21313step0 raw21313step0Labels := by
      have hz : ∀ j, raw21313 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21313step0 = (fun i j => raw21313 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21313step0 raw21313; decide +kernel
      have hl : raw21313step0Labels = raw21313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21313 raw21313Labels permutation434 hz
    mixedMoment B raw21313step0 raw21313step0Labels = mixedMoment B raw21313step1 raw21313step1Labels := by
      have hz : ∀ j, raw21313step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21313step1 = (fun i j => raw21313step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21313step1 raw21313step0; decide +kernel
      have hl : raw21313step1Labels = raw21313step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21313step0 raw21313step0Labels permutation80 hz
    mixedMoment B raw21313step1 raw21313step1Labels = mixedMoment B raw21313step2 raw21313step2Labels := by
      have ha : raw21313step2 = (fun i j => raw21313step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21313step2 raw21313step1; decide +kernel
      have hl : raw21313step2Labels = raw21313step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21313step1 raw21313step1Labels permutation8 permutation6
    mixedMoment B raw21313step2 raw21313step2Labels = mixedMoment B raw21313step3 raw21313step3Labels := by
      have ha : raw21313step3 = raw21313step2 := by apply Matrix.ext; unfold raw21313step3 raw21313step2; decide +kernel
      have hl : raw21313step2Labels = labelEmbedding9 ∘ raw21313step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21313step2 raw21313step2Labels raw21313step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4269 node4269Labels := by rfl

def raw21314 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21314step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21314step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21314step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21314 raw21314Labels = mixedMoment B node4401 node4401Labels := by
  calc
    mixedMoment B raw21314 raw21314Labels = mixedMoment B raw21314step0 raw21314step0Labels := by
      have hz : ∀ j, raw21314 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21314step0 = (fun i j => raw21314 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21314step0 raw21314; decide +kernel
      have hl : raw21314step0Labels = raw21314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21314 raw21314Labels permutation434 hz
    mixedMoment B raw21314step0 raw21314step0Labels = mixedMoment B raw21314step1 raw21314step1Labels := by
      have ha : raw21314step1 = (fun i j => raw21314step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21314step1 raw21314step0; decide +kernel
      have hl : raw21314step1Labels = raw21314step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21314step0 raw21314step0Labels permutation38 permutation6
    mixedMoment B raw21314step1 raw21314step1Labels = mixedMoment B raw21314step2 raw21314step2Labels := by
      have ha : raw21314step2 = raw21314step1 := by apply Matrix.ext; unfold raw21314step2 raw21314step1; decide +kernel
      have hl : raw21314step1Labels = labelEmbedding9 ∘ raw21314step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21314step1 raw21314step1Labels raw21314step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4401 node4401Labels := by rfl

def raw21315 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21315Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21315step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21315 raw21315Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw21315 raw21315Labels = mixedMoment B raw21315step0 raw21315step0Labels := by
      have hz : ∀ j, raw21315 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21315step0 = (fun i j => raw21315 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21315step0 raw21315; decide +kernel
      have hl : raw21315step0Labels = raw21315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21315 raw21315Labels permutation434 hz
    mixedMoment B raw21315step0 raw21315step0Labels = mixedMoment B raw21315step1 raw21315step1Labels := by
      have ha : raw21315step1 = (fun i j => raw21315step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21315step1 raw21315step0; decide +kernel
      have hl : raw21315step1Labels = raw21315step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21315step0 raw21315step0Labels permutation38 permutation6
    _ = mixedMoment B node1217 node1217Labels := by rfl

def raw21316 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21316Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21316step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21316step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21316step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21316step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21316step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21316 raw21316Labels = mixedMoment B node1269 node1269Labels := by
  calc
    mixedMoment B raw21316 raw21316Labels = mixedMoment B raw21316step0 raw21316step0Labels := by
      have hz : ∀ j, raw21316 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21316step0 = (fun i j => raw21316 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21316step0 raw21316; decide +kernel
      have hl : raw21316step0Labels = raw21316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21316 raw21316Labels permutation434 hz
    mixedMoment B raw21316step0 raw21316step0Labels = mixedMoment B raw21316step1 raw21316step1Labels := by
      have hz : ∀ j, raw21316step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21316step1 = (fun i j => raw21316step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21316step1 raw21316step0; decide +kernel
      have hl : raw21316step1Labels = raw21316step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21316step0 raw21316step0Labels permutation80 hz
    mixedMoment B raw21316step1 raw21316step1Labels = mixedMoment B raw21316step2 raw21316step2Labels := by
      have ha : raw21316step2 = (fun i j => raw21316step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21316step2 raw21316step1; decide +kernel
      have hl : raw21316step2Labels = raw21316step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21316step1 raw21316step1Labels permutation8 permutation6
    _ = mixedMoment B node1269 node1269Labels := by rfl

def raw21317 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21317Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21317step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21317step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21317step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21317step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21317step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21317 raw21317Labels = mixedMoment B node1271 node1271Labels := by
  calc
    mixedMoment B raw21317 raw21317Labels = mixedMoment B raw21317step0 raw21317step0Labels := by
      have hz : ∀ j, raw21317 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21317step0 = (fun i j => raw21317 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21317step0 raw21317; decide +kernel
      have hl : raw21317step0Labels = raw21317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21317 raw21317Labels permutation434 hz
    mixedMoment B raw21317step0 raw21317step0Labels = mixedMoment B raw21317step1 raw21317step1Labels := by
      have hz : ∀ j, raw21317step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21317step1 = (fun i j => raw21317step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21317step1 raw21317step0; decide +kernel
      have hl : raw21317step1Labels = raw21317step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21317step0 raw21317step0Labels permutation80 hz
    mixedMoment B raw21317step1 raw21317step1Labels = mixedMoment B raw21317step2 raw21317step2Labels := by
      have ha : raw21317step2 = (fun i j => raw21317step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21317step2 raw21317step1; decide +kernel
      have hl : raw21317step2Labels = raw21317step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21317step1 raw21317step1Labels permutation8 permutation6
    _ = mixedMoment B node1271 node1271Labels := by rfl

def raw21318 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21318Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21318step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21318step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21318step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21318step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw21318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21318 raw21318Labels = mixedMoment B node828 node828Labels := by
  calc
    mixedMoment B raw21318 raw21318Labels = mixedMoment B raw21318step0 raw21318step0Labels := by
      have hz : ∀ j, raw21318 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21318step0 = (fun i j => raw21318 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21318step0 raw21318; decide +kernel
      have hl : raw21318step0Labels = raw21318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21318 raw21318Labels permutation434 hz
    mixedMoment B raw21318step0 raw21318step0Labels = mixedMoment B raw21318step1 raw21318step1Labels := by
      have hz : ∀ j, raw21318step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21318step1 = (fun i j => raw21318step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21318step1 raw21318step0; decide +kernel
      have hl : raw21318step1Labels = raw21318step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21318step0 raw21318step0Labels permutation80 hz
    mixedMoment B raw21318step1 raw21318step1Labels = mixedMoment B raw21318step2 raw21318step2Labels := by
      have ha : raw21318step2 = (fun i j => raw21318step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21318step2 raw21318step1; decide +kernel
      have hl : raw21318step2Labels = raw21318step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21318step1 raw21318step1Labels permutation8 permutation6
    _ = mixedMoment B node828 node828Labels := by rfl

def raw21319 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21319Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21319step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw21319step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21319 raw21319Labels = mixedMoment B node991 node991Labels := by
  calc
    mixedMoment B raw21319 raw21319Labels = mixedMoment B raw21319step0 raw21319step0Labels := by
      have hz : ∀ j, raw21319 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21319step0 = (fun i j => raw21319 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21319step0 raw21319; decide +kernel
      have hl : raw21319step0Labels = raw21319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21319 raw21319Labels permutation434 hz
    mixedMoment B raw21319step0 raw21319step0Labels = mixedMoment B raw21319step1 raw21319step1Labels := by
      have ha : raw21319step1 = (fun i j => raw21319step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21319step1 raw21319step0; decide +kernel
      have hl : raw21319step1Labels = raw21319step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21319step0 raw21319step0Labels permutation38 permutation6
    _ = mixedMoment B node991 node991Labels := by rfl

def raw21320 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21320Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21320step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw21320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21320 raw21320Labels = mixedMoment B node991 node991Labels := by
  calc
    mixedMoment B raw21320 raw21320Labels = mixedMoment B raw21320step0 raw21320step0Labels := by
      have hz : ∀ j, raw21320 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21320step0 = (fun i j => raw21320 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21320step0 raw21320; decide +kernel
      have hl : raw21320step0Labels = raw21320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21320 raw21320Labels permutation346 hz
    mixedMoment B raw21320step0 raw21320step0Labels = mixedMoment B raw21320step1 raw21320step1Labels := by
      have ha : raw21320step1 = (fun i j => raw21320step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21320step1 raw21320step0; decide +kernel
      have hl : raw21320step1Labels = raw21320step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21320step0 raw21320step0Labels permutation38 permutation6
    _ = mixedMoment B node991 node991Labels := by rfl

def raw21321 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21321Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21321step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21321step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21321step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21321step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw21321step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21321 raw21321Labels = mixedMoment B node1059 node1059Labels := by
  calc
    mixedMoment B raw21321 raw21321Labels = mixedMoment B raw21321step0 raw21321step0Labels := by
      have hz : ∀ j, raw21321 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21321step0 = (fun i j => raw21321 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21321step0 raw21321; decide +kernel
      have hl : raw21321step0Labels = raw21321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21321 raw21321Labels permutation434 hz
    mixedMoment B raw21321step0 raw21321step0Labels = mixedMoment B raw21321step1 raw21321step1Labels := by
      have hz : ∀ j, raw21321step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21321step1 = (fun i j => raw21321step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21321step1 raw21321step0; decide +kernel
      have hl : raw21321step1Labels = raw21321step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21321step0 raw21321step0Labels permutation80 hz
    mixedMoment B raw21321step1 raw21321step1Labels = mixedMoment B raw21321step2 raw21321step2Labels := by
      have ha : raw21321step2 = (fun i j => raw21321step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21321step2 raw21321step1; decide +kernel
      have hl : raw21321step2Labels = raw21321step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21321step1 raw21321step1Labels permutation8 permutation6
    _ = mixedMoment B node1059 node1059Labels := by rfl

def raw21322 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21322Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21322step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21322step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21322step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw21322step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21322 raw21322Labels = mixedMoment B node1061 node1061Labels := by
  calc
    mixedMoment B raw21322 raw21322Labels = mixedMoment B raw21322step0 raw21322step0Labels := by
      have hz : ∀ j, raw21322 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21322step0 = (fun i j => raw21322 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21322step0 raw21322; decide +kernel
      have hl : raw21322step0Labels = raw21322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21322 raw21322Labels permutation434 hz
    mixedMoment B raw21322step0 raw21322step0Labels = mixedMoment B raw21322step1 raw21322step1Labels := by
      have hz : ∀ j, raw21322step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21322step1 = (fun i j => raw21322step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21322step1 raw21322step0; decide +kernel
      have hl : raw21322step1Labels = raw21322step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21322step0 raw21322step0Labels permutation80 hz
    mixedMoment B raw21322step1 raw21322step1Labels = mixedMoment B raw21322step2 raw21322step2Labels := by
      have ha : raw21322step2 = (fun i j => raw21322step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21322step2 raw21322step1; decide +kernel
      have hl : raw21322step2Labels = raw21322step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21322step1 raw21322step1Labels permutation8 permutation6
    _ = mixedMoment B node1061 node1061Labels := by rfl

def raw21323 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21323Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21323step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21323step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21323step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21323 raw21323Labels = mixedMoment B node787 node787Labels := by
  calc
    mixedMoment B raw21323 raw21323Labels = mixedMoment B raw21323step0 raw21323step0Labels := by
      have hz : ∀ j, raw21323 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21323step0 = (fun i j => raw21323 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21323step0 raw21323; decide +kernel
      have hl : raw21323step0Labels = raw21323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21323 raw21323Labels permutation434 hz
    mixedMoment B raw21323step0 raw21323step0Labels = mixedMoment B raw21323step1 raw21323step1Labels := by
      have ha : raw21323step1 = (fun i j => raw21323step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21323step1 raw21323step0; decide +kernel
      have hl : raw21323step1Labels = raw21323step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21323step0 raw21323step0Labels permutation32 permutation6
    _ = mixedMoment B node787 node787Labels := by rfl

def raw21324 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21324Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21324step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21324step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21324step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21324step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21324step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21324 raw21324Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw21324 raw21324Labels = mixedMoment B raw21324step0 raw21324step0Labels := by
      have hz : ∀ j, raw21324 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21324step0 = (fun i j => raw21324 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21324step0 raw21324; decide +kernel
      have hl : raw21324step0Labels = raw21324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21324 raw21324Labels permutation434 hz
    mixedMoment B raw21324step0 raw21324step0Labels = mixedMoment B raw21324step1 raw21324step1Labels := by
      have hz : ∀ j, raw21324step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21324step1 = (fun i j => raw21324step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21324step1 raw21324step0; decide +kernel
      have hl : raw21324step1Labels = raw21324step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21324step0 raw21324step0Labels permutation56 hz
    mixedMoment B raw21324step1 raw21324step1Labels = mixedMoment B raw21324step2 raw21324step2Labels := by
      have ha : raw21324step2 = (fun i j => raw21324step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21324step2 raw21324step1; decide +kernel
      have hl : raw21324step2Labels = raw21324step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21324step1 raw21324step1Labels permutation8 permutation6
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw21325 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21325Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21325step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21325 raw21325Labels = mixedMoment B node972 node972Labels := by
  calc
    mixedMoment B raw21325 raw21325Labels = mixedMoment B raw21325step0 raw21325step0Labels := by
      have ha : raw21325step0 = (fun i j => raw21325 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21325step0 raw21325; decide +kernel
      have hl : raw21325step0Labels = raw21325Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21325 raw21325Labels permutation200 permutation6
    _ = mixedMoment B node972 node972Labels := by rfl

def raw21326 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21326Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21326step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21326step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21326 raw21326Labels = mixedMoment B node1022 node1022Labels := by
  calc
    mixedMoment B raw21326 raw21326Labels = mixedMoment B raw21326step0 raw21326step0Labels := by
      have hz : ∀ j, raw21326 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21326step0 = (fun i j => raw21326 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21326step0 raw21326; decide +kernel
      have hl : raw21326step0Labels = raw21326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21326 raw21326Labels permutation434 hz
    mixedMoment B raw21326step0 raw21326step0Labels = mixedMoment B raw21326step1 raw21326step1Labels := by
      have ha : raw21326step1 = (fun i j => raw21326step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21326step1 raw21326step0; decide +kernel
      have hl : raw21326step1Labels = raw21326step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21326step0 raw21326step0Labels permutation32 permutation6
    _ = mixedMoment B node1022 node1022Labels := by rfl

def raw21327 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21327Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21327step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21327step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21327 raw21327Labels = mixedMoment B node1024 node1024Labels := by
  calc
    mixedMoment B raw21327 raw21327Labels = mixedMoment B raw21327step0 raw21327step0Labels := by
      have hz : ∀ j, raw21327 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21327step0 = (fun i j => raw21327 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21327step0 raw21327; decide +kernel
      have hl : raw21327step0Labels = raw21327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21327 raw21327Labels permutation434 hz
    mixedMoment B raw21327step0 raw21327step0Labels = mixedMoment B raw21327step1 raw21327step1Labels := by
      have ha : raw21327step1 = (fun i j => raw21327step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21327step1 raw21327step0; decide +kernel
      have hl : raw21327step1Labels = raw21327step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21327step0 raw21327step0Labels permutation32 permutation6
    _ = mixedMoment B node1024 node1024Labels := by rfl

def raw21328 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21328Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21328step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21328 raw21328Labels = mixedMoment B node787 node787Labels := by
  calc
    mixedMoment B raw21328 raw21328Labels = mixedMoment B raw21328step0 raw21328step0Labels := by
      have hz : ∀ j, raw21328 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21328step0 = (fun i j => raw21328 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21328step0 raw21328; decide +kernel
      have hl : raw21328step0Labels = raw21328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21328 raw21328Labels permutation346 hz
    mixedMoment B raw21328step0 raw21328step0Labels = mixedMoment B raw21328step1 raw21328step1Labels := by
      have ha : raw21328step1 = (fun i j => raw21328step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21328step1 raw21328step0; decide +kernel
      have hl : raw21328step1Labels = raw21328step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21328step0 raw21328step0Labels permutation32 permutation6
    _ = mixedMoment B node787 node787Labels := by rfl

def raw21329 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21329Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21329step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21329step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21329step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21329 raw21329Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw21329 raw21329Labels = mixedMoment B raw21329step0 raw21329step0Labels := by
      have hz : ∀ j, raw21329 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21329step0 = (fun i j => raw21329 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21329step0 raw21329; decide +kernel
      have hl : raw21329step0Labels = raw21329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21329 raw21329Labels permutation346 hz
    mixedMoment B raw21329step0 raw21329step0Labels = mixedMoment B raw21329step1 raw21329step1Labels := by
      have hz : ∀ j, raw21329step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21329step1 = (fun i j => raw21329step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21329step1 raw21329step0; decide +kernel
      have hl : raw21329step1Labels = raw21329step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21329step0 raw21329step0Labels permutation56 hz
    mixedMoment B raw21329step1 raw21329step1Labels = mixedMoment B raw21329step2 raw21329step2Labels := by
      have ha : raw21329step2 = (fun i j => raw21329step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21329step2 raw21329step1; decide +kernel
      have hl : raw21329step2Labels = raw21329step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21329step1 raw21329step1Labels permutation8 permutation6
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw21330 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21330Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21330step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw21330step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21330 raw21330Labels = mixedMoment B node972 node972Labels := by
  calc
    mixedMoment B raw21330 raw21330Labels = mixedMoment B raw21330step0 raw21330step0Labels := by
      have ha : raw21330step0 = (fun i j => raw21330 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21330step0 raw21330; decide +kernel
      have hl : raw21330step0Labels = raw21330Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21330 raw21330Labels permutation176 permutation6
    _ = mixedMoment B node972 node972Labels := by rfl

def raw21331 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21331Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21331step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21331 raw21331Labels = mixedMoment B node1022 node1022Labels := by
  calc
    mixedMoment B raw21331 raw21331Labels = mixedMoment B raw21331step0 raw21331step0Labels := by
      have hz : ∀ j, raw21331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21331step0 = (fun i j => raw21331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21331step0 raw21331; decide +kernel
      have hl : raw21331step0Labels = raw21331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21331 raw21331Labels permutation346 hz
    mixedMoment B raw21331step0 raw21331step0Labels = mixedMoment B raw21331step1 raw21331step1Labels := by
      have ha : raw21331step1 = (fun i j => raw21331step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21331step1 raw21331step0; decide +kernel
      have hl : raw21331step1Labels = raw21331step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21331step0 raw21331step0Labels permutation32 permutation6
    _ = mixedMoment B node1022 node1022Labels := by rfl

def raw21332 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21332Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21332step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21332step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw21332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21332 raw21332Labels = mixedMoment B node1024 node1024Labels := by
  calc
    mixedMoment B raw21332 raw21332Labels = mixedMoment B raw21332step0 raw21332step0Labels := by
      have hz : ∀ j, raw21332 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21332step0 = (fun i j => raw21332 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21332step0 raw21332; decide +kernel
      have hl : raw21332step0Labels = raw21332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21332 raw21332Labels permutation346 hz
    mixedMoment B raw21332step0 raw21332step0Labels = mixedMoment B raw21332step1 raw21332step1Labels := by
      have ha : raw21332step1 = (fun i j => raw21332step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21332step1 raw21332step0; decide +kernel
      have hl : raw21332step1Labels = raw21332step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21332step0 raw21332step0Labels permutation32 permutation6
    _ = mixedMoment B node1024 node1024Labels := by rfl

def raw21333 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21333Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21333step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21333step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21333step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21333step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21333 raw21333Labels = mixedMoment B node813 node813Labels := by
  calc
    mixedMoment B raw21333 raw21333Labels = mixedMoment B raw21333step0 raw21333step0Labels := by
      have hz : ∀ j, raw21333 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21333step0 = (fun i j => raw21333 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21333step0 raw21333; decide +kernel
      have hl : raw21333step0Labels = raw21333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21333 raw21333Labels permutation434 hz
    mixedMoment B raw21333step0 raw21333step0Labels = mixedMoment B raw21333step1 raw21333step1Labels := by
      have hz : ∀ j, raw21333step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21333step1 = (fun i j => raw21333step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21333step1 raw21333step0; decide +kernel
      have hl : raw21333step1Labels = raw21333step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21333step0 raw21333step0Labels permutation80 hz
    mixedMoment B raw21333step1 raw21333step1Labels = mixedMoment B raw21333step2 raw21333step2Labels := by
      have ha : raw21333step2 = (fun i j => raw21333step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21333step2 raw21333step1; decide +kernel
      have hl : raw21333step2Labels = raw21333step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21333step1 raw21333step1Labels permutation8 permutation6
    _ = mixedMoment B node813 node813Labels := by rfl

def raw21334 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21334Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21334step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21334step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21334step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-2, -1, 3]]
def raw21334step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21334step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw21334step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21334 raw21334Labels = mixedMoment B node1091 node1091Labels := by
  calc
    mixedMoment B raw21334 raw21334Labels = mixedMoment B raw21334step0 raw21334step0Labels := by
      have hz : ∀ j, raw21334 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21334step0 = (fun i j => raw21334 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21334step0 raw21334; decide +kernel
      have hl : raw21334step0Labels = raw21334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21334 raw21334Labels permutation434 hz
    mixedMoment B raw21334step0 raw21334step0Labels = mixedMoment B raw21334step1 raw21334step1Labels := by
      have hz : ∀ j, raw21334step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21334step1 = (fun i j => raw21334step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21334step1 raw21334step0; decide +kernel
      have hl : raw21334step1Labels = raw21334step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21334step0 raw21334step0Labels permutation80 hz
    mixedMoment B raw21334step1 raw21334step1Labels = mixedMoment B raw21334step2 raw21334step2Labels := by
      have hz : ∀ j, raw21334step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21334step2 = (fun i j => raw21334step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21334step2 raw21334step1; decide +kernel
      have hl : raw21334step2Labels = raw21334step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21334step1 raw21334step1Labels permutation14 hz
    mixedMoment B raw21334step2 raw21334step2Labels = mixedMoment B raw21334step3 raw21334step3Labels := by
      have ha : raw21334step3 = (fun i j => raw21334step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21334step3 raw21334step2; decide +kernel
      have hl : raw21334step3Labels = raw21334step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21334step2 raw21334step2Labels permutation2 permutation6
    _ = mixedMoment B node1091 node1091Labels := by rfl

def raw21335 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21335Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21335step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21335step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21335 raw21335Labels = mixedMoment B node983 node983Labels := by
  calc
    mixedMoment B raw21335 raw21335Labels = mixedMoment B raw21335step0 raw21335step0Labels := by
      have hz : ∀ j, raw21335 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21335step0 = (fun i j => raw21335 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21335step0 raw21335; decide +kernel
      have hl : raw21335step0Labels = raw21335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21335 raw21335Labels permutation434 hz
    mixedMoment B raw21335step0 raw21335step0Labels = mixedMoment B raw21335step1 raw21335step1Labels := by
      have ha : raw21335step1 = (fun i j => raw21335step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21335step1 raw21335step0; decide +kernel
      have hl : raw21335step1Labels = raw21335step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21335step0 raw21335step0Labels permutation38 permutation6
    _ = mixedMoment B node983 node983Labels := by rfl

def raw21336 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21336Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21336step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw21336step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21336 raw21336Labels = mixedMoment B node983 node983Labels := by
  calc
    mixedMoment B raw21336 raw21336Labels = mixedMoment B raw21336step0 raw21336step0Labels := by
      have hz : ∀ j, raw21336 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21336step0 = (fun i j => raw21336 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21336step0 raw21336; decide +kernel
      have hl : raw21336step0Labels = raw21336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21336 raw21336Labels permutation346 hz
    mixedMoment B raw21336step0 raw21336step0Labels = mixedMoment B raw21336step1 raw21336step1Labels := by
      have ha : raw21336step1 = (fun i j => raw21336step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21336step1 raw21336step0; decide +kernel
      have hl : raw21336step1Labels = raw21336step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21336step0 raw21336step0Labels permutation38 permutation6
    _ = mixedMoment B node983 node983Labels := by rfl

def raw21337 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21337Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21337step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21337step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21337step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw21337step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21337 raw21337Labels = mixedMoment B node1047 node1047Labels := by
  calc
    mixedMoment B raw21337 raw21337Labels = mixedMoment B raw21337step0 raw21337step0Labels := by
      have hz : ∀ j, raw21337 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21337step0 = (fun i j => raw21337 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21337step0 raw21337; decide +kernel
      have hl : raw21337step0Labels = raw21337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21337 raw21337Labels permutation434 hz
    mixedMoment B raw21337step0 raw21337step0Labels = mixedMoment B raw21337step1 raw21337step1Labels := by
      have hz : ∀ j, raw21337step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21337step1 = (fun i j => raw21337step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21337step1 raw21337step0; decide +kernel
      have hl : raw21337step1Labels = raw21337step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21337step0 raw21337step0Labels permutation80 hz
    mixedMoment B raw21337step1 raw21337step1Labels = mixedMoment B raw21337step2 raw21337step2Labels := by
      have ha : raw21337step2 = (fun i j => raw21337step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21337step2 raw21337step1; decide +kernel
      have hl : raw21337step2Labels = raw21337step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21337step1 raw21337step1Labels permutation8 permutation6
    _ = mixedMoment B node1047 node1047Labels := by rfl

def raw21338 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21338Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21338step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21338step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21338step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21338step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21338step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21338 raw21338Labels = mixedMoment B node812 node812Labels := by
  calc
    mixedMoment B raw21338 raw21338Labels = mixedMoment B raw21338step0 raw21338step0Labels := by
      have hz : ∀ j, raw21338 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21338step0 = (fun i j => raw21338 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21338step0 raw21338; decide +kernel
      have hl : raw21338step0Labels = raw21338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21338 raw21338Labels permutation434 hz
    mixedMoment B raw21338step0 raw21338step0Labels = mixedMoment B raw21338step1 raw21338step1Labels := by
      have hz : ∀ j, raw21338step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21338step1 = (fun i j => raw21338step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21338step1 raw21338step0; decide +kernel
      have hl : raw21338step1Labels = raw21338step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21338step0 raw21338step0Labels permutation80 hz
    mixedMoment B raw21338step1 raw21338step1Labels = mixedMoment B raw21338step2 raw21338step2Labels := by
      have ha : raw21338step2 = (fun i j => raw21338step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21338step2 raw21338step1; decide +kernel
      have hl : raw21338step2Labels = raw21338step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21338step1 raw21338step1Labels permutation8 permutation6
    _ = mixedMoment B node812 node812Labels := by rfl

def raw21339 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21339Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21339step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21339step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21339 raw21339Labels = mixedMoment B node982 node982Labels := by
  calc
    mixedMoment B raw21339 raw21339Labels = mixedMoment B raw21339step0 raw21339step0Labels := by
      have hz : ∀ j, raw21339 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21339step0 = (fun i j => raw21339 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21339step0 raw21339; decide +kernel
      have hl : raw21339step0Labels = raw21339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21339 raw21339Labels permutation434 hz
    mixedMoment B raw21339step0 raw21339step0Labels = mixedMoment B raw21339step1 raw21339step1Labels := by
      have ha : raw21339step1 = (fun i j => raw21339step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21339step1 raw21339step0; decide +kernel
      have hl : raw21339step1Labels = raw21339step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21339step0 raw21339step0Labels permutation38 permutation6
    _ = mixedMoment B node982 node982Labels := by rfl

def raw21340 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21340Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21340step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21340step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21340step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw21340step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21340step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21340 raw21340Labels = mixedMoment B node1043 node1043Labels := by
  calc
    mixedMoment B raw21340 raw21340Labels = mixedMoment B raw21340step0 raw21340step0Labels := by
      have hz : ∀ j, raw21340 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21340step0 = (fun i j => raw21340 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21340step0 raw21340; decide +kernel
      have hl : raw21340step0Labels = raw21340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21340 raw21340Labels permutation434 hz
    mixedMoment B raw21340step0 raw21340step0Labels = mixedMoment B raw21340step1 raw21340step1Labels := by
      have hz : ∀ j, raw21340step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21340step1 = (fun i j => raw21340step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21340step1 raw21340step0; decide +kernel
      have hl : raw21340step1Labels = raw21340step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21340step0 raw21340step0Labels permutation80 hz
    mixedMoment B raw21340step1 raw21340step1Labels = mixedMoment B raw21340step2 raw21340step2Labels := by
      have ha : raw21340step2 = (fun i j => raw21340step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21340step2 raw21340step1; decide +kernel
      have hl : raw21340step2Labels = raw21340step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21340step1 raw21340step1Labels permutation8 permutation6
    _ = mixedMoment B node1043 node1043Labels := by rfl

def raw21341 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21341Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21341step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21341step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21341step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21341step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21341 raw21341Labels = mixedMoment B node1215 node1215Labels := by
  calc
    mixedMoment B raw21341 raw21341Labels = mixedMoment B raw21341step0 raw21341step0Labels := by
      have hz : ∀ j, raw21341 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21341step0 = (fun i j => raw21341 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21341step0 raw21341; decide +kernel
      have hl : raw21341step0Labels = raw21341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21341 raw21341Labels permutation434 hz
    mixedMoment B raw21341step0 raw21341step0Labels = mixedMoment B raw21341step1 raw21341step1Labels := by
      have ha : raw21341step1 = (fun i j => raw21341step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21341step1 raw21341step0; decide +kernel
      have hl : raw21341step1Labels = raw21341step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21341step0 raw21341step0Labels permutation32 permutation7
    mixedMoment B raw21341step1 raw21341step1Labels = mixedMoment B raw21341step2 raw21341step2Labels := by
      have ha : raw21341step2 = raw21341step1 := by apply Matrix.ext; unfold raw21341step2 raw21341step1; decide +kernel
      have hl : raw21341step1Labels = labelEmbedding1 ∘ raw21341step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21341step1 raw21341step1Labels raw21341step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1215 node1215Labels := by rfl

def raw21342 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21342Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21342step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21342step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21342step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21342step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21342 raw21342Labels = mixedMoment B node1215 node1215Labels := by
  calc
    mixedMoment B raw21342 raw21342Labels = mixedMoment B raw21342step0 raw21342step0Labels := by
      have hz : ∀ j, raw21342 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21342step0 = (fun i j => raw21342 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21342step0 raw21342; decide +kernel
      have hl : raw21342step0Labels = raw21342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21342 raw21342Labels permutation346 hz
    mixedMoment B raw21342step0 raw21342step0Labels = mixedMoment B raw21342step1 raw21342step1Labels := by
      have ha : raw21342step1 = (fun i j => raw21342step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21342step1 raw21342step0; decide +kernel
      have hl : raw21342step1Labels = raw21342step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21342step0 raw21342step0Labels permutation32 permutation7
    mixedMoment B raw21342step1 raw21342step1Labels = mixedMoment B raw21342step2 raw21342step2Labels := by
      have ha : raw21342step2 = raw21342step1 := by apply Matrix.ext; unfold raw21342step2 raw21342step1; decide +kernel
      have hl : raw21342step1Labels = labelEmbedding1 ∘ raw21342step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21342step1 raw21342step1Labels raw21342step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1215 node1215Labels := by rfl

def raw21343 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21343Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21343step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21343step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21343step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21343step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21343step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21343step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21343step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21343 raw21343Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw21343 raw21343Labels = mixedMoment B raw21343step0 raw21343step0Labels := by
      have hz : ∀ j, raw21343 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21343step0 = (fun i j => raw21343 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21343step0 raw21343; decide +kernel
      have hl : raw21343step0Labels = raw21343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21343 raw21343Labels permutation434 hz
    mixedMoment B raw21343step0 raw21343step0Labels = mixedMoment B raw21343step1 raw21343step1Labels := by
      have hz : ∀ j, raw21343step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21343step1 = (fun i j => raw21343step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21343step1 raw21343step0; decide +kernel
      have hl : raw21343step1Labels = raw21343step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21343step0 raw21343step0Labels permutation80 hz
    mixedMoment B raw21343step1 raw21343step1Labels = mixedMoment B raw21343step2 raw21343step2Labels := by
      have ha : raw21343step2 = (fun i j => raw21343step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21343step2 raw21343step1; decide +kernel
      have hl : raw21343step2Labels = raw21343step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21343step1 raw21343step1Labels permutation8 permutation7
    mixedMoment B raw21343step2 raw21343step2Labels = mixedMoment B raw21343step3 raw21343step3Labels := by
      have ha : raw21343step3 = raw21343step2 := by apply Matrix.ext; unfold raw21343step3 raw21343step2; decide +kernel
      have hl : raw21343step2Labels = labelEmbedding1 ∘ raw21343step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21343step2 raw21343step2Labels raw21343step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1239 node1239Labels := by rfl

def raw21344 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21344Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21344step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21344step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21344step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21344step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw21344step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21344step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw21344step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21344 raw21344Labels = mixedMoment B node1469 node1469Labels := by
  calc
    mixedMoment B raw21344 raw21344Labels = mixedMoment B raw21344step0 raw21344step0Labels := by
      have hz : ∀ j, raw21344 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21344step0 = (fun i j => raw21344 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21344step0 raw21344; decide +kernel
      have hl : raw21344step0Labels = raw21344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21344 raw21344Labels permutation434 hz
    mixedMoment B raw21344step0 raw21344step0Labels = mixedMoment B raw21344step1 raw21344step1Labels := by
      have hz : ∀ j, raw21344step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21344step1 = (fun i j => raw21344step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21344step1 raw21344step0; decide +kernel
      have hl : raw21344step1Labels = raw21344step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21344step0 raw21344step0Labels permutation80 hz
    mixedMoment B raw21344step1 raw21344step1Labels = mixedMoment B raw21344step2 raw21344step2Labels := by
      have ha : raw21344step2 = (fun i j => raw21344step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21344step2 raw21344step1; decide +kernel
      have hl : raw21344step2Labels = raw21344step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21344step1 raw21344step1Labels permutation8 permutation7
    mixedMoment B raw21344step2 raw21344step2Labels = mixedMoment B raw21344step3 raw21344step3Labels := by
      have ha : raw21344step3 = raw21344step2 := by apply Matrix.ext; unfold raw21344step3 raw21344step2; decide +kernel
      have hl : raw21344step2Labels = labelEmbedding1 ∘ raw21344step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21344step2 raw21344step2Labels raw21344step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1469 node1469Labels := by rfl

def raw21345 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21345Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21345step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21345step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21345step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21345step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21345 raw21345Labels = mixedMoment B node1359 node1359Labels := by
  calc
    mixedMoment B raw21345 raw21345Labels = mixedMoment B raw21345step0 raw21345step0Labels := by
      have hz : ∀ j, raw21345 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21345step0 = (fun i j => raw21345 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21345step0 raw21345; decide +kernel
      have hl : raw21345step0Labels = raw21345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21345 raw21345Labels permutation434 hz
    mixedMoment B raw21345step0 raw21345step0Labels = mixedMoment B raw21345step1 raw21345step1Labels := by
      have ha : raw21345step1 = (fun i j => raw21345step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21345step1 raw21345step0; decide +kernel
      have hl : raw21345step1Labels = raw21345step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21345step0 raw21345step0Labels permutation32 permutation7
    mixedMoment B raw21345step1 raw21345step1Labels = mixedMoment B raw21345step2 raw21345step2Labels := by
      have ha : raw21345step2 = raw21345step1 := by apply Matrix.ext; unfold raw21345step2 raw21345step1; decide +kernel
      have hl : raw21345step1Labels = labelEmbedding1 ∘ raw21345step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21345step1 raw21345step1Labels raw21345step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1359 node1359Labels := by rfl

def raw21346 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21346Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21346step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21346step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21346step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21346step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21346 raw21346Labels = mixedMoment B node1359 node1359Labels := by
  calc
    mixedMoment B raw21346 raw21346Labels = mixedMoment B raw21346step0 raw21346step0Labels := by
      have hz : ∀ j, raw21346 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21346step0 = (fun i j => raw21346 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21346step0 raw21346; decide +kernel
      have hl : raw21346step0Labels = raw21346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21346 raw21346Labels permutation346 hz
    mixedMoment B raw21346step0 raw21346step0Labels = mixedMoment B raw21346step1 raw21346step1Labels := by
      have ha : raw21346step1 = (fun i j => raw21346step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21346step1 raw21346step0; decide +kernel
      have hl : raw21346step1Labels = raw21346step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21346step0 raw21346step0Labels permutation32 permutation7
    mixedMoment B raw21346step1 raw21346step1Labels = mixedMoment B raw21346step2 raw21346step2Labels := by
      have ha : raw21346step2 = raw21346step1 := by apply Matrix.ext; unfold raw21346step2 raw21346step1; decide +kernel
      have hl : raw21346step1Labels = labelEmbedding1 ∘ raw21346step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21346step1 raw21346step1Labels raw21346step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1359 node1359Labels := by rfl

def raw21347 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21347Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21347step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21347step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21347step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21347step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw21347step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21347step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw21347step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21347 raw21347Labels = mixedMoment B node1372 node1372Labels := by
  calc
    mixedMoment B raw21347 raw21347Labels = mixedMoment B raw21347step0 raw21347step0Labels := by
      have hz : ∀ j, raw21347 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21347step0 = (fun i j => raw21347 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21347step0 raw21347; decide +kernel
      have hl : raw21347step0Labels = raw21347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21347 raw21347Labels permutation434 hz
    mixedMoment B raw21347step0 raw21347step0Labels = mixedMoment B raw21347step1 raw21347step1Labels := by
      have hz : ∀ j, raw21347step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21347step1 = (fun i j => raw21347step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21347step1 raw21347step0; decide +kernel
      have hl : raw21347step1Labels = raw21347step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21347step0 raw21347step0Labels permutation80 hz
    mixedMoment B raw21347step1 raw21347step1Labels = mixedMoment B raw21347step2 raw21347step2Labels := by
      have ha : raw21347step2 = (fun i j => raw21347step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21347step2 raw21347step1; decide +kernel
      have hl : raw21347step2Labels = raw21347step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21347step1 raw21347step1Labels permutation8 permutation7
    mixedMoment B raw21347step2 raw21347step2Labels = mixedMoment B raw21347step3 raw21347step3Labels := by
      have ha : raw21347step3 = raw21347step2 := by apply Matrix.ext; unfold raw21347step3 raw21347step2; decide +kernel
      have hl : raw21347step2Labels = labelEmbedding1 ∘ raw21347step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21347step2 raw21347step2Labels raw21347step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1372 node1372Labels := by rfl

def raw21348 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21348Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21348step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21348step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21348step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21348step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw21348step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21348step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw21348step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21348 raw21348Labels = mixedMoment B node1369 node1369Labels := by
  calc
    mixedMoment B raw21348 raw21348Labels = mixedMoment B raw21348step0 raw21348step0Labels := by
      have hz : ∀ j, raw21348 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21348step0 = (fun i j => raw21348 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21348step0 raw21348; decide +kernel
      have hl : raw21348step0Labels = raw21348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21348 raw21348Labels permutation434 hz
    mixedMoment B raw21348step0 raw21348step0Labels = mixedMoment B raw21348step1 raw21348step1Labels := by
      have hz : ∀ j, raw21348step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21348step1 = (fun i j => raw21348step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21348step1 raw21348step0; decide +kernel
      have hl : raw21348step1Labels = raw21348step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21348step0 raw21348step0Labels permutation80 hz
    mixedMoment B raw21348step1 raw21348step1Labels = mixedMoment B raw21348step2 raw21348step2Labels := by
      have ha : raw21348step2 = (fun i j => raw21348step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21348step2 raw21348step1; decide +kernel
      have hl : raw21348step2Labels = raw21348step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21348step1 raw21348step1Labels permutation8 permutation7
    mixedMoment B raw21348step2 raw21348step2Labels = mixedMoment B raw21348step3 raw21348step3Labels := by
      have ha : raw21348step3 = raw21348step2 := by apply Matrix.ext; unfold raw21348step3 raw21348step2; decide +kernel
      have hl : raw21348step2Labels = labelEmbedding1 ∘ raw21348step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21348step2 raw21348step2Labels raw21348step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1369 node1369Labels := by rfl

def raw21349 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21349Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21349step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21349step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21349step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21349step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21349 raw21349Labels = mixedMoment B node1476 node1476Labels := by
  calc
    mixedMoment B raw21349 raw21349Labels = mixedMoment B raw21349step0 raw21349step0Labels := by
      have hz : ∀ j, raw21349 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21349step0 = (fun i j => raw21349 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21349step0 raw21349; decide +kernel
      have hl : raw21349step0Labels = raw21349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21349 raw21349Labels permutation434 hz
    mixedMoment B raw21349step0 raw21349step0Labels = mixedMoment B raw21349step1 raw21349step1Labels := by
      have ha : raw21349step1 = (fun i j => raw21349step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21349step1 raw21349step0; decide +kernel
      have hl : raw21349step1Labels = raw21349step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21349step0 raw21349step0Labels permutation32 permutation7
    mixedMoment B raw21349step1 raw21349step1Labels = mixedMoment B raw21349step2 raw21349step2Labels := by
      have ha : raw21349step2 = raw21349step1 := by apply Matrix.ext; unfold raw21349step2 raw21349step1; decide +kernel
      have hl : raw21349step1Labels = labelEmbedding1 ∘ raw21349step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21349step1 raw21349step1Labels raw21349step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1476 node1476Labels := by rfl

def raw21350 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21350Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21350step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21350step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21350step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21350step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21350step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21350step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21350step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21350 raw21350Labels = mixedMoment B node1413 node1413Labels := by
  calc
    mixedMoment B raw21350 raw21350Labels = mixedMoment B raw21350step0 raw21350step0Labels := by
      have hz : ∀ j, raw21350 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21350step0 = (fun i j => raw21350 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21350step0 raw21350; decide +kernel
      have hl : raw21350step0Labels = raw21350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21350 raw21350Labels permutation434 hz
    mixedMoment B raw21350step0 raw21350step0Labels = mixedMoment B raw21350step1 raw21350step1Labels := by
      have hz : ∀ j, raw21350step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21350step1 = (fun i j => raw21350step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21350step1 raw21350step0; decide +kernel
      have hl : raw21350step1Labels = raw21350step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21350step0 raw21350step0Labels permutation56 hz
    mixedMoment B raw21350step1 raw21350step1Labels = mixedMoment B raw21350step2 raw21350step2Labels := by
      have ha : raw21350step2 = (fun i j => raw21350step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21350step2 raw21350step1; decide +kernel
      have hl : raw21350step2Labels = raw21350step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21350step1 raw21350step1Labels permutation8 permutation7
    mixedMoment B raw21350step2 raw21350step2Labels = mixedMoment B raw21350step3 raw21350step3Labels := by
      have ha : raw21350step3 = raw21350step2 := by apply Matrix.ext; unfold raw21350step3 raw21350step2; decide +kernel
      have hl : raw21350step2Labels = labelEmbedding1 ∘ raw21350step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21350step2 raw21350step2Labels raw21350step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1413 node1413Labels := by rfl

def raw21351 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21351Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21351step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21351step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21351 raw21351Labels = mixedMoment B node1378 node1378Labels := by
  calc
    mixedMoment B raw21351 raw21351Labels = mixedMoment B raw21351step0 raw21351step0Labels := by
      have ha : raw21351step0 = (fun i j => raw21351 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21351step0 raw21351; decide +kernel
      have hl : raw21351step0Labels = raw21351Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21351 raw21351Labels permutation152 permutation7
    mixedMoment B raw21351step0 raw21351step0Labels = mixedMoment B raw21351step1 raw21351step1Labels := by
      have ha : raw21351step1 = raw21351step0 := by apply Matrix.ext; unfold raw21351step1 raw21351step0; decide +kernel
      have hl : raw21351step0Labels = labelEmbedding1 ∘ raw21351step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21351step0 raw21351step0Labels raw21351step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1378 node1378Labels := by rfl

def raw21352 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21352Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21352step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21352step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21352step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21352 raw21352Labels = mixedMoment B node1388 node1388Labels := by
  calc
    mixedMoment B raw21352 raw21352Labels = mixedMoment B raw21352step0 raw21352step0Labels := by
      have hz : ∀ j, raw21352 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21352step0 = (fun i j => raw21352 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21352step0 raw21352; decide +kernel
      have hl : raw21352step0Labels = raw21352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21352 raw21352Labels permutation434 hz
    mixedMoment B raw21352step0 raw21352step0Labels = mixedMoment B raw21352step1 raw21352step1Labels := by
      have ha : raw21352step1 = (fun i j => raw21352step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21352step1 raw21352step0; decide +kernel
      have hl : raw21352step1Labels = raw21352step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21352step0 raw21352step0Labels permutation32 permutation7
    mixedMoment B raw21352step1 raw21352step1Labels = mixedMoment B raw21352step2 raw21352step2Labels := by
      have ha : raw21352step2 = raw21352step1 := by apply Matrix.ext; unfold raw21352step2 raw21352step1; decide +kernel
      have hl : raw21352step1Labels = labelEmbedding1 ∘ raw21352step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21352step1 raw21352step1Labels raw21352step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1388 node1388Labels := by rfl

def raw21353 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21353Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21353step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21353step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21353step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21353step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21353 raw21353Labels = mixedMoment B node1385 node1385Labels := by
  calc
    mixedMoment B raw21353 raw21353Labels = mixedMoment B raw21353step0 raw21353step0Labels := by
      have hz : ∀ j, raw21353 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21353step0 = (fun i j => raw21353 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21353step0 raw21353; decide +kernel
      have hl : raw21353step0Labels = raw21353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21353 raw21353Labels permutation434 hz
    mixedMoment B raw21353step0 raw21353step0Labels = mixedMoment B raw21353step1 raw21353step1Labels := by
      have ha : raw21353step1 = (fun i j => raw21353step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21353step1 raw21353step0; decide +kernel
      have hl : raw21353step1Labels = raw21353step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21353step0 raw21353step0Labels permutation32 permutation7
    mixedMoment B raw21353step1 raw21353step1Labels = mixedMoment B raw21353step2 raw21353step2Labels := by
      have ha : raw21353step2 = raw21353step1 := by apply Matrix.ext; unfold raw21353step2 raw21353step1; decide +kernel
      have hl : raw21353step1Labels = labelEmbedding1 ∘ raw21353step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21353step1 raw21353step1Labels raw21353step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1385 node1385Labels := by rfl

def raw21354 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21354Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21354step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21354step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21354step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21354step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21354step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21354 raw21354Labels = mixedMoment B node1476 node1476Labels := by
  calc
    mixedMoment B raw21354 raw21354Labels = mixedMoment B raw21354step0 raw21354step0Labels := by
      have hz : ∀ j, raw21354 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21354step0 = (fun i j => raw21354 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21354step0 raw21354; decide +kernel
      have hl : raw21354step0Labels = raw21354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21354 raw21354Labels permutation346 hz
    mixedMoment B raw21354step0 raw21354step0Labels = mixedMoment B raw21354step1 raw21354step1Labels := by
      have ha : raw21354step1 = (fun i j => raw21354step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21354step1 raw21354step0; decide +kernel
      have hl : raw21354step1Labels = raw21354step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21354step0 raw21354step0Labels permutation32 permutation7
    mixedMoment B raw21354step1 raw21354step1Labels = mixedMoment B raw21354step2 raw21354step2Labels := by
      have ha : raw21354step2 = raw21354step1 := by apply Matrix.ext; unfold raw21354step2 raw21354step1; decide +kernel
      have hl : raw21354step1Labels = labelEmbedding1 ∘ raw21354step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21354step1 raw21354step1Labels raw21354step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1476 node1476Labels := by rfl

def raw21355 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21355Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21355step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21355step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21355step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21355step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21355step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21355step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21355step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21355 raw21355Labels = mixedMoment B node1413 node1413Labels := by
  calc
    mixedMoment B raw21355 raw21355Labels = mixedMoment B raw21355step0 raw21355step0Labels := by
      have hz : ∀ j, raw21355 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21355step0 = (fun i j => raw21355 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21355step0 raw21355; decide +kernel
      have hl : raw21355step0Labels = raw21355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21355 raw21355Labels permutation346 hz
    mixedMoment B raw21355step0 raw21355step0Labels = mixedMoment B raw21355step1 raw21355step1Labels := by
      have hz : ∀ j, raw21355step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21355step1 = (fun i j => raw21355step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21355step1 raw21355step0; decide +kernel
      have hl : raw21355step1Labels = raw21355step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21355step0 raw21355step0Labels permutation56 hz
    mixedMoment B raw21355step1 raw21355step1Labels = mixedMoment B raw21355step2 raw21355step2Labels := by
      have ha : raw21355step2 = (fun i j => raw21355step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21355step2 raw21355step1; decide +kernel
      have hl : raw21355step2Labels = raw21355step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21355step1 raw21355step1Labels permutation8 permutation7
    mixedMoment B raw21355step2 raw21355step2Labels = mixedMoment B raw21355step3 raw21355step3Labels := by
      have ha : raw21355step3 = raw21355step2 := by apply Matrix.ext; unfold raw21355step3 raw21355step2; decide +kernel
      have hl : raw21355step2Labels = labelEmbedding1 ∘ raw21355step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21355step2 raw21355step2Labels raw21355step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1413 node1413Labels := by rfl

def raw21356 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21356Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21356step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21356step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21356step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21356 raw21356Labels = mixedMoment B node1378 node1378Labels := by
  calc
    mixedMoment B raw21356 raw21356Labels = mixedMoment B raw21356step0 raw21356step0Labels := by
      have ha : raw21356step0 = (fun i j => raw21356 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21356step0 raw21356; decide +kernel
      have hl : raw21356step0Labels = raw21356Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21356 raw21356Labels permutation158 permutation7
    mixedMoment B raw21356step0 raw21356step0Labels = mixedMoment B raw21356step1 raw21356step1Labels := by
      have ha : raw21356step1 = raw21356step0 := by apply Matrix.ext; unfold raw21356step1 raw21356step0; decide +kernel
      have hl : raw21356step0Labels = labelEmbedding1 ∘ raw21356step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21356step0 raw21356step0Labels raw21356step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1378 node1378Labels := by rfl

def raw21357 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21357Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21357step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21357step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21357step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw21357step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21357 raw21357Labels = mixedMoment B node1388 node1388Labels := by
  calc
    mixedMoment B raw21357 raw21357Labels = mixedMoment B raw21357step0 raw21357step0Labels := by
      have hz : ∀ j, raw21357 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21357step0 = (fun i j => raw21357 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21357step0 raw21357; decide +kernel
      have hl : raw21357step0Labels = raw21357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21357 raw21357Labels permutation346 hz
    mixedMoment B raw21357step0 raw21357step0Labels = mixedMoment B raw21357step1 raw21357step1Labels := by
      have ha : raw21357step1 = (fun i j => raw21357step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21357step1 raw21357step0; decide +kernel
      have hl : raw21357step1Labels = raw21357step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21357step0 raw21357step0Labels permutation32 permutation7
    mixedMoment B raw21357step1 raw21357step1Labels = mixedMoment B raw21357step2 raw21357step2Labels := by
      have ha : raw21357step2 = raw21357step1 := by apply Matrix.ext; unfold raw21357step2 raw21357step1; decide +kernel
      have hl : raw21357step1Labels = labelEmbedding1 ∘ raw21357step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21357step1 raw21357step1Labels raw21357step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1388 node1388Labels := by rfl

def raw21358 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21358Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw21358step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21358step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21358step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw21358step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21358 raw21358Labels = mixedMoment B node1385 node1385Labels := by
  calc
    mixedMoment B raw21358 raw21358Labels = mixedMoment B raw21358step0 raw21358step0Labels := by
      have hz : ∀ j, raw21358 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21358step0 = (fun i j => raw21358 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21358step0 raw21358; decide +kernel
      have hl : raw21358step0Labels = raw21358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21358 raw21358Labels permutation346 hz
    mixedMoment B raw21358step0 raw21358step0Labels = mixedMoment B raw21358step1 raw21358step1Labels := by
      have ha : raw21358step1 = (fun i j => raw21358step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21358step1 raw21358step0; decide +kernel
      have hl : raw21358step1Labels = raw21358step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21358step0 raw21358step0Labels permutation32 permutation7
    mixedMoment B raw21358step1 raw21358step1Labels = mixedMoment B raw21358step2 raw21358step2Labels := by
      have ha : raw21358step2 = raw21358step1 := by apply Matrix.ext; unfold raw21358step2 raw21358step1; decide +kernel
      have hl : raw21358step1Labels = labelEmbedding1 ∘ raw21358step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21358step1 raw21358step1Labels raw21358step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1385 node1385Labels := by rfl

def raw21359 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21359Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21359step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21359step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21359step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21359step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw21359step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21359step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw21359step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21359 raw21359Labels = mixedMoment B node1481 node1481Labels := by
  calc
    mixedMoment B raw21359 raw21359Labels = mixedMoment B raw21359step0 raw21359step0Labels := by
      have hz : ∀ j, raw21359 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21359step0 = (fun i j => raw21359 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21359step0 raw21359; decide +kernel
      have hl : raw21359step0Labels = raw21359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21359 raw21359Labels permutation434 hz
    mixedMoment B raw21359step0 raw21359step0Labels = mixedMoment B raw21359step1 raw21359step1Labels := by
      have hz : ∀ j, raw21359step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21359step1 = (fun i j => raw21359step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21359step1 raw21359step0; decide +kernel
      have hl : raw21359step1Labels = raw21359step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21359step0 raw21359step0Labels permutation80 hz
    mixedMoment B raw21359step1 raw21359step1Labels = mixedMoment B raw21359step2 raw21359step2Labels := by
      have ha : raw21359step2 = (fun i j => raw21359step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21359step2 raw21359step1; decide +kernel
      have hl : raw21359step2Labels = raw21359step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21359step1 raw21359step1Labels permutation8 permutation7
    mixedMoment B raw21359step2 raw21359step2Labels = mixedMoment B raw21359step3 raw21359step3Labels := by
      have ha : raw21359step3 = raw21359step2 := by apply Matrix.ext; unfold raw21359step3 raw21359step2; decide +kernel
      have hl : raw21359step2Labels = labelEmbedding1 ∘ raw21359step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21359step2 raw21359step2Labels raw21359step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1481 node1481Labels := by rfl

def raw21360 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21360Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21360step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21360step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21360step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21360step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-2, -1, 3]]
def raw21360step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21360step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![3, -1, -2]]
def raw21360step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21360step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![3, -1, -2]]
def raw21360step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21360 raw21360Labels = mixedMoment B node1445 node1445Labels := by
  calc
    mixedMoment B raw21360 raw21360Labels = mixedMoment B raw21360step0 raw21360step0Labels := by
      have hz : ∀ j, raw21360 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21360step0 = (fun i j => raw21360 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21360step0 raw21360; decide +kernel
      have hl : raw21360step0Labels = raw21360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21360 raw21360Labels permutation434 hz
    mixedMoment B raw21360step0 raw21360step0Labels = mixedMoment B raw21360step1 raw21360step1Labels := by
      have hz : ∀ j, raw21360step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21360step1 = (fun i j => raw21360step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21360step1 raw21360step0; decide +kernel
      have hl : raw21360step1Labels = raw21360step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21360step0 raw21360step0Labels permutation80 hz
    mixedMoment B raw21360step1 raw21360step1Labels = mixedMoment B raw21360step2 raw21360step2Labels := by
      have hz : ∀ j, raw21360step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21360step2 = (fun i j => raw21360step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21360step2 raw21360step1; decide +kernel
      have hl : raw21360step2Labels = raw21360step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21360step1 raw21360step1Labels permutation14 hz
    mixedMoment B raw21360step2 raw21360step2Labels = mixedMoment B raw21360step3 raw21360step3Labels := by
      have ha : raw21360step3 = (fun i j => raw21360step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21360step3 raw21360step2; decide +kernel
      have hl : raw21360step3Labels = raw21360step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21360step2 raw21360step2Labels permutation2 permutation7
    mixedMoment B raw21360step3 raw21360step3Labels = mixedMoment B raw21360step4 raw21360step4Labels := by
      have ha : raw21360step4 = raw21360step3 := by apply Matrix.ext; unfold raw21360step4 raw21360step3; decide +kernel
      have hl : raw21360step3Labels = labelEmbedding1 ∘ raw21360step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21360step3 raw21360step3Labels raw21360step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1445 node1445Labels := by rfl

def raw21361 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21361Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21361step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw21361step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21361step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw21361step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21361 raw21361Labels = mixedMoment B node1394 node1394Labels := by
  calc
    mixedMoment B raw21361 raw21361Labels = mixedMoment B raw21361step0 raw21361step0Labels := by
      have hz : ∀ j, raw21361 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21361step0 = (fun i j => raw21361 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21361step0 raw21361; decide +kernel
      have hl : raw21361step0Labels = raw21361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21361 raw21361Labels permutation434 hz
    mixedMoment B raw21361step0 raw21361step0Labels = mixedMoment B raw21361step1 raw21361step1Labels := by
      have ha : raw21361step1 = (fun i j => raw21361step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21361step1 raw21361step0; decide +kernel
      have hl : raw21361step1Labels = raw21361step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21361step0 raw21361step0Labels permutation32 permutation7
    mixedMoment B raw21361step1 raw21361step1Labels = mixedMoment B raw21361step2 raw21361step2Labels := by
      have ha : raw21361step2 = raw21361step1 := by apply Matrix.ext; unfold raw21361step2 raw21361step1; decide +kernel
      have hl : raw21361step1Labels = labelEmbedding1 ∘ raw21361step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21361step1 raw21361step1Labels raw21361step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1394 node1394Labels := by rfl

def raw21362 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21362Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21362step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw21362step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw21362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21362 raw21362Labels = mixedMoment B node1394 node1394Labels := by
  calc
    mixedMoment B raw21362 raw21362Labels = mixedMoment B raw21362step0 raw21362step0Labels := by
      have hz : ∀ j, raw21362 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21362step0 = (fun i j => raw21362 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21362step0 raw21362; decide +kernel
      have hl : raw21362step0Labels = raw21362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21362 raw21362Labels permutation346 hz
    mixedMoment B raw21362step0 raw21362step0Labels = mixedMoment B raw21362step1 raw21362step1Labels := by
      have ha : raw21362step1 = (fun i j => raw21362step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21362step1 raw21362step0; decide +kernel
      have hl : raw21362step1Labels = raw21362step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21362step0 raw21362step0Labels permutation32 permutation7
    mixedMoment B raw21362step1 raw21362step1Labels = mixedMoment B raw21362step2 raw21362step2Labels := by
      have ha : raw21362step2 = raw21362step1 := by apply Matrix.ext; unfold raw21362step2 raw21362step1; decide +kernel
      have hl : raw21362step1Labels = labelEmbedding1 ∘ raw21362step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21362step1 raw21362step1Labels raw21362step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1394 node1394Labels := by rfl

def raw21363 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21363Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21363step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21363step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw21363step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21363step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw21363step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21363step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw21363step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21363 raw21363Labels = mixedMoment B node1408 node1408Labels := by
  calc
    mixedMoment B raw21363 raw21363Labels = mixedMoment B raw21363step0 raw21363step0Labels := by
      have hz : ∀ j, raw21363 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21363step0 = (fun i j => raw21363 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21363step0 raw21363; decide +kernel
      have hl : raw21363step0Labels = raw21363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21363 raw21363Labels permutation434 hz
    mixedMoment B raw21363step0 raw21363step0Labels = mixedMoment B raw21363step1 raw21363step1Labels := by
      have hz : ∀ j, raw21363step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21363step1 = (fun i j => raw21363step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21363step1 raw21363step0; decide +kernel
      have hl : raw21363step1Labels = raw21363step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21363step0 raw21363step0Labels permutation80 hz
    mixedMoment B raw21363step1 raw21363step1Labels = mixedMoment B raw21363step2 raw21363step2Labels := by
      have ha : raw21363step2 = (fun i j => raw21363step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21363step2 raw21363step1; decide +kernel
      have hl : raw21363step2Labels = raw21363step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21363step1 raw21363step1Labels permutation8 permutation7
    mixedMoment B raw21363step2 raw21363step2Labels = mixedMoment B raw21363step3 raw21363step3Labels := by
      have ha : raw21363step3 = raw21363step2 := by apply Matrix.ext; unfold raw21363step3 raw21363step2; decide +kernel
      have hl : raw21363step2Labels = labelEmbedding1 ∘ raw21363step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21363step2 raw21363step2Labels raw21363step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1408 node1408Labels := by rfl

def raw21364 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21364Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21364step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21364step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21364step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21364step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def raw21364step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21364step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def raw21364step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21364 raw21364Labels = mixedMoment B node1484 node1484Labels := by
  calc
    mixedMoment B raw21364 raw21364Labels = mixedMoment B raw21364step0 raw21364step0Labels := by
      have hz : ∀ j, raw21364 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21364step0 = (fun i j => raw21364 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21364step0 raw21364; decide +kernel
      have hl : raw21364step0Labels = raw21364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21364 raw21364Labels permutation434 hz
    mixedMoment B raw21364step0 raw21364step0Labels = mixedMoment B raw21364step1 raw21364step1Labels := by
      have hz : ∀ j, raw21364step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21364step1 = (fun i j => raw21364step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21364step1 raw21364step0; decide +kernel
      have hl : raw21364step1Labels = raw21364step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21364step0 raw21364step0Labels permutation80 hz
    mixedMoment B raw21364step1 raw21364step1Labels = mixedMoment B raw21364step2 raw21364step2Labels := by
      have ha : raw21364step2 = (fun i j => raw21364step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21364step2 raw21364step1; decide +kernel
      have hl : raw21364step2Labels = raw21364step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21364step1 raw21364step1Labels permutation8 permutation7
    mixedMoment B raw21364step2 raw21364step2Labels = mixedMoment B raw21364step3 raw21364step3Labels := by
      have ha : raw21364step3 = raw21364step2 := by apply Matrix.ext; unfold raw21364step3 raw21364step2; decide +kernel
      have hl : raw21364step2Labels = labelEmbedding1 ∘ raw21364step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21364step2 raw21364step2Labels raw21364step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1484 node1484Labels := by rfl

def raw21365 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21365Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21365step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21365step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21365step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21365step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21365 raw21365Labels = mixedMoment B node1397 node1397Labels := by
  calc
    mixedMoment B raw21365 raw21365Labels = mixedMoment B raw21365step0 raw21365step0Labels := by
      have hz : ∀ j, raw21365 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21365step0 = (fun i j => raw21365 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21365step0 raw21365; decide +kernel
      have hl : raw21365step0Labels = raw21365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21365 raw21365Labels permutation434 hz
    mixedMoment B raw21365step0 raw21365step0Labels = mixedMoment B raw21365step1 raw21365step1Labels := by
      have ha : raw21365step1 = (fun i j => raw21365step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21365step1 raw21365step0; decide +kernel
      have hl : raw21365step1Labels = raw21365step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21365step0 raw21365step0Labels permutation32 permutation7
    mixedMoment B raw21365step1 raw21365step1Labels = mixedMoment B raw21365step2 raw21365step2Labels := by
      have ha : raw21365step2 = raw21365step1 := by apply Matrix.ext; unfold raw21365step2 raw21365step1; decide +kernel
      have hl : raw21365step1Labels = labelEmbedding1 ∘ raw21365step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21365step1 raw21365step1Labels raw21365step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1397 node1397Labels := by rfl

def raw21366 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21366Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21366step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21366step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21366step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw21366step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21366 raw21366Labels = mixedMoment B node1397 node1397Labels := by
  calc
    mixedMoment B raw21366 raw21366Labels = mixedMoment B raw21366step0 raw21366step0Labels := by
      have hz : ∀ j, raw21366 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21366step0 = (fun i j => raw21366 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21366step0 raw21366; decide +kernel
      have hl : raw21366step0Labels = raw21366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21366 raw21366Labels permutation346 hz
    mixedMoment B raw21366step0 raw21366step0Labels = mixedMoment B raw21366step1 raw21366step1Labels := by
      have ha : raw21366step1 = (fun i j => raw21366step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21366step1 raw21366step0; decide +kernel
      have hl : raw21366step1Labels = raw21366step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21366step0 raw21366step0Labels permutation32 permutation7
    mixedMoment B raw21366step1 raw21366step1Labels = mixedMoment B raw21366step2 raw21366step2Labels := by
      have ha : raw21366step2 = raw21366step1 := by apply Matrix.ext; unfold raw21366step2 raw21366step1; decide +kernel
      have hl : raw21366step1Labels = labelEmbedding1 ∘ raw21366step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21366step1 raw21366step1Labels raw21366step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1397 node1397Labels := by rfl

def raw21367 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21367step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21367step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21367step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21367step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21367step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21367 raw21367Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw21367 raw21367Labels = mixedMoment B raw21367step0 raw21367step0Labels := by
      have hz : ∀ j, raw21367 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21367step0 = (fun i j => raw21367 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21367step0 raw21367; decide +kernel
      have hl : raw21367step0Labels = raw21367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21367 raw21367Labels permutation434 hz
    mixedMoment B raw21367step0 raw21367step0Labels = mixedMoment B raw21367step1 raw21367step1Labels := by
      have hz : ∀ j, raw21367step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21367step1 = (fun i j => raw21367step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21367step1 raw21367step0; decide +kernel
      have hl : raw21367step1Labels = raw21367step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21367step0 raw21367step0Labels permutation80 hz
    mixedMoment B raw21367step1 raw21367step1Labels = mixedMoment B raw21367step2 raw21367step2Labels := by
      have ha : raw21367step2 = (fun i j => raw21367step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21367step2 raw21367step1; decide +kernel
      have hl : raw21367step2Labels = raw21367step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21367step1 raw21367step1Labels permutation8 permutation4
    mixedMoment B raw21367step2 raw21367step2Labels = mixedMoment B raw21367step3 raw21367step3Labels := by
      have ha : raw21367step3 = -raw21367step2 := by apply Matrix.ext; change ∀ i j, raw21367step3 i j = -(raw21367step2 i j); unfold raw21367step3 raw21367step2; decide +kernel
      have hl : raw21367step3Labels = raw21367step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1750 node1750Labels := by rfl

def raw21368 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21368step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21368step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw21368step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21368step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw21368step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21368 raw21368Labels = mixedMoment B node857 node857Labels := by
  calc
    mixedMoment B raw21368 raw21368Labels = mixedMoment B raw21368step0 raw21368step0Labels := by
      have hz : ∀ j, raw21368 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21368step0 = (fun i j => raw21368 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21368step0 raw21368; decide +kernel
      have hl : raw21368step0Labels = raw21368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21368 raw21368Labels permutation434 hz
    mixedMoment B raw21368step0 raw21368step0Labels = mixedMoment B raw21368step1 raw21368step1Labels := by
      have hz : ∀ j, raw21368step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21368step1 = (fun i j => raw21368step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21368step1 raw21368step0; decide +kernel
      have hl : raw21368step1Labels = raw21368step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21368step0 raw21368step0Labels permutation80 hz
    mixedMoment B raw21368step1 raw21368step1Labels = mixedMoment B raw21368step2 raw21368step2Labels := by
      have ha : raw21368step2 = (fun i j => raw21368step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21368step2 raw21368step1; decide +kernel
      have hl : raw21368step2Labels = raw21368step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21368step1 raw21368step1Labels permutation11 permutation4
    mixedMoment B raw21368step2 raw21368step2Labels = mixedMoment B raw21368step3 raw21368step3Labels := by
      have ha : raw21368step3 = -raw21368step2 := by apply Matrix.ext; change ∀ i j, raw21368step3 i j = -(raw21368step2 i j); unfold raw21368step3 raw21368step2; decide +kernel
      have hl : raw21368step3Labels = raw21368step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node857 node857Labels := by rfl

def raw21369 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21369step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21369step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21369 raw21369Labels = mixedMoment B node847 node847Labels := by
  calc
    mixedMoment B raw21369 raw21369Labels = mixedMoment B raw21369step0 raw21369step0Labels := by
      have hz : ∀ j, raw21369 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21369step0 = (fun i j => raw21369 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21369step0 raw21369; decide +kernel
      have hl : raw21369step0Labels = raw21369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21369 raw21369Labels permutation434 hz
    mixedMoment B raw21369step0 raw21369step0Labels = mixedMoment B raw21369step1 raw21369step1Labels := by
      have ha : raw21369step1 = (fun i j => raw21369step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21369step1 raw21369step0; decide +kernel
      have hl : raw21369step1Labels = raw21369step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21369step0 raw21369step0Labels permutation32 permutation4
    mixedMoment B raw21369step1 raw21369step1Labels = mixedMoment B raw21369step2 raw21369step2Labels := by
      have ha : raw21369step2 = -raw21369step1 := by apply Matrix.ext; change ∀ i j, raw21369step2 i j = -(raw21369step1 i j); unfold raw21369step2 raw21369step1; decide +kernel
      have hl : raw21369step2Labels = raw21369step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node847 node847Labels := by rfl

def raw21370 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw21370step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21370step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw21370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21370step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw21370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21370 raw21370Labels = mixedMoment B node847 node847Labels := by
  calc
    mixedMoment B raw21370 raw21370Labels = mixedMoment B raw21370step0 raw21370step0Labels := by
      have hz : ∀ j, raw21370 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21370step0 = (fun i j => raw21370 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21370step0 raw21370; decide +kernel
      have hl : raw21370step0Labels = raw21370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21370 raw21370Labels permutation346 hz
    mixedMoment B raw21370step0 raw21370step0Labels = mixedMoment B raw21370step1 raw21370step1Labels := by
      have ha : raw21370step1 = (fun i j => raw21370step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21370step1 raw21370step0; decide +kernel
      have hl : raw21370step1Labels = raw21370step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21370step0 raw21370step0Labels permutation32 permutation4
    mixedMoment B raw21370step1 raw21370step1Labels = mixedMoment B raw21370step2 raw21370step2Labels := by
      have ha : raw21370step2 = -raw21370step1 := by apply Matrix.ext; change ∀ i j, raw21370step2 i j = -(raw21370step1 i j); unfold raw21370step2 raw21370step1; decide +kernel
      have hl : raw21370step2Labels = raw21370step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node847 node847Labels := by rfl

def raw21371 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21371step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw21371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21371step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw21371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21371step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw21371step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21371 raw21371Labels = mixedMoment B node853 node853Labels := by
  calc
    mixedMoment B raw21371 raw21371Labels = mixedMoment B raw21371step0 raw21371step0Labels := by
      have hz : ∀ j, raw21371 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21371step0 = (fun i j => raw21371 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21371step0 raw21371; decide +kernel
      have hl : raw21371step0Labels = raw21371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21371 raw21371Labels permutation434 hz
    mixedMoment B raw21371step0 raw21371step0Labels = mixedMoment B raw21371step1 raw21371step1Labels := by
      have hz : ∀ j, raw21371step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21371step1 = (fun i j => raw21371step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21371step1 raw21371step0; decide +kernel
      have hl : raw21371step1Labels = raw21371step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21371step0 raw21371step0Labels permutation80 hz
    mixedMoment B raw21371step1 raw21371step1Labels = mixedMoment B raw21371step2 raw21371step2Labels := by
      have ha : raw21371step2 = (fun i j => raw21371step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21371step2 raw21371step1; decide +kernel
      have hl : raw21371step2Labels = raw21371step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21371step1 raw21371step1Labels permutation9 permutation4
    mixedMoment B raw21371step2 raw21371step2Labels = mixedMoment B raw21371step3 raw21371step3Labels := by
      have ha : raw21371step3 = -raw21371step2 := by apply Matrix.ext; change ∀ i j, raw21371step3 i j = -(raw21371step2 i j); unfold raw21371step3 raw21371step2; decide +kernel
      have hl : raw21371step3Labels = raw21371step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node853 node853Labels := by rfl

def raw21372 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21372step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw21372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21372step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw21372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21372step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw21372step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21372 raw21372Labels = mixedMoment B node851 node851Labels := by
  calc
    mixedMoment B raw21372 raw21372Labels = mixedMoment B raw21372step0 raw21372step0Labels := by
      have hz : ∀ j, raw21372 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21372step0 = (fun i j => raw21372 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21372step0 raw21372; decide +kernel
      have hl : raw21372step0Labels = raw21372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21372 raw21372Labels permutation434 hz
    mixedMoment B raw21372step0 raw21372step0Labels = mixedMoment B raw21372step1 raw21372step1Labels := by
      have hz : ∀ j, raw21372step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21372step1 = (fun i j => raw21372step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21372step1 raw21372step0; decide +kernel
      have hl : raw21372step1Labels = raw21372step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21372step0 raw21372step0Labels permutation80 hz
    mixedMoment B raw21372step1 raw21372step1Labels = mixedMoment B raw21372step2 raw21372step2Labels := by
      have ha : raw21372step2 = (fun i j => raw21372step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21372step2 raw21372step1; decide +kernel
      have hl : raw21372step2Labels = raw21372step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21372step1 raw21372step1Labels permutation8 permutation4
    mixedMoment B raw21372step2 raw21372step2Labels = mixedMoment B raw21372step3 raw21372step3Labels := by
      have ha : raw21372step3 = -raw21372step2 := by apply Matrix.ext; change ∀ i j, raw21372step3 i j = -(raw21372step2 i j); unfold raw21372step3 raw21372step2; decide +kernel
      have hl : raw21372step3Labels = raw21372step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node851 node851Labels := by rfl

def raw21373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21373Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21373step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21373step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw21373step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21373 raw21373Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw21373 raw21373Labels = mixedMoment B raw21373step0 raw21373step0Labels := by
      have hz : ∀ j, raw21373 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21373step0 = (fun i j => raw21373 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21373step0 raw21373; decide +kernel
      have hl : raw21373step0Labels = raw21373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21373 raw21373Labels permutation434 hz
    mixedMoment B raw21373step0 raw21373step0Labels = mixedMoment B raw21373step1 raw21373step1Labels := by
      have hz : ∀ j, raw21373step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21373step1 = (fun i j => raw21373step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21373step1 raw21373step0; decide +kernel
      have hl : raw21373step1Labels = raw21373step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21373step0 raw21373step0Labels permutation80 hz
    _ = mixedMoment B node4894 node4894Labels := by rfl

def raw21374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21374step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21374step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21374step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21374step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21374 raw21374Labels = mixedMoment B node4177 node4177Labels := by
  calc
    mixedMoment B raw21374 raw21374Labels = mixedMoment B raw21374step0 raw21374step0Labels := by
      have hz : ∀ j, raw21374 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21374step0 = (fun i j => raw21374 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21374step0 raw21374; decide +kernel
      have hl : raw21374step0Labels = raw21374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21374 raw21374Labels permutation434 hz
    mixedMoment B raw21374step0 raw21374step0Labels = mixedMoment B raw21374step1 raw21374step1Labels := by
      have hz : ∀ j, raw21374step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21374step1 = (fun i j => raw21374step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21374step1 raw21374step0; decide +kernel
      have hl : raw21374step1Labels = raw21374step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21374step0 raw21374step0Labels permutation80 hz
    mixedMoment B raw21374step1 raw21374step1Labels = mixedMoment B raw21374step2 raw21374step2Labels := by
      have ha : raw21374step2 = (fun i j => raw21374step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21374step2 raw21374step1; decide +kernel
      have hl : raw21374step2Labels = raw21374step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21374step1 raw21374step1Labels permutation10 permutation2
    _ = mixedMoment B node4177 node4177Labels := by rfl

def raw21375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw21375step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21375step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21375step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21375 raw21375Labels = mixedMoment B node4346 node4346Labels := by
  calc
    mixedMoment B raw21375 raw21375Labels = mixedMoment B raw21375step0 raw21375step0Labels := by
      have hz : ∀ j, raw21375 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21375step0 = (fun i j => raw21375 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21375step0 raw21375; decide +kernel
      have hl : raw21375step0Labels = raw21375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21375 raw21375Labels permutation434 hz
    mixedMoment B raw21375step0 raw21375step0Labels = mixedMoment B raw21375step1 raw21375step1Labels := by
      have ha : raw21375step1 = (fun i j => raw21375step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21375step1 raw21375step0; decide +kernel
      have hl : raw21375step1Labels = raw21375step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21375step0 raw21375step0Labels permutation40 permutation2
    _ = mixedMoment B node4346 node4346Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
