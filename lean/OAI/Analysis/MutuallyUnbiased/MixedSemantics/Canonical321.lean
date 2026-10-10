import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw41088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw41088Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1]]
def raw41088step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, 1, -2], ![1, -2, 1]]
def raw41088step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41088step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-2, 1, 1], ![-2, 0, 2]]
def raw41088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41088step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw41088step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41088 raw41088Labels = mixedMoment B node2889 node2889Labels := by
  calc
    mixedMoment B raw41088 raw41088Labels = mixedMoment B raw41088step0 raw41088step0Labels := by
      have hz : ∀ j, raw41088 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41088step0 = (fun i j => raw41088 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41088step0 raw41088; decide +kernel
      have hl : raw41088step0Labels = raw41088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41088 raw41088Labels permutation434 hz
    mixedMoment B raw41088step0 raw41088step0Labels = mixedMoment B raw41088step1 raw41088step1Labels := by
      have hz : ∀ j, raw41088step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41088step1 = (fun i j => raw41088step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41088step1 raw41088step0; decide +kernel
      have hl : raw41088step1Labels = raw41088step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41088step0 raw41088step0Labels permutation80 hz
    mixedMoment B raw41088step1 raw41088step1Labels = mixedMoment B raw41088step2 raw41088step2Labels := by
      have ha : raw41088step2 = (fun i j => raw41088step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41088step2 raw41088step1; decide +kernel
      have hl : raw41088step2Labels = raw41088step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41088step1 raw41088step1Labels permutation13 permutation6
    mixedMoment B raw41088step2 raw41088step2Labels = mixedMoment B raw41088step3 raw41088step3Labels := by
      have ha : raw41088step3 = -raw41088step2 := by apply Matrix.ext; change ∀ i j, raw41088step3 i j = -(raw41088step2 i j); unfold raw41088step3 raw41088step2; decide +kernel
      have hl : raw41088step3Labels = raw41088step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2889 node2889Labels := by rfl

def raw41089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw41089Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![2, 1, -3]]
def raw41089step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41089step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41089 raw41089Labels = mixedMoment B node2815 node2815Labels := by
  calc
    mixedMoment B raw41089 raw41089Labels = mixedMoment B raw41089step0 raw41089step0Labels := by
      have hz : ∀ j, raw41089 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41089step0 = (fun i j => raw41089 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41089step0 raw41089; decide +kernel
      have hl : raw41089step0Labels = raw41089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41089 raw41089Labels permutation346 hz
    mixedMoment B raw41089step0 raw41089step0Labels = mixedMoment B raw41089step1 raw41089step1Labels := by
      have ha : raw41089step1 = (fun i j => raw41089step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41089step1 raw41089step0; decide +kernel
      have hl : raw41089step1Labels = raw41089step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41089step0 raw41089step0Labels permutation137 permutation6
    _ = mixedMoment B node2815 node2815Labels := by rfl

def raw41090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw41090Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw41090step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw41090step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41090step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw41090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41090 raw41090Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw41090 raw41090Labels = mixedMoment B raw41090step0 raw41090step0Labels := by
      have hz : ∀ j, raw41090 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41090step0 = (fun i j => raw41090 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41090step0 raw41090; decide +kernel
      have hl : raw41090step0Labels = raw41090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41090 raw41090Labels permutation346 hz
    mixedMoment B raw41090step0 raw41090step0Labels = mixedMoment B raw41090step1 raw41090step1Labels := by
      have ha : raw41090step1 = (fun i j => raw41090step0 (permutation43 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41090step1 raw41090step0; decide +kernel
      have hl : raw41090step1Labels = raw41090step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41090step0 raw41090step0Labels permutation43 permutation6
    mixedMoment B raw41090step1 raw41090step1Labels = mixedMoment B raw41090step2 raw41090step2Labels := by
      have ha : raw41090step2 = -raw41090step1 := by apply Matrix.ext; change ∀ i j, raw41090step2 i j = -(raw41090step1 i j); unfold raw41090step2 raw41090step1; decide +kernel
      have hl : raw41090step2Labels = raw41090step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2931 node2931Labels := by rfl

def raw41091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw41091Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw41091step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw41091step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41091step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41091step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41091 raw41091Labels = mixedMoment B node2813 node2813Labels := by
  calc
    mixedMoment B raw41091 raw41091Labels = mixedMoment B raw41091step0 raw41091step0Labels := by
      have hz : ∀ j, raw41091 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41091step0 = (fun i j => raw41091 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41091step0 raw41091; decide +kernel
      have hl : raw41091step0Labels = raw41091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41091 raw41091Labels permutation346 hz
    mixedMoment B raw41091step0 raw41091step0Labels = mixedMoment B raw41091step1 raw41091step1Labels := by
      have ha : raw41091step1 = (fun i j => raw41091step0 (permutation43 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41091step1 raw41091step0; decide +kernel
      have hl : raw41091step1Labels = raw41091step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41091step0 raw41091step0Labels permutation43 permutation6
    mixedMoment B raw41091step1 raw41091step1Labels = mixedMoment B raw41091step2 raw41091step2Labels := by
      have ha : raw41091step2 = -raw41091step1 := by apply Matrix.ext; change ∀ i j, raw41091step2 i j = -(raw41091step1 i j); unfold raw41091step2 raw41091step1; decide +kernel
      have hl : raw41091step2Labels = raw41091step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2813 node2813Labels := by rfl

def raw41092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw41092Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41092step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw41092step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41092step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41092step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41092 raw41092Labels = mixedMoment B node2893 node2893Labels := by
  calc
    mixedMoment B raw41092 raw41092Labels = mixedMoment B raw41092step0 raw41092step0Labels := by
      have ha : raw41092step0 = (fun i j => raw41092 (permutation187 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41092step0 raw41092; decide +kernel
      have hl : raw41092step0Labels = raw41092Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41092 raw41092Labels permutation187 permutation6
    mixedMoment B raw41092step0 raw41092step0Labels = mixedMoment B raw41092step1 raw41092step1Labels := by
      have ha : raw41092step1 = -raw41092step0 := by apply Matrix.ext; change ∀ i j, raw41092step1 i j = -(raw41092step0 i j); unfold raw41092step1 raw41092step0; decide +kernel
      have hl : raw41092step1Labels = raw41092step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2893 node2893Labels := by rfl

def raw41093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw41093Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41093step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41093step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41093step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41093step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41093 raw41093Labels = mixedMoment B node2814 node2814Labels := by
  calc
    mixedMoment B raw41093 raw41093Labels = mixedMoment B raw41093step0 raw41093step0Labels := by
      have ha : raw41093step0 = (fun i j => raw41093 (permutation224 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41093step0 raw41093; decide +kernel
      have hl : raw41093step0Labels = raw41093Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41093 raw41093Labels permutation224 permutation6
    mixedMoment B raw41093step0 raw41093step0Labels = mixedMoment B raw41093step1 raw41093step1Labels := by
      have ha : raw41093step1 = -raw41093step0 := by apply Matrix.ext; change ∀ i j, raw41093step1 i j = -(raw41093step0 i j); unfold raw41093step1 raw41093step0; decide +kernel
      have hl : raw41093step1Labels = raw41093step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2814 node2814Labels := by rfl

def raw41094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 1, -3]]
def raw41094Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![2, 1, -3]]
def raw41094step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw41094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41094step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41094step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41094 raw41094Labels = mixedMoment B node2815 node2815Labels := by
  calc
    mixedMoment B raw41094 raw41094Labels = mixedMoment B raw41094step0 raw41094step0Labels := by
      have hz : ∀ j, raw41094 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41094step0 = (fun i j => raw41094 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41094step0 raw41094; decide +kernel
      have hl : raw41094step0Labels = raw41094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41094 raw41094Labels permutation434 hz
    mixedMoment B raw41094step0 raw41094step0Labels = mixedMoment B raw41094step1 raw41094step1Labels := by
      have ha : raw41094step1 = (fun i j => raw41094step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41094step1 raw41094step0; decide +kernel
      have hl : raw41094step1Labels = raw41094step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41094step0 raw41094step0Labels permutation44 permutation6
    mixedMoment B raw41094step1 raw41094step1Labels = mixedMoment B raw41094step2 raw41094step2Labels := by
      have ha : raw41094step2 = -raw41094step1 := by apply Matrix.ext; change ∀ i j, raw41094step2 i j = -(raw41094step1 i j); unfold raw41094step2 raw41094step1; decide +kernel
      have hl : raw41094step2Labels = raw41094step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2815 node2815Labels := by rfl

def raw41095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw41095Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41095step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41095step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41095step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41095 raw41095Labels = mixedMoment B node2809 node2809Labels := by
  calc
    mixedMoment B raw41095 raw41095Labels = mixedMoment B raw41095step0 raw41095step0Labels := by
      have ha : raw41095step0 = (fun i j => raw41095 (permutation218 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41095step0 raw41095; decide +kernel
      have hl : raw41095step0Labels = raw41095Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41095 raw41095Labels permutation218 permutation6
    mixedMoment B raw41095step0 raw41095step0Labels = mixedMoment B raw41095step1 raw41095step1Labels := by
      have ha : raw41095step1 = -raw41095step0 := by apply Matrix.ext; change ∀ i j, raw41095step1 i j = -(raw41095step0 i j); unfold raw41095step1 raw41095step0; decide +kernel
      have hl : raw41095step1Labels = raw41095step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2809 node2809Labels := by rfl

def raw41096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw41096Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 2, -4]]
def raw41096step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41096step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, -2, 2], ![2, 2, -4]]
def raw41096step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41096step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw41096step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41096 raw41096Labels = mixedMoment B node1145 node1145Labels := by
  calc
    mixedMoment B raw41096 raw41096Labels = mixedMoment B raw41096step0 raw41096step0Labels := by
      have hz : ∀ j, raw41096 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41096step0 = (fun i j => raw41096 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41096step0 raw41096; decide +kernel
      have hl : raw41096step0Labels = raw41096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41096 raw41096Labels permutation434 hz
    mixedMoment B raw41096step0 raw41096step0Labels = mixedMoment B raw41096step1 raw41096step1Labels := by
      have hz : ∀ j, raw41096step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41096step1 = (fun i j => raw41096step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41096step1 raw41096step0; decide +kernel
      have hl : raw41096step1Labels = raw41096step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41096step0 raw41096step0Labels permutation80 hz
    mixedMoment B raw41096step1 raw41096step1Labels = mixedMoment B raw41096step2 raw41096step2Labels := by
      have ha : raw41096step2 = (fun i j => raw41096step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41096step2 raw41096step1; decide +kernel
      have hl : raw41096step2Labels = raw41096step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41096step1 raw41096step1Labels permutation29 permutation6
    _ = mixedMoment B node1145 node1145Labels := by rfl

def raw41097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw41097Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -2, 1]]
def raw41097step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, 2, -3], ![1, -2, 1]]
def raw41097step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41097step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw41097step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41097 raw41097Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw41097 raw41097Labels = mixedMoment B raw41097step0 raw41097step0Labels := by
      have hz : ∀ j, raw41097 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41097step0 = (fun i j => raw41097 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41097step0 raw41097; decide +kernel
      have hl : raw41097step0Labels = raw41097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41097 raw41097Labels permutation434 hz
    mixedMoment B raw41097step0 raw41097step0Labels = mixedMoment B raw41097step1 raw41097step1Labels := by
      have hz : ∀ j, raw41097step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41097step1 = (fun i j => raw41097step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41097step1 raw41097step0; decide +kernel
      have hl : raw41097step1Labels = raw41097step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41097step0 raw41097step0Labels permutation80 hz
    mixedMoment B raw41097step1 raw41097step1Labels = mixedMoment B raw41097step2 raw41097step2Labels := by
      have ha : raw41097step2 = (fun i j => raw41097step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41097step2 raw41097step1; decide +kernel
      have hl : raw41097step2Labels = raw41097step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41097step1 raw41097step1Labels permutation23 permutation6
    _ = mixedMoment B node2519 node2519Labels := by rfl

def raw41098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw41098Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0]]
def raw41098step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41098step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41098 raw41098Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw41098 raw41098Labels = mixedMoment B raw41098step0 raw41098step0Labels := by
      have hz : ∀ j, raw41098 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41098step0 = (fun i j => raw41098 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41098step0 raw41098; decide +kernel
      have hl : raw41098step0Labels = raw41098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41098 raw41098Labels permutation346 hz
    mixedMoment B raw41098step0 raw41098step0Labels = mixedMoment B raw41098step1 raw41098step1Labels := by
      have ha : raw41098step1 = (fun i j => raw41098step0 (permutation115 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41098step1 raw41098step0; decide +kernel
      have hl : raw41098step1Labels = raw41098step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41098step0 raw41098step0Labels permutation115 permutation6
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw41099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw41099Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1]]
def raw41099step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw41099step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41099 raw41099Labels = mixedMoment B node2434 node2434Labels := by
  calc
    mixedMoment B raw41099 raw41099Labels = mixedMoment B raw41099step0 raw41099step0Labels := by
      have hz : ∀ j, raw41099 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41099step0 = (fun i j => raw41099 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41099step0 raw41099; decide +kernel
      have hl : raw41099step0Labels = raw41099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41099 raw41099Labels permutation346 hz
    mixedMoment B raw41099step0 raw41099step0Labels = mixedMoment B raw41099step1 raw41099step1Labels := by
      have ha : raw41099step1 = (fun i j => raw41099step0 (permutation115 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41099step1 raw41099step0; decide +kernel
      have hl : raw41099step1Labels = raw41099step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41099step0 raw41099step0Labels permutation115 permutation6
    _ = mixedMoment B node2434 node2434Labels := by rfl

def raw41100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw41100Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw41100step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw41100step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41100step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41100step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41100 raw41100Labels = mixedMoment B node2818 node2818Labels := by
  calc
    mixedMoment B raw41100 raw41100Labels = mixedMoment B raw41100step0 raw41100step0Labels := by
      have hz : ∀ j, raw41100 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41100step0 = (fun i j => raw41100 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41100step0 raw41100; decide +kernel
      have hl : raw41100step0Labels = raw41100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41100 raw41100Labels permutation346 hz
    mixedMoment B raw41100step0 raw41100step0Labels = mixedMoment B raw41100step1 raw41100step1Labels := by
      have ha : raw41100step1 = (fun i j => raw41100step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41100step1 raw41100step0; decide +kernel
      have hl : raw41100step1Labels = raw41100step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41100step0 raw41100step0Labels permutation38 permutation6
    mixedMoment B raw41100step1 raw41100step1Labels = mixedMoment B raw41100step2 raw41100step2Labels := by
      have ha : raw41100step2 = -raw41100step1 := by apply Matrix.ext; change ∀ i j, raw41100step2 i j = -(raw41100step1 i j); unfold raw41100step2 raw41100step1; decide +kernel
      have hl : raw41100step2Labels = raw41100step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2818 node2818Labels := by rfl

def raw41101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw41101Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41101 raw41101Labels = mixedMoment B node2429 node2429Labels := by
  calc
    mixedMoment B raw41101 raw41101Labels = mixedMoment B raw41101step0 raw41101step0Labels := by
      have ha : raw41101step0 = (fun i j => raw41101 (permutation540 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41101step0 raw41101; decide +kernel
      have hl : raw41101step0Labels = raw41101Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41101 raw41101Labels permutation540 permutation6
    _ = mixedMoment B node2429 node2429Labels := by rfl

def raw41102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 3, -5]]
def raw41102Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 3, -5]]
def raw41102step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41102step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -2, 2], ![2, 3, -5]]
def raw41102step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41102step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![2, 3, -5]]
def raw41102step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41102step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw41102step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41102 raw41102Labels = mixedMoment B node620 node620Labels := by
  calc
    mixedMoment B raw41102 raw41102Labels = mixedMoment B raw41102step0 raw41102step0Labels := by
      have hz : ∀ j, raw41102 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41102step0 = (fun i j => raw41102 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41102step0 raw41102; decide +kernel
      have hl : raw41102step0Labels = raw41102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41102 raw41102Labels permutation434 hz
    mixedMoment B raw41102step0 raw41102step0Labels = mixedMoment B raw41102step1 raw41102step1Labels := by
      have hz : ∀ j, raw41102step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41102step1 = (fun i j => raw41102step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41102step1 raw41102step0; decide +kernel
      have hl : raw41102step1Labels = raw41102step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41102step0 raw41102step0Labels permutation80 hz
    mixedMoment B raw41102step1 raw41102step1Labels = mixedMoment B raw41102step2 raw41102step2Labels := by
      have hz : ∀ j, raw41102step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41102step2 = (fun i j => raw41102step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41102step2 raw41102step1; decide +kernel
      have hl : raw41102step2Labels = raw41102step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41102step1 raw41102step1Labels permutation14 hz
    mixedMoment B raw41102step2 raw41102step2Labels = mixedMoment B raw41102step3 raw41102step3Labels := by
      have ha : raw41102step3 = (fun i j => raw41102step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41102step3 raw41102step2; decide +kernel
      have hl : raw41102step3Labels = raw41102step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41102step2 raw41102step2Labels permutation7 permutation6
    _ = mixedMoment B node620 node620Labels := by rfl

def raw41103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -2, 1]]
def raw41103Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -2, 1]]
def raw41103step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41103step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![1, 3, -4], ![1, -2, 1]]
def raw41103step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41103step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, 3, -4], ![1, -2, 1]]
def raw41103step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41103step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw41103step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41103 raw41103Labels = mixedMoment B node1091 node1091Labels := by
  calc
    mixedMoment B raw41103 raw41103Labels = mixedMoment B raw41103step0 raw41103step0Labels := by
      have hz : ∀ j, raw41103 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41103step0 = (fun i j => raw41103 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41103step0 raw41103; decide +kernel
      have hl : raw41103step0Labels = raw41103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41103 raw41103Labels permutation434 hz
    mixedMoment B raw41103step0 raw41103step0Labels = mixedMoment B raw41103step1 raw41103step1Labels := by
      have hz : ∀ j, raw41103step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41103step1 = (fun i j => raw41103step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41103step1 raw41103step0; decide +kernel
      have hl : raw41103step1Labels = raw41103step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41103step0 raw41103step0Labels permutation80 hz
    mixedMoment B raw41103step1 raw41103step1Labels = mixedMoment B raw41103step2 raw41103step2Labels := by
      have hz : ∀ j, raw41103step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41103step2 = (fun i j => raw41103step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41103step2 raw41103step1; decide +kernel
      have hl : raw41103step2Labels = raw41103step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41103step1 raw41103step1Labels permutation14 hz
    mixedMoment B raw41103step2 raw41103step2Labels = mixedMoment B raw41103step3 raw41103step3Labels := by
      have ha : raw41103step3 = (fun i j => raw41103step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41103step3 raw41103step2; decide +kernel
      have hl : raw41103step3Labels = raw41103step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41103step2 raw41103step2Labels permutation5 permutation6
    _ = mixedMoment B node1091 node1091Labels := by rfl

def raw41104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]
def raw41104Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]
def raw41104step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![2, 3, -5]]
def raw41104step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41104step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41104step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41104 raw41104Labels = mixedMoment B node611 node611Labels := by
  calc
    mixedMoment B raw41104 raw41104Labels = mixedMoment B raw41104step0 raw41104step0Labels := by
      have hz : ∀ j, raw41104 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41104step0 = (fun i j => raw41104 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41104step0 raw41104; decide +kernel
      have hl : raw41104step0Labels = raw41104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41104 raw41104Labels permutation346 hz
    mixedMoment B raw41104step0 raw41104step0Labels = mixedMoment B raw41104step1 raw41104step1Labels := by
      have hz : ∀ j, raw41104step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41104step1 = (fun i j => raw41104step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41104step1 raw41104step0; decide +kernel
      have hl : raw41104step1Labels = raw41104step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41104step0 raw41104step0Labels permutation56 hz
    mixedMoment B raw41104step1 raw41104step1Labels = mixedMoment B raw41104step2 raw41104step2Labels := by
      have ha : raw41104step2 = (fun i j => raw41104step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41104step2 raw41104step1; decide +kernel
      have hl : raw41104step2Labels = raw41104step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41104step1 raw41104step1Labels permutation29 permutation6
    _ = mixedMoment B node611 node611Labels := by rfl

def raw41105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw41105Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw41105step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 3, -4], ![1, -1, 0]]
def raw41105step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41105step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41105 raw41105Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw41105 raw41105Labels = mixedMoment B raw41105step0 raw41105step0Labels := by
      have hz : ∀ j, raw41105 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41105step0 = (fun i j => raw41105 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41105step0 raw41105; decide +kernel
      have hl : raw41105step0Labels = raw41105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41105 raw41105Labels permutation346 hz
    mixedMoment B raw41105step0 raw41105step0Labels = mixedMoment B raw41105step1 raw41105step1Labels := by
      have hz : ∀ j, raw41105step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41105step1 = (fun i j => raw41105step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41105step1 raw41105step0; decide +kernel
      have hl : raw41105step1Labels = raw41105step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41105step0 raw41105step0Labels permutation56 hz
    mixedMoment B raw41105step1 raw41105step1Labels = mixedMoment B raw41105step2 raw41105step2Labels := by
      have ha : raw41105step2 = (fun i j => raw41105step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41105step2 raw41105step1; decide +kernel
      have hl : raw41105step2Labels = raw41105step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41105step1 raw41105step1Labels permutation25 permutation6
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw41106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]
def raw41106Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]
def raw41106step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41106step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 3, -4], ![1, 0, -1]]
def raw41106step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41106step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw41106step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41106 raw41106Labels = mixedMoment B node939 node939Labels := by
  calc
    mixedMoment B raw41106 raw41106Labels = mixedMoment B raw41106step0 raw41106step0Labels := by
      have hz : ∀ j, raw41106 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41106step0 = (fun i j => raw41106 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41106step0 raw41106; decide +kernel
      have hl : raw41106step0Labels = raw41106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41106 raw41106Labels permutation346 hz
    mixedMoment B raw41106step0 raw41106step0Labels = mixedMoment B raw41106step1 raw41106step1Labels := by
      have hz : ∀ j, raw41106step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41106step1 = (fun i j => raw41106step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41106step1 raw41106step0; decide +kernel
      have hl : raw41106step1Labels = raw41106step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41106step0 raw41106step0Labels permutation56 hz
    mixedMoment B raw41106step1 raw41106step1Labels = mixedMoment B raw41106step2 raw41106step2Labels := by
      have ha : raw41106step2 = (fun i j => raw41106step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41106step2 raw41106step1; decide +kernel
      have hl : raw41106step2Labels = raw41106step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41106step1 raw41106step1Labels permutation25 permutation6
    _ = mixedMoment B node939 node939Labels := by rfl

def raw41107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2]]
def raw41107Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2]]
def raw41107step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41107step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![1, 2, -3], ![1, 1, -2]]
def raw41107step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41107step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw41107step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41107 raw41107Labels = mixedMoment B node2345 node2345Labels := by
  calc
    mixedMoment B raw41107 raw41107Labels = mixedMoment B raw41107step0 raw41107step0Labels := by
      have hz : ∀ j, raw41107 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41107step0 = (fun i j => raw41107 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41107step0 raw41107; decide +kernel
      have hl : raw41107step0Labels = raw41107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41107 raw41107Labels permutation346 hz
    mixedMoment B raw41107step0 raw41107step0Labels = mixedMoment B raw41107step1 raw41107step1Labels := by
      have hz : ∀ j, raw41107step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41107step1 = (fun i j => raw41107step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41107step1 raw41107step0; decide +kernel
      have hl : raw41107step1Labels = raw41107step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41107step0 raw41107step0Labels permutation56 hz
    mixedMoment B raw41107step1 raw41107step1Labels = mixedMoment B raw41107step2 raw41107step2Labels := by
      have ha : raw41107step2 = (fun i j => raw41107step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41107step2 raw41107step1; decide +kernel
      have hl : raw41107step2Labels = raw41107step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41107step1 raw41107step1Labels permutation25 permutation6
    _ = mixedMoment B node2345 node2345Labels := by rfl

def raw41108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw41108Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw41108step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41108step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41108 raw41108Labels = mixedMoment B node930 node930Labels := by
  calc
    mixedMoment B raw41108 raw41108Labels = mixedMoment B raw41108step0 raw41108step0Labels := by
      have hz : ∀ j, raw41108 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41108step0 = (fun i j => raw41108 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41108step0 raw41108; decide +kernel
      have hl : raw41108step0Labels = raw41108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41108 raw41108Labels permutation265 hz
    mixedMoment B raw41108step0 raw41108step0Labels = mixedMoment B raw41108step1 raw41108step1Labels := by
      have ha : raw41108step1 = (fun i j => raw41108step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41108step1 raw41108step0; decide +kernel
      have hl : raw41108step1Labels = raw41108step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41108step0 raw41108step0Labels permutation125 permutation6
    _ = mixedMoment B node930 node930Labels := by rfl

def raw41109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2]]
def raw41109Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2]]
def raw41109step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41109 raw41109Labels = mixedMoment B node2339 node2339Labels := by
  calc
    mixedMoment B raw41109 raw41109Labels = mixedMoment B raw41109step0 raw41109step0Labels := by
      have hz : ∀ j, raw41109 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41109step0 = (fun i j => raw41109 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41109step0 raw41109; decide +kernel
      have hl : raw41109step0Labels = raw41109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41109 raw41109Labels permutation265 hz
    mixedMoment B raw41109step0 raw41109step0Labels = mixedMoment B raw41109step1 raw41109step1Labels := by
      have ha : raw41109step1 = (fun i j => raw41109step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41109step1 raw41109step0; decide +kernel
      have hl : raw41109step1Labels = raw41109step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41109step0 raw41109step0Labels permutation125 permutation6
    _ = mixedMoment B node2339 node2339Labels := by rfl

def raw41110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw41110Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw41110step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![3, -1, -2]]
def raw41110step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41110step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![3, -1, -2]]
def raw41110step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41110step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-2, 3, -1], ![-2, -1, 3]]
def raw41110step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41110step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw41110step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41110 raw41110Labels = mixedMoment B node1310 node1310Labels := by
  calc
    mixedMoment B raw41110 raw41110Labels = mixedMoment B raw41110step0 raw41110step0Labels := by
      have hz : ∀ j, raw41110 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41110step0 = (fun i j => raw41110 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41110step0 raw41110; decide +kernel
      have hl : raw41110step0Labels = raw41110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41110 raw41110Labels permutation520 hz
    mixedMoment B raw41110step0 raw41110step0Labels = mixedMoment B raw41110step1 raw41110step1Labels := by
      have hz : ∀ j, raw41110step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41110step1 = (fun i j => raw41110step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41110step1 raw41110step0; decide +kernel
      have hl : raw41110step1Labels = raw41110step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41110step0 raw41110step0Labels permutation104 hz
    mixedMoment B raw41110step1 raw41110step1Labels = mixedMoment B raw41110step2 raw41110step2Labels := by
      have hz : ∀ j, raw41110step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41110step2 = (fun i j => raw41110step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41110step2 raw41110step1; decide +kernel
      have hl : raw41110step2Labels = raw41110step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41110step1 raw41110step1Labels permutation20 hz
    mixedMoment B raw41110step2 raw41110step2Labels = mixedMoment B raw41110step3 raw41110step3Labels := by
      have ha : raw41110step3 = (fun i j => raw41110step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41110step3 raw41110step2; decide +kernel
      have hl : raw41110step3Labels = raw41110step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41110step2 raw41110step2Labels permutation3 permutation6
    mixedMoment B raw41110step3 raw41110step3Labels = mixedMoment B raw41110step4 raw41110step4Labels := by
      have ha : raw41110step4 = -raw41110step3 := by apply Matrix.ext; change ∀ i j, raw41110step4 i j = -(raw41110step3 i j); unfold raw41110step4 raw41110step3; decide +kernel
      have hl : raw41110step4Labels = raw41110step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1310 node1310Labels := by rfl

def raw41111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41111Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41111step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41111step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 3, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41111step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41111step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw41111step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41111step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw41111step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41111 raw41111Labels = mixedMoment B node1245 node1245Labels := by
  calc
    mixedMoment B raw41111 raw41111Labels = mixedMoment B raw41111step0 raw41111step0Labels := by
      have hz : ∀ j, raw41111 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41111step0 = (fun i j => raw41111 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41111step0 raw41111; decide +kernel
      have hl : raw41111step0Labels = raw41111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41111 raw41111Labels permutation434 hz
    mixedMoment B raw41111step0 raw41111step0Labels = mixedMoment B raw41111step1 raw41111step1Labels := by
      have hz : ∀ j, raw41111step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41111step1 = (fun i j => raw41111step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41111step1 raw41111step0; decide +kernel
      have hl : raw41111step1Labels = raw41111step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41111step0 raw41111step0Labels permutation80 hz
    mixedMoment B raw41111step1 raw41111step1Labels = mixedMoment B raw41111step2 raw41111step2Labels := by
      have ha : raw41111step2 = (fun i j => raw41111step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41111step2 raw41111step1; decide +kernel
      have hl : raw41111step2Labels = raw41111step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41111step1 raw41111step1Labels permutation11 permutation6
    mixedMoment B raw41111step2 raw41111step2Labels = mixedMoment B raw41111step3 raw41111step3Labels := by
      have ha : raw41111step3 = -raw41111step2 := by apply Matrix.ext; change ∀ i j, raw41111step3 i j = -(raw41111step2 i j); unfold raw41111step3 raw41111step2; decide +kernel
      have hl : raw41111step3Labels = raw41111step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1245 node1245Labels := by rfl

def raw41112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw41112Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw41112step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41112step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![3, -1, -2]]
def raw41112step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41112step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw41112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41112step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41112step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41112 raw41112Labels = mixedMoment B node1306 node1306Labels := by
  calc
    mixedMoment B raw41112 raw41112Labels = mixedMoment B raw41112step0 raw41112step0Labels := by
      have hz : ∀ j, raw41112 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41112step0 = (fun i j => raw41112 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41112step0 raw41112; decide +kernel
      have hl : raw41112step0Labels = raw41112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41112 raw41112Labels permutation520 hz
    mixedMoment B raw41112step0 raw41112step0Labels = mixedMoment B raw41112step1 raw41112step1Labels := by
      have hz : ∀ j, raw41112step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41112step1 = (fun i j => raw41112step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41112step1 raw41112step0; decide +kernel
      have hl : raw41112step1Labels = raw41112step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41112step0 raw41112step0Labels permutation104 hz
    mixedMoment B raw41112step1 raw41112step1Labels = mixedMoment B raw41112step2 raw41112step2Labels := by
      have ha : raw41112step2 = (fun i j => raw41112step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41112step2 raw41112step1; decide +kernel
      have hl : raw41112step2Labels = raw41112step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41112step1 raw41112step1Labels permutation10 permutation6
    mixedMoment B raw41112step2 raw41112step2Labels = mixedMoment B raw41112step3 raw41112step3Labels := by
      have ha : raw41112step3 = -raw41112step2 := by apply Matrix.ext; change ∀ i j, raw41112step3 i j = -(raw41112step2 i j); unfold raw41112step3 raw41112step2; decide +kernel
      have hl : raw41112step3Labels = raw41112step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1306 node1306Labels := by rfl

def raw41113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41113Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41113step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41113step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41113step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41113 raw41113Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw41113 raw41113Labels = mixedMoment B raw41113step0 raw41113step0Labels := by
      have hz : ∀ j, raw41113 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41113step0 = (fun i j => raw41113 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41113step0 raw41113; decide +kernel
      have hl : raw41113step0Labels = raw41113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41113 raw41113Labels permutation434 hz
    mixedMoment B raw41113step0 raw41113step0Labels = mixedMoment B raw41113step1 raw41113step1Labels := by
      have ha : raw41113step1 = (fun i j => raw41113step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41113step1 raw41113step0; decide +kernel
      have hl : raw41113step1Labels = raw41113step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41113step0 raw41113step0Labels permutation55 permutation6
    mixedMoment B raw41113step1 raw41113step1Labels = mixedMoment B raw41113step2 raw41113step2Labels := by
      have ha : raw41113step2 = -raw41113step1 := by apply Matrix.ext; change ∀ i j, raw41113step2 i j = -(raw41113step1 i j); unfold raw41113step2 raw41113step1; decide +kernel
      have hl : raw41113step2Labels = raw41113step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1291 node1291Labels := by rfl

def raw41114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41114Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41114step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw41114step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41114step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41114step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41114 raw41114Labels = mixedMoment B node1241 node1241Labels := by
  calc
    mixedMoment B raw41114 raw41114Labels = mixedMoment B raw41114step0 raw41114step0Labels := by
      have hz : ∀ j, raw41114 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41114step0 = (fun i j => raw41114 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41114step0 raw41114; decide +kernel
      have hl : raw41114step0Labels = raw41114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41114 raw41114Labels permutation434 hz
    mixedMoment B raw41114step0 raw41114step0Labels = mixedMoment B raw41114step1 raw41114step1Labels := by
      have ha : raw41114step1 = (fun i j => raw41114step0 (permutation46 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41114step1 raw41114step0; decide +kernel
      have hl : raw41114step1Labels = raw41114step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41114step0 raw41114step0Labels permutation46 permutation6
    mixedMoment B raw41114step1 raw41114step1Labels = mixedMoment B raw41114step2 raw41114step2Labels := by
      have ha : raw41114step2 = -raw41114step1 := by apply Matrix.ext; change ∀ i j, raw41114step2 i j = -(raw41114step1 i j); unfold raw41114step2 raw41114step1; decide +kernel
      have hl : raw41114step2Labels = raw41114step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1241 node1241Labels := by rfl

def raw41115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41115Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41115step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41115step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41115 raw41115Labels = mixedMoment B node1233 node1233Labels := by
  calc
    mixedMoment B raw41115 raw41115Labels = mixedMoment B raw41115step0 raw41115step0Labels := by
      have ha : raw41115step0 = (fun i j => raw41115 (permutation259 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41115step0 raw41115; decide +kernel
      have hl : raw41115step0Labels = raw41115Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41115 raw41115Labels permutation259 permutation6
    mixedMoment B raw41115step0 raw41115step0Labels = mixedMoment B raw41115step1 raw41115step1Labels := by
      have ha : raw41115step1 = -raw41115step0 := by apply Matrix.ext; change ∀ i j, raw41115step1 i j = -(raw41115step0 i j); unfold raw41115step1 raw41115step0; decide +kernel
      have hl : raw41115step1Labels = raw41115step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1233 node1233Labels := by rfl

def raw41116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41116Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41116step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41116step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def raw41116step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41116step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw41116step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41116step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41116step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41116 raw41116Labels = mixedMoment B node1295 node1295Labels := by
  calc
    mixedMoment B raw41116 raw41116Labels = mixedMoment B raw41116step0 raw41116step0Labels := by
      have hz : ∀ j, raw41116 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41116step0 = (fun i j => raw41116 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41116step0 raw41116; decide +kernel
      have hl : raw41116step0Labels = raw41116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41116 raw41116Labels permutation434 hz
    mixedMoment B raw41116step0 raw41116step0Labels = mixedMoment B raw41116step1 raw41116step1Labels := by
      have hz : ∀ j, raw41116step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41116step1 = (fun i j => raw41116step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41116step1 raw41116step0; decide +kernel
      have hl : raw41116step1Labels = raw41116step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41116step0 raw41116step0Labels permutation80 hz
    mixedMoment B raw41116step1 raw41116step1Labels = mixedMoment B raw41116step2 raw41116step2Labels := by
      have ha : raw41116step2 = (fun i j => raw41116step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41116step2 raw41116step1; decide +kernel
      have hl : raw41116step2Labels = raw41116step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41116step1 raw41116step1Labels permutation12 permutation6
    mixedMoment B raw41116step2 raw41116step2Labels = mixedMoment B raw41116step3 raw41116step3Labels := by
      have ha : raw41116step3 = -raw41116step2 := by apply Matrix.ext; change ∀ i j, raw41116step3 i j = -(raw41116step2 i j); unfold raw41116step3 raw41116step2; decide +kernel
      have hl : raw41116step3Labels = raw41116step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1295 node1295Labels := by rfl

def raw41117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41117Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41117step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41117step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, -1, 0], ![2, 1, -3]]
def raw41117step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41117step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw41117step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41117step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw41117step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41117 raw41117Labels = mixedMoment B node1243 node1243Labels := by
  calc
    mixedMoment B raw41117 raw41117Labels = mixedMoment B raw41117step0 raw41117step0Labels := by
      have hz : ∀ j, raw41117 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41117step0 = (fun i j => raw41117 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41117step0 raw41117; decide +kernel
      have hl : raw41117step0Labels = raw41117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41117 raw41117Labels permutation434 hz
    mixedMoment B raw41117step0 raw41117step0Labels = mixedMoment B raw41117step1 raw41117step1Labels := by
      have hz : ∀ j, raw41117step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41117step1 = (fun i j => raw41117step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41117step1 raw41117step0; decide +kernel
      have hl : raw41117step1Labels = raw41117step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41117step0 raw41117step0Labels permutation80 hz
    mixedMoment B raw41117step1 raw41117step1Labels = mixedMoment B raw41117step2 raw41117step2Labels := by
      have ha : raw41117step2 = (fun i j => raw41117step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41117step2 raw41117step1; decide +kernel
      have hl : raw41117step2Labels = raw41117step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41117step1 raw41117step1Labels permutation10 permutation6
    mixedMoment B raw41117step2 raw41117step2Labels = mixedMoment B raw41117step3 raw41117step3Labels := by
      have ha : raw41117step3 = -raw41117step2 := by apply Matrix.ext; change ∀ i j, raw41117step3 i j = -(raw41117step2 i j); unfold raw41117step3 raw41117step2; decide +kernel
      have hl : raw41117step3Labels = raw41117step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1243 node1243Labels := by rfl

def raw41118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41118Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41118step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw41118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41118step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41118 raw41118Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw41118 raw41118Labels = mixedMoment B raw41118step0 raw41118step0Labels := by
      have hz : ∀ j, raw41118 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41118step0 = (fun i j => raw41118 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41118step0 raw41118; decide +kernel
      have hl : raw41118step0Labels = raw41118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41118 raw41118Labels permutation346 hz
    mixedMoment B raw41118step0 raw41118step0Labels = mixedMoment B raw41118step1 raw41118step1Labels := by
      have ha : raw41118step1 = (fun i j => raw41118step0 (permutation54 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41118step1 raw41118step0; decide +kernel
      have hl : raw41118step1Labels = raw41118step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41118step0 raw41118step0Labels permutation54 permutation6
    mixedMoment B raw41118step1 raw41118step1Labels = mixedMoment B raw41118step2 raw41118step2Labels := by
      have ha : raw41118step2 = -raw41118step1 := by apply Matrix.ext; change ∀ i j, raw41118step2 i j = -(raw41118step1 i j); unfold raw41118step2 raw41118step1; decide +kernel
      have hl : raw41118step2Labels = raw41118step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1237 node1237Labels := by rfl

def raw41119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw41119Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![3, -1, -2]]
def raw41119step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![3, -1, -2]]
def raw41119step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41119step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw41119step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41119step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw41119step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41119 raw41119Labels = mixedMoment B node1273 node1273Labels := by
  calc
    mixedMoment B raw41119 raw41119Labels = mixedMoment B raw41119step0 raw41119step0Labels := by
      have hz : ∀ j, raw41119 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41119step0 = (fun i j => raw41119 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41119step0 raw41119; decide +kernel
      have hl : raw41119step0Labels = raw41119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41119 raw41119Labels permutation520 hz
    mixedMoment B raw41119step0 raw41119step0Labels = mixedMoment B raw41119step1 raw41119step1Labels := by
      have hz : ∀ j, raw41119step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41119step1 = (fun i j => raw41119step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41119step1 raw41119step0; decide +kernel
      have hl : raw41119step1Labels = raw41119step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41119step0 raw41119step0Labels permutation104 hz
    mixedMoment B raw41119step1 raw41119step1Labels = mixedMoment B raw41119step2 raw41119step2Labels := by
      have ha : raw41119step2 = (fun i j => raw41119step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41119step2 raw41119step1; decide +kernel
      have hl : raw41119step2Labels = raw41119step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41119step1 raw41119step1Labels permutation9 permutation6
    mixedMoment B raw41119step2 raw41119step2Labels = mixedMoment B raw41119step3 raw41119step3Labels := by
      have ha : raw41119step3 = -raw41119step2 := by apply Matrix.ext; change ∀ i j, raw41119step3 i j = -(raw41119step2 i j); unfold raw41119step3 raw41119step2; decide +kernel
      have hl : raw41119step3Labels = raw41119step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1273 node1273Labels := by rfl

def raw41120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41120Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw41120step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw41120step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41120step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41120step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41120 raw41120Labels = mixedMoment B node1261 node1261Labels := by
  calc
    mixedMoment B raw41120 raw41120Labels = mixedMoment B raw41120step0 raw41120step0Labels := by
      have hz : ∀ j, raw41120 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41120step0 = (fun i j => raw41120 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41120step0 raw41120; decide +kernel
      have hl : raw41120step0Labels = raw41120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41120 raw41120Labels permutation434 hz
    mixedMoment B raw41120step0 raw41120step0Labels = mixedMoment B raw41120step1 raw41120step1Labels := by
      have ha : raw41120step1 = (fun i j => raw41120step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41120step1 raw41120step0; decide +kernel
      have hl : raw41120step1Labels = raw41120step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41120step0 raw41120step0Labels permutation37 permutation6
    mixedMoment B raw41120step1 raw41120step1Labels = mixedMoment B raw41120step2 raw41120step2Labels := by
      have ha : raw41120step2 = -raw41120step1 := by apply Matrix.ext; change ∀ i j, raw41120step2 i j = -(raw41120step1 i j); unfold raw41120step2 raw41120step1; decide +kernel
      have hl : raw41120step2Labels = raw41120step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1261 node1261Labels := by rfl

def raw41121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41121Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw41121step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41121step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41121step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41121 raw41121Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw41121 raw41121Labels = mixedMoment B raw41121step0 raw41121step0Labels := by
      have hz : ∀ j, raw41121 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41121step0 = (fun i j => raw41121 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41121step0 raw41121; decide +kernel
      have hl : raw41121step0Labels = raw41121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41121 raw41121Labels permutation434 hz
    mixedMoment B raw41121step0 raw41121step0Labels = mixedMoment B raw41121step1 raw41121step1Labels := by
      have ha : raw41121step1 = (fun i j => raw41121step0 (permutation45 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41121step1 raw41121step0; decide +kernel
      have hl : raw41121step1Labels = raw41121step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41121step0 raw41121step0Labels permutation45 permutation6
    mixedMoment B raw41121step1 raw41121step1Labels = mixedMoment B raw41121step2 raw41121step2Labels := by
      have ha : raw41121step2 = -raw41121step1 := by apply Matrix.ext; change ∀ i j, raw41121step2 i j = -(raw41121step1 i j); unfold raw41121step2 raw41121step1; decide +kernel
      have hl : raw41121step2Labels = raw41121step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1219 node1219Labels := by rfl

def raw41122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41122Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw41122step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41122step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41122 raw41122Labels = mixedMoment B node1212 node1212Labels := by
  calc
    mixedMoment B raw41122 raw41122Labels = mixedMoment B raw41122step0 raw41122step0Labels := by
      have ha : raw41122step0 = (fun i j => raw41122 (permutation249 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41122step0 raw41122; decide +kernel
      have hl : raw41122step0Labels = raw41122Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41122 raw41122Labels permutation249 permutation6
    mixedMoment B raw41122step0 raw41122step0Labels = mixedMoment B raw41122step1 raw41122step1Labels := by
      have ha : raw41122step1 = -raw41122step0 := by apply Matrix.ext; change ∀ i j, raw41122step1 i j = -(raw41122step0 i j); unfold raw41122step1 raw41122step0; decide +kernel
      have hl : raw41122step1Labels = raw41122step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1212 node1212Labels := by rfl

def raw41123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw41123Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw41123step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw41123step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41123step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41123 raw41123Labels = mixedMoment B node1270 node1270Labels := by
  calc
    mixedMoment B raw41123 raw41123Labels = mixedMoment B raw41123step0 raw41123step0Labels := by
      have hz : ∀ j, raw41123 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41123step0 = (fun i j => raw41123 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41123step0 raw41123; decide +kernel
      have hl : raw41123step0Labels = raw41123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41123 raw41123Labels permutation520 hz
    mixedMoment B raw41123step0 raw41123step0Labels = mixedMoment B raw41123step1 raw41123step1Labels := by
      have ha : raw41123step1 = (fun i j => raw41123step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41123step1 raw41123step0; decide +kernel
      have hl : raw41123step1Labels = raw41123step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41123step0 raw41123step0Labels permutation32 permutation6
    mixedMoment B raw41123step1 raw41123step1Labels = mixedMoment B raw41123step2 raw41123step2Labels := by
      have ha : raw41123step2 = -raw41123step1 := by apply Matrix.ext; change ∀ i j, raw41123step2 i j = -(raw41123step1 i j); unfold raw41123step2 raw41123step1; decide +kernel
      have hl : raw41123step2Labels = raw41123step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1270 node1270Labels := by rfl

def raw41124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41124Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw41124step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw41124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41124step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41124 raw41124Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw41124 raw41124Labels = mixedMoment B raw41124step0 raw41124step0Labels := by
      have hz : ∀ j, raw41124 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41124step0 = (fun i j => raw41124 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41124step0 raw41124; decide +kernel
      have hl : raw41124step0Labels = raw41124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41124 raw41124Labels permutation434 hz
    mixedMoment B raw41124step0 raw41124step0Labels = mixedMoment B raw41124step1 raw41124step1Labels := by
      have ha : raw41124step1 = (fun i j => raw41124step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41124step1 raw41124step0; decide +kernel
      have hl : raw41124step1Labels = raw41124step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41124step0 raw41124step0Labels permutation44 permutation6
    mixedMoment B raw41124step1 raw41124step1Labels = mixedMoment B raw41124step2 raw41124step2Labels := by
      have ha : raw41124step2 = -raw41124step1 := by apply Matrix.ext; change ∀ i j, raw41124step2 i j = -(raw41124step1 i j); unfold raw41124step2 raw41124step1; decide +kernel
      have hl : raw41124step2Labels = raw41124step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1217 node1217Labels := by rfl

def raw41125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -1, -1]]
def raw41125Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![2, -1, -1]]
def raw41125step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41125step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw41125step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41125step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw41125step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41125step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw41125step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41125 raw41125Labels = mixedMoment B node1264 node1264Labels := by
  calc
    mixedMoment B raw41125 raw41125Labels = mixedMoment B raw41125step0 raw41125step0Labels := by
      have hz : ∀ j, raw41125 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41125step0 = (fun i j => raw41125 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41125step0 raw41125; decide +kernel
      have hl : raw41125step0Labels = raw41125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41125 raw41125Labels permutation434 hz
    mixedMoment B raw41125step0 raw41125step0Labels = mixedMoment B raw41125step1 raw41125step1Labels := by
      have hz : ∀ j, raw41125step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41125step1 = (fun i j => raw41125step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41125step1 raw41125step0; decide +kernel
      have hl : raw41125step1Labels = raw41125step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41125step0 raw41125step0Labels permutation80 hz
    mixedMoment B raw41125step1 raw41125step1Labels = mixedMoment B raw41125step2 raw41125step2Labels := by
      have ha : raw41125step2 = (fun i j => raw41125step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41125step2 raw41125step1; decide +kernel
      have hl : raw41125step2Labels = raw41125step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41125step1 raw41125step1Labels permutation9 permutation6
    mixedMoment B raw41125step2 raw41125step2Labels = mixedMoment B raw41125step3 raw41125step3Labels := by
      have ha : raw41125step3 = -raw41125step2 := by apply Matrix.ext; change ∀ i j, raw41125step3 i j = -(raw41125step2 i j); unfold raw41125step3 raw41125step2; decide +kernel
      have hl : raw41125step3Labels = raw41125step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1264 node1264Labels := by rfl

def raw41126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw41126Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw41126step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41126step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw41126step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41126step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw41126step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41126 raw41126Labels = mixedMoment B node1221 node1221Labels := by
  calc
    mixedMoment B raw41126 raw41126Labels = mixedMoment B raw41126step0 raw41126step0Labels := by
      have hz : ∀ j, raw41126 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41126step0 = (fun i j => raw41126 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41126step0 raw41126; decide +kernel
      have hl : raw41126step0Labels = raw41126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41126 raw41126Labels permutation434 hz
    mixedMoment B raw41126step0 raw41126step0Labels = mixedMoment B raw41126step1 raw41126step1Labels := by
      have hz : ∀ j, raw41126step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41126step1 = (fun i j => raw41126step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41126step1 raw41126step0; decide +kernel
      have hl : raw41126step1Labels = raw41126step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41126step0 raw41126step0Labels permutation80 hz
    mixedMoment B raw41126step1 raw41126step1Labels = mixedMoment B raw41126step2 raw41126step2Labels := by
      have ha : raw41126step2 = (fun i j => raw41126step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41126step2 raw41126step1; decide +kernel
      have hl : raw41126step2Labels = raw41126step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41126step1 raw41126step1Labels permutation29 permutation6
    _ = mixedMoment B node1221 node1221Labels := by rfl

def raw41127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41127Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41127step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw41127step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw41127step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41127 raw41127Labels = mixedMoment B node1215 node1215Labels := by
  calc
    mixedMoment B raw41127 raw41127Labels = mixedMoment B raw41127step0 raw41127step0Labels := by
      have hz : ∀ j, raw41127 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41127step0 = (fun i j => raw41127 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41127step0 raw41127; decide +kernel
      have hl : raw41127step0Labels = raw41127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41127 raw41127Labels permutation346 hz
    mixedMoment B raw41127step0 raw41127step0Labels = mixedMoment B raw41127step1 raw41127step1Labels := by
      have ha : raw41127step1 = (fun i j => raw41127step0 (permutation51 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41127step1 raw41127step0; decide +kernel
      have hl : raw41127step1Labels = raw41127step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41127step0 raw41127step0Labels permutation51 permutation6
    mixedMoment B raw41127step1 raw41127step1Labels = mixedMoment B raw41127step2 raw41127step2Labels := by
      have ha : raw41127step2 = -raw41127step1 := by apply Matrix.ext; change ∀ i j, raw41127step2 i j = -(raw41127step1 i j); unfold raw41127step2 raw41127step1; decide +kernel
      have hl : raw41127step2Labels = raw41127step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1215 node1215Labels := by rfl

def raw41128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw41128Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![3, -1, -2]]
def raw41128step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![3, -1, -2]]
def raw41128step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41128step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![-2, 3, -1], ![-3, 0, 3]]
def raw41128step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41128step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -3, 1], ![3, 0, -3]]
def raw41128step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41128 raw41128Labels = mixedMoment B node1174 node1174Labels := by
  calc
    mixedMoment B raw41128 raw41128Labels = mixedMoment B raw41128step0 raw41128step0Labels := by
      have hz : ∀ j, raw41128 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41128step0 = (fun i j => raw41128 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41128step0 raw41128; decide +kernel
      have hl : raw41128step0Labels = raw41128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41128 raw41128Labels permutation520 hz
    mixedMoment B raw41128step0 raw41128step0Labels = mixedMoment B raw41128step1 raw41128step1Labels := by
      have hz : ∀ j, raw41128step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41128step1 = (fun i j => raw41128step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41128step1 raw41128step0; decide +kernel
      have hl : raw41128step1Labels = raw41128step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41128step0 raw41128step0Labels permutation104 hz
    mixedMoment B raw41128step1 raw41128step1Labels = mixedMoment B raw41128step2 raw41128step2Labels := by
      have ha : raw41128step2 = (fun i j => raw41128step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41128step2 raw41128step1; decide +kernel
      have hl : raw41128step2Labels = raw41128step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41128step1 raw41128step1Labels permutation9 permutation6
    mixedMoment B raw41128step2 raw41128step2Labels = mixedMoment B raw41128step3 raw41128step3Labels := by
      have ha : raw41128step3 = -raw41128step2 := by apply Matrix.ext; change ∀ i j, raw41128step3 i j = -(raw41128step2 i j); unfold raw41128step3 raw41128step2; decide +kernel
      have hl : raw41128step3Labels = raw41128step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1174 node1174Labels := by rfl

def raw41129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41129Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw41129step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![-3, 0, 3]]
def raw41129step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41129step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw41129step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41129 raw41129Labels = mixedMoment B node1153 node1153Labels := by
  calc
    mixedMoment B raw41129 raw41129Labels = mixedMoment B raw41129step0 raw41129step0Labels := by
      have hz : ∀ j, raw41129 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41129step0 = (fun i j => raw41129 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41129step0 raw41129; decide +kernel
      have hl : raw41129step0Labels = raw41129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41129 raw41129Labels permutation434 hz
    mixedMoment B raw41129step0 raw41129step0Labels = mixedMoment B raw41129step1 raw41129step1Labels := by
      have ha : raw41129step1 = (fun i j => raw41129step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41129step1 raw41129step0; decide +kernel
      have hl : raw41129step1Labels = raw41129step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41129step0 raw41129step0Labels permutation35 permutation6
    mixedMoment B raw41129step1 raw41129step1Labels = mixedMoment B raw41129step2 raw41129step2Labels := by
      have ha : raw41129step2 = -raw41129step1 := by apply Matrix.ext; change ∀ i j, raw41129step2 i j = -(raw41129step1 i j); unfold raw41129step2 raw41129step1; decide +kernel
      have hl : raw41129step2Labels = raw41129step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1153 node1153Labels := by rfl

def raw41130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw41130Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![3, -1, -2]]
def raw41130step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw41130step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw41130step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41130 raw41130Labels = mixedMoment B node1171 node1171Labels := by
  calc
    mixedMoment B raw41130 raw41130Labels = mixedMoment B raw41130step0 raw41130step0Labels := by
      have hz : ∀ j, raw41130 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41130step0 = (fun i j => raw41130 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41130step0 raw41130; decide +kernel
      have hl : raw41130step0Labels = raw41130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41130 raw41130Labels permutation520 hz
    mixedMoment B raw41130step0 raw41130step0Labels = mixedMoment B raw41130step1 raw41130step1Labels := by
      have ha : raw41130step1 = (fun i j => raw41130step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41130step1 raw41130step0; decide +kernel
      have hl : raw41130step1Labels = raw41130step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41130step0 raw41130step0Labels permutation35 permutation6
    mixedMoment B raw41130step1 raw41130step1Labels = mixedMoment B raw41130step2 raw41130step2Labels := by
      have ha : raw41130step2 = -raw41130step1 := by apply Matrix.ext; change ∀ i j, raw41130step2 i j = -(raw41130step1 i j); unfold raw41130step2 raw41130step1; decide +kernel
      have hl : raw41130step2Labels = raw41130step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1171 node1171Labels := by rfl

def raw41131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41131Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41131step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw41131step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41131step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41131step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41131 raw41131Labels = mixedMoment B node1156 node1156Labels := by
  calc
    mixedMoment B raw41131 raw41131Labels = mixedMoment B raw41131step0 raw41131step0Labels := by
      have ha : raw41131step0 = (fun i j => raw41131 (permutation175 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41131step0 raw41131; decide +kernel
      have hl : raw41131step0Labels = raw41131Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41131 raw41131Labels permutation175 permutation6
    mixedMoment B raw41131step0 raw41131step0Labels = mixedMoment B raw41131step1 raw41131step1Labels := by
      have ha : raw41131step1 = -raw41131step0 := by apply Matrix.ext; change ∀ i j, raw41131step1 i j = -(raw41131step0 i j); unfold raw41131step1 raw41131step0; decide +kernel
      have hl : raw41131step1Labels = raw41131step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1156 node1156Labels := by rfl

def raw41132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41132Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41132step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41132step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41132step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41132 raw41132Labels = mixedMoment B node1151 node1151Labels := by
  calc
    mixedMoment B raw41132 raw41132Labels = mixedMoment B raw41132step0 raw41132step0Labels := by
      have ha : raw41132step0 = (fun i j => raw41132 (permutation167 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41132step0 raw41132; decide +kernel
      have hl : raw41132step0Labels = raw41132Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41132 raw41132Labels permutation167 permutation6
    mixedMoment B raw41132step0 raw41132step0Labels = mixedMoment B raw41132step1 raw41132step1Labels := by
      have ha : raw41132step1 = -raw41132step0 := by apply Matrix.ext; change ∀ i j, raw41132step1 i j = -(raw41132step0 i j); unfold raw41132step1 raw41132step0; decide +kernel
      have hl : raw41132step1Labels = raw41132step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1151 node1151Labels := by rfl

def raw41133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41133Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw41133step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![-1, 2, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw41133step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41133step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw41133step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41133 raw41133Labels = mixedMoment B node1160 node1160Labels := by
  calc
    mixedMoment B raw41133 raw41133Labels = mixedMoment B raw41133step0 raw41133step0Labels := by
      have hz : ∀ j, raw41133 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41133step0 = (fun i j => raw41133 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41133step0 raw41133; decide +kernel
      have hl : raw41133step0Labels = raw41133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41133 raw41133Labels permutation434 hz
    mixedMoment B raw41133step0 raw41133step0Labels = mixedMoment B raw41133step1 raw41133step1Labels := by
      have ha : raw41133step1 = (fun i j => raw41133step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41133step1 raw41133step0; decide +kernel
      have hl : raw41133step1Labels = raw41133step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41133step0 raw41133step0Labels permutation37 permutation6
    mixedMoment B raw41133step1 raw41133step1Labels = mixedMoment B raw41133step2 raw41133step2Labels := by
      have ha : raw41133step2 = -raw41133step1 := by apply Matrix.ext; change ∀ i j, raw41133step2 i j = -(raw41133step1 i j); unfold raw41133step2 raw41133step1; decide +kernel
      have hl : raw41133step2Labels = raw41133step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1160 node1160Labels := by rfl

def raw41134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw41134Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw41134step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw41134step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41134step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw41134step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41134 raw41134Labels = mixedMoment B node1155 node1155Labels := by
  calc
    mixedMoment B raw41134 raw41134Labels = mixedMoment B raw41134step0 raw41134step0Labels := by
      have hz : ∀ j, raw41134 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41134step0 = (fun i j => raw41134 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41134step0 raw41134; decide +kernel
      have hl : raw41134step0Labels = raw41134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41134 raw41134Labels permutation434 hz
    mixedMoment B raw41134step0 raw41134step0Labels = mixedMoment B raw41134step1 raw41134step1Labels := by
      have ha : raw41134step1 = (fun i j => raw41134step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41134step1 raw41134step0; decide +kernel
      have hl : raw41134step1Labels = raw41134step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41134step0 raw41134step0Labels permutation34 permutation6
    mixedMoment B raw41134step1 raw41134step1Labels = mixedMoment B raw41134step2 raw41134step2Labels := by
      have ha : raw41134step2 = -raw41134step1 := by apply Matrix.ext; change ∀ i j, raw41134step2 i j = -(raw41134step1 i j); unfold raw41134step2 raw41134step1; decide +kernel
      have hl : raw41134step2Labels = raw41134step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1155 node1155Labels := by rfl

def raw41135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw41135Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41135step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw41135step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41135step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41135step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41135 raw41135Labels = mixedMoment B node1149 node1149Labels := by
  calc
    mixedMoment B raw41135 raw41135Labels = mixedMoment B raw41135step0 raw41135step0Labels := by
      have ha : raw41135step0 = (fun i j => raw41135 (permutation175 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41135step0 raw41135; decide +kernel
      have hl : raw41135step0Labels = raw41135Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41135 raw41135Labels permutation175 permutation6
    mixedMoment B raw41135step0 raw41135step0Labels = mixedMoment B raw41135step1 raw41135step1Labels := by
      have ha : raw41135step1 = -raw41135step0 := by apply Matrix.ext; change ∀ i j, raw41135step1 i j = -(raw41135step0 i j); unfold raw41135step1 raw41135step0; decide +kernel
      have hl : raw41135step1Labels = raw41135step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1149 node1149Labels := by rfl

def raw41136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw41136Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw41136step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41136step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41136 raw41136Labels = mixedMoment B node1169 node1169Labels := by
  calc
    mixedMoment B raw41136 raw41136Labels = mixedMoment B raw41136step0 raw41136step0Labels := by
      have ha : raw41136step0 = (fun i j => raw41136 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41136step0 raw41136; decide +kernel
      have hl : raw41136step0Labels = raw41136Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41136 raw41136Labels permutation152 permutation6
    mixedMoment B raw41136step0 raw41136step0Labels = mixedMoment B raw41136step1 raw41136step1Labels := by
      have ha : raw41136step1 = -raw41136step0 := by apply Matrix.ext; change ∀ i j, raw41136step1 i j = -(raw41136step0 i j); unfold raw41136step1 raw41136step0; decide +kernel
      have hl : raw41136step1Labels = raw41136step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1169 node1169Labels := by rfl

def raw41137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw41137Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw41137step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41137step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41137step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41137 raw41137Labels = mixedMoment B node1150 node1150Labels := by
  calc
    mixedMoment B raw41137 raw41137Labels = mixedMoment B raw41137step0 raw41137step0Labels := by
      have ha : raw41137step0 = (fun i j => raw41137 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41137step0 raw41137; decide +kernel
      have hl : raw41137step0Labels = raw41137Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41137 raw41137Labels permutation164 permutation6
    mixedMoment B raw41137step0 raw41137step0Labels = mixedMoment B raw41137step1 raw41137step1Labels := by
      have ha : raw41137step1 = -raw41137step0 := by apply Matrix.ext; change ∀ i j, raw41137step1 i j = -(raw41137step0 i j); unfold raw41137step1 raw41137step0; decide +kernel
      have hl : raw41137step1Labels = raw41137step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1150 node1150Labels := by rfl

def raw41138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -1, -1]]
def raw41138Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw41138step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw41138step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41138step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw41138step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41138 raw41138Labels = mixedMoment B node1159 node1159Labels := by
  calc
    mixedMoment B raw41138 raw41138Labels = mixedMoment B raw41138step0 raw41138step0Labels := by
      have hz : ∀ j, raw41138 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41138step0 = (fun i j => raw41138 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41138step0 raw41138; decide +kernel
      have hl : raw41138step0Labels = raw41138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41138 raw41138Labels permutation434 hz
    mixedMoment B raw41138step0 raw41138step0Labels = mixedMoment B raw41138step1 raw41138step1Labels := by
      have ha : raw41138step1 = (fun i j => raw41138step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41138step1 raw41138step0; decide +kernel
      have hl : raw41138step1Labels = raw41138step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41138step0 raw41138step0Labels permutation36 permutation6
    mixedMoment B raw41138step1 raw41138step1Labels = mixedMoment B raw41138step2 raw41138step2Labels := by
      have ha : raw41138step2 = -raw41138step1 := by apply Matrix.ext; change ∀ i j, raw41138step2 i j = -(raw41138step1 i j); unfold raw41138step2 raw41138step1; decide +kernel
      have hl : raw41138step2Labels = raw41138step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1159 node1159Labels := by rfl

def raw41139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw41139Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw41139step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw41139step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41139 raw41139Labels = mixedMoment B node1115 node1115Labels := by
  calc
    mixedMoment B raw41139 raw41139Labels = mixedMoment B raw41139step0 raw41139step0Labels := by
      have hz : ∀ j, raw41139 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41139step0 = (fun i j => raw41139 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41139step0 raw41139; decide +kernel
      have hl : raw41139step0Labels = raw41139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41139 raw41139Labels permutation434 hz
    mixedMoment B raw41139step0 raw41139step0Labels = mixedMoment B raw41139step1 raw41139step1Labels := by
      have ha : raw41139step1 = (fun i j => raw41139step0 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41139step1 raw41139step0; decide +kernel
      have hl : raw41139step1Labels = raw41139step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41139step0 raw41139step0Labels permutation145 permutation6
    _ = mixedMoment B node1115 node1115Labels := by rfl

def raw41140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41140Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw41140step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41140step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw41140step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41140 raw41140Labels = mixedMoment B node1148 node1148Labels := by
  calc
    mixedMoment B raw41140 raw41140Labels = mixedMoment B raw41140step0 raw41140step0Labels := by
      have ha : raw41140step0 = (fun i j => raw41140 (permutation174 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41140step0 raw41140; decide +kernel
      have hl : raw41140step0Labels = raw41140Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41140 raw41140Labels permutation174 permutation6
    mixedMoment B raw41140step0 raw41140step0Labels = mixedMoment B raw41140step1 raw41140step1Labels := by
      have ha : raw41140step1 = -raw41140step0 := by apply Matrix.ext; change ∀ i j, raw41140step1 i j = -(raw41140step0 i j); unfold raw41140step1 raw41140step0; decide +kernel
      have hl : raw41140step1Labels = raw41140step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1148 node1148Labels := by rfl

def raw41141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw41141Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw41141step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41141step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![2, 3, -5]]
def raw41141step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41141step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw41141step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41141 raw41141Labels = mixedMoment B node584 node584Labels := by
  calc
    mixedMoment B raw41141 raw41141Labels = mixedMoment B raw41141step0 raw41141step0Labels := by
      have hz : ∀ j, raw41141 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41141step0 = (fun i j => raw41141 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41141step0 raw41141; decide +kernel
      have hl : raw41141step0Labels = raw41141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41141 raw41141Labels permutation434 hz
    mixedMoment B raw41141step0 raw41141step0Labels = mixedMoment B raw41141step1 raw41141step1Labels := by
      have hz : ∀ j, raw41141step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41141step1 = (fun i j => raw41141step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41141step1 raw41141step0; decide +kernel
      have hl : raw41141step1Labels = raw41141step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41141step0 raw41141step0Labels permutation80 hz
    mixedMoment B raw41141step1 raw41141step1Labels = mixedMoment B raw41141step2 raw41141step2Labels := by
      have ha : raw41141step2 = (fun i j => raw41141step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41141step2 raw41141step1; decide +kernel
      have hl : raw41141step2Labels = raw41141step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41141step1 raw41141step1Labels permutation31 permutation6
    _ = mixedMoment B node584 node584Labels := by rfl

def raw41142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw41142Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw41142step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41142step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![2, -1, -1]]
def raw41142step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41142step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![2, -1, -1]]
def raw41142step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41142step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-3, 0, 3]]
def raw41142step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41142step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw41142step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41142 raw41142Labels = mixedMoment B node1297 node1297Labels := by
  calc
    mixedMoment B raw41142 raw41142Labels = mixedMoment B raw41142step0 raw41142step0Labels := by
      have hz : ∀ j, raw41142 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41142step0 = (fun i j => raw41142 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41142step0 raw41142; decide +kernel
      have hl : raw41142step0Labels = raw41142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41142 raw41142Labels permutation520 hz
    mixedMoment B raw41142step0 raw41142step0Labels = mixedMoment B raw41142step1 raw41142step1Labels := by
      have hz : ∀ j, raw41142step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41142step1 = (fun i j => raw41142step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41142step1 raw41142step0; decide +kernel
      have hl : raw41142step1Labels = raw41142step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41142step0 raw41142step0Labels permutation104 hz
    mixedMoment B raw41142step1 raw41142step1Labels = mixedMoment B raw41142step2 raw41142step2Labels := by
      have hz : ∀ j, raw41142step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41142step2 = (fun i j => raw41142step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41142step2 raw41142step1; decide +kernel
      have hl : raw41142step2Labels = raw41142step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41142step1 raw41142step1Labels permutation20 hz
    mixedMoment B raw41142step2 raw41142step2Labels = mixedMoment B raw41142step3 raw41142step3Labels := by
      have ha : raw41142step3 = (fun i j => raw41142step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41142step3 raw41142step2; decide +kernel
      have hl : raw41142step3Labels = raw41142step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41142step2 raw41142step2Labels permutation3 permutation6
    mixedMoment B raw41142step3 raw41142step3Labels = mixedMoment B raw41142step4 raw41142step4Labels := by
      have ha : raw41142step4 = -raw41142step3 := by apply Matrix.ext; change ∀ i j, raw41142step4 i j = -(raw41142step3 i j); unfold raw41142step4 raw41142step3; decide +kernel
      have hl : raw41142step4Labels = raw41142step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1297 node1297Labels := by rfl

def raw41143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw41143Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw41143step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41143step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, -1, 1], ![2, 0, -2]]
def raw41143step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41143step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 2, 0], ![-3, 0, 3]]
def raw41143step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41143step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw41143step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41143 raw41143Labels = mixedMoment B node1143 node1143Labels := by
  calc
    mixedMoment B raw41143 raw41143Labels = mixedMoment B raw41143step0 raw41143step0Labels := by
      have hz : ∀ j, raw41143 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41143step0 = (fun i j => raw41143 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41143step0 raw41143; decide +kernel
      have hl : raw41143step0Labels = raw41143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41143 raw41143Labels permutation434 hz
    mixedMoment B raw41143step0 raw41143step0Labels = mixedMoment B raw41143step1 raw41143step1Labels := by
      have hz : ∀ j, raw41143step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41143step1 = (fun i j => raw41143step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41143step1 raw41143step0; decide +kernel
      have hl : raw41143step1Labels = raw41143step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41143step0 raw41143step0Labels permutation80 hz
    mixedMoment B raw41143step1 raw41143step1Labels = mixedMoment B raw41143step2 raw41143step2Labels := by
      have ha : raw41143step2 = (fun i j => raw41143step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41143step2 raw41143step1; decide +kernel
      have hl : raw41143step2Labels = raw41143step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41143step1 raw41143step1Labels permutation11 permutation6
    mixedMoment B raw41143step2 raw41143step2Labels = mixedMoment B raw41143step3 raw41143step3Labels := by
      have ha : raw41143step3 = -raw41143step2 := by apply Matrix.ext; change ∀ i j, raw41143step3 i j = -(raw41143step2 i j); unfold raw41143step3 raw41143step2; decide +kernel
      have hl : raw41143step3Labels = raw41143step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1143 node1143Labels := by rfl

def raw41144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw41144Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw41144step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41144step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41144step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41144step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-3, 0, 3]]
def raw41144step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41144step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw41144step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41144 raw41144Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw41144 raw41144Labels = mixedMoment B raw41144step0 raw41144step0Labels := by
      have hz : ∀ j, raw41144 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41144step0 = (fun i j => raw41144 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41144step0 raw41144; decide +kernel
      have hl : raw41144step0Labels = raw41144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41144 raw41144Labels permutation434 hz
    mixedMoment B raw41144step0 raw41144step0Labels = mixedMoment B raw41144step1 raw41144step1Labels := by
      have hz : ∀ j, raw41144step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41144step1 = (fun i j => raw41144step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41144step1 raw41144step0; decide +kernel
      have hl : raw41144step1Labels = raw41144step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41144step0 raw41144step0Labels permutation80 hz
    mixedMoment B raw41144step1 raw41144step1Labels = mixedMoment B raw41144step2 raw41144step2Labels := by
      have ha : raw41144step2 = (fun i j => raw41144step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41144step2 raw41144step1; decide +kernel
      have hl : raw41144step2Labels = raw41144step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41144step1 raw41144step1Labels permutation13 permutation6
    mixedMoment B raw41144step2 raw41144step2Labels = mixedMoment B raw41144step3 raw41144step3Labels := by
      have ha : raw41144step3 = -raw41144step2 := by apply Matrix.ext; change ∀ i j, raw41144step3 i j = -(raw41144step2 i j); unfold raw41144step3 raw41144step2; decide +kernel
      have hl : raw41144step3Labels = raw41144step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1239 node1239Labels := by rfl

def raw41145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41145Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41145step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw41145step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41145step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw41145step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41145 raw41145Labels = mixedMoment B node1128 node1128Labels := by
  calc
    mixedMoment B raw41145 raw41145Labels = mixedMoment B raw41145step0 raw41145step0Labels := by
      have hz : ∀ j, raw41145 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41145step0 = (fun i j => raw41145 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41145step0 raw41145; decide +kernel
      have hl : raw41145step0Labels = raw41145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41145 raw41145Labels permutation346 hz
    mixedMoment B raw41145step0 raw41145step0Labels = mixedMoment B raw41145step1 raw41145step1Labels := by
      have ha : raw41145step1 = (fun i j => raw41145step0 (permutation41 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41145step1 raw41145step0; decide +kernel
      have hl : raw41145step1Labels = raw41145step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41145step0 raw41145step0Labels permutation41 permutation6
    mixedMoment B raw41145step1 raw41145step1Labels = mixedMoment B raw41145step2 raw41145step2Labels := by
      have ha : raw41145step2 = -raw41145step1 := by apply Matrix.ext; change ∀ i j, raw41145step2 i j = -(raw41145step1 i j); unfold raw41145step2 raw41145step1; decide +kernel
      have hl : raw41145step2Labels = raw41145step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1128 node1128Labels := by rfl

def raw41146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw41146Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw41146step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41146step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![2, -1, -1]]
def raw41146step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41146step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw41146step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41146step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw41146step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41146 raw41146Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw41146 raw41146Labels = mixedMoment B raw41146step0 raw41146step0Labels := by
      have hz : ∀ j, raw41146 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41146step0 = (fun i j => raw41146 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41146step0 raw41146; decide +kernel
      have hl : raw41146step0Labels = raw41146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41146 raw41146Labels permutation520 hz
    mixedMoment B raw41146step0 raw41146step0Labels = mixedMoment B raw41146step1 raw41146step1Labels := by
      have hz : ∀ j, raw41146step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41146step1 = (fun i j => raw41146step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41146step1 raw41146step0; decide +kernel
      have hl : raw41146step1Labels = raw41146step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41146step0 raw41146step0Labels permutation104 hz
    mixedMoment B raw41146step1 raw41146step1Labels = mixedMoment B raw41146step2 raw41146step2Labels := by
      have ha : raw41146step2 = (fun i j => raw41146step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41146step2 raw41146step1; decide +kernel
      have hl : raw41146step2Labels = raw41146step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41146step1 raw41146step1Labels permutation13 permutation6
    mixedMoment B raw41146step2 raw41146step2Labels = mixedMoment B raw41146step3 raw41146step3Labels := by
      have ha : raw41146step3 = -raw41146step2 := by apply Matrix.ext; change ∀ i j, raw41146step3 i j = -(raw41146step2 i j); unfold raw41146step3 raw41146step2; decide +kernel
      have hl : raw41146step3Labels = raw41146step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1294 node1294Labels := by rfl

def raw41147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw41147Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw41147step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41147step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41147step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41147 raw41147Labels = mixedMoment B node1138 node1138Labels := by
  calc
    mixedMoment B raw41147 raw41147Labels = mixedMoment B raw41147step0 raw41147step0Labels := by
      have hz : ∀ j, raw41147 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41147step0 = (fun i j => raw41147 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41147step0 raw41147; decide +kernel
      have hl : raw41147step0Labels = raw41147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41147 raw41147Labels permutation434 hz
    mixedMoment B raw41147step0 raw41147step0Labels = mixedMoment B raw41147step1 raw41147step1Labels := by
      have ha : raw41147step1 = (fun i j => raw41147step0 (permutation47 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41147step1 raw41147step0; decide +kernel
      have hl : raw41147step1Labels = raw41147step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41147step0 raw41147step0Labels permutation47 permutation6
    mixedMoment B raw41147step1 raw41147step1Labels = mixedMoment B raw41147step2 raw41147step2Labels := by
      have ha : raw41147step2 = -raw41147step1 := by apply Matrix.ext; change ∀ i j, raw41147step2 i j = -(raw41147step1 i j); unfold raw41147step2 raw41147step1; decide +kernel
      have hl : raw41147step2Labels = raw41147step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1138 node1138Labels := by rfl

def raw41148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw41148Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41148step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw41148step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41148step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41148 raw41148Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw41148 raw41148Labels = mixedMoment B raw41148step0 raw41148step0Labels := by
      have hz : ∀ j, raw41148 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41148step0 = (fun i j => raw41148 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41148step0 raw41148; decide +kernel
      have hl : raw41148step0Labels = raw41148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41148 raw41148Labels permutation434 hz
    mixedMoment B raw41148step0 raw41148step0Labels = mixedMoment B raw41148step1 raw41148step1Labels := by
      have ha : raw41148step1 = (fun i j => raw41148step0 (permutation55 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41148step1 raw41148step0; decide +kernel
      have hl : raw41148step1Labels = raw41148step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41148step0 raw41148step0Labels permutation55 permutation6
    mixedMoment B raw41148step1 raw41148step1Labels = mixedMoment B raw41148step2 raw41148step2Labels := by
      have ha : raw41148step2 = -raw41148step1 := by apply Matrix.ext; change ∀ i j, raw41148step2 i j = -(raw41148step1 i j); unfold raw41148step2 raw41148step1; decide +kernel
      have hl : raw41148step2Labels = raw41148step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw41149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41149Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw41149step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41149step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41149step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41149 raw41149Labels = mixedMoment B node1126 node1126Labels := by
  calc
    mixedMoment B raw41149 raw41149Labels = mixedMoment B raw41149step0 raw41149step0Labels := by
      have ha : raw41149step0 = (fun i j => raw41149 (permutation217 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41149step0 raw41149; decide +kernel
      have hl : raw41149step0Labels = raw41149Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41149 raw41149Labels permutation217 permutation6
    mixedMoment B raw41149step0 raw41149step0Labels = mixedMoment B raw41149step1 raw41149step1Labels := by
      have ha : raw41149step1 = -raw41149step0 := by apply Matrix.ext; change ∀ i j, raw41149step1 i j = -(raw41149step0 i j); unfold raw41149step1 raw41149step0; decide +kernel
      have hl : raw41149step1Labels = raw41149step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1126 node1126Labels := by rfl

def raw41150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw41150Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw41150step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41150step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, -1, 1], ![2, 1, -3]]
def raw41150step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41150step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw41150step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41150step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw41150step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41150 raw41150Labels = mixedMoment B node1145 node1145Labels := by
  calc
    mixedMoment B raw41150 raw41150Labels = mixedMoment B raw41150step0 raw41150step0Labels := by
      have hz : ∀ j, raw41150 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41150step0 = (fun i j => raw41150 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41150step0 raw41150; decide +kernel
      have hl : raw41150step0Labels = raw41150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41150 raw41150Labels permutation434 hz
    mixedMoment B raw41150step0 raw41150step0Labels = mixedMoment B raw41150step1 raw41150step1Labels := by
      have hz : ∀ j, raw41150step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41150step1 = (fun i j => raw41150step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41150step1 raw41150step0; decide +kernel
      have hl : raw41150step1Labels = raw41150step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41150step0 raw41150step0Labels permutation80 hz
    mixedMoment B raw41150step1 raw41150step1Labels = mixedMoment B raw41150step2 raw41150step2Labels := by
      have ha : raw41150step2 = (fun i j => raw41150step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41150step2 raw41150step1; decide +kernel
      have hl : raw41150step2Labels = raw41150step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41150step1 raw41150step1Labels permutation10 permutation6
    mixedMoment B raw41150step2 raw41150step2Labels = mixedMoment B raw41150step3 raw41150step3Labels := by
      have ha : raw41150step3 = -raw41150step2 := by apply Matrix.ext; change ∀ i j, raw41150step3 i j = -(raw41150step2 i j); unfold raw41150step3 raw41150step2; decide +kernel
      have hl : raw41150step3Labels = raw41150step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1145 node1145Labels := by rfl

def raw41151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw41151Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw41151step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41151step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41151step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41151step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw41151step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41151step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw41151step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41151 raw41151Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw41151 raw41151Labels = mixedMoment B raw41151step0 raw41151step0Labels := by
      have hz : ∀ j, raw41151 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41151step0 = (fun i j => raw41151 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41151step0 raw41151; decide +kernel
      have hl : raw41151step0Labels = raw41151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41151 raw41151Labels permutation434 hz
    mixedMoment B raw41151step0 raw41151step0Labels = mixedMoment B raw41151step1 raw41151step1Labels := by
      have hz : ∀ j, raw41151step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41151step1 = (fun i j => raw41151step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41151step1 raw41151step0; decide +kernel
      have hl : raw41151step1Labels = raw41151step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41151step0 raw41151step0Labels permutation80 hz
    mixedMoment B raw41151step1 raw41151step1Labels = mixedMoment B raw41151step2 raw41151step2Labels := by
      have ha : raw41151step2 = (fun i j => raw41151step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41151step2 raw41151step1; decide +kernel
      have hl : raw41151step2Labels = raw41151step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41151step1 raw41151step1Labels permutation13 permutation6
    mixedMoment B raw41151step2 raw41151step2Labels = mixedMoment B raw41151step3 raw41151step3Labels := by
      have ha : raw41151step3 = -raw41151step2 := by apply Matrix.ext; change ∀ i j, raw41151step3 i j = -(raw41151step2 i j); unfold raw41151step3 raw41151step2; decide +kernel
      have hl : raw41151step3Labels = raw41151step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1246 node1246Labels := by rfl

def raw41152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw41152Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw41152step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw41152step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41152step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41152 raw41152Labels = mixedMoment B node1134 node1134Labels := by
  calc
    mixedMoment B raw41152 raw41152Labels = mixedMoment B raw41152step0 raw41152step0Labels := by
      have hz : ∀ j, raw41152 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41152step0 = (fun i j => raw41152 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41152step0 raw41152; decide +kernel
      have hl : raw41152step0Labels = raw41152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41152 raw41152Labels permutation346 hz
    mixedMoment B raw41152step0 raw41152step0Labels = mixedMoment B raw41152step1 raw41152step1Labels := by
      have ha : raw41152step1 = (fun i j => raw41152step0 (permutation43 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41152step1 raw41152step0; decide +kernel
      have hl : raw41152step1Labels = raw41152step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41152step0 raw41152step0Labels permutation43 permutation6
    mixedMoment B raw41152step1 raw41152step1Labels = mixedMoment B raw41152step2 raw41152step2Labels := by
      have ha : raw41152step2 = -raw41152step1 := by apply Matrix.ext; change ∀ i j, raw41152step2 i j = -(raw41152step1 i j); unfold raw41152step2 raw41152step1; decide +kernel
      have hl : raw41152step2Labels = raw41152step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1134 node1134Labels := by rfl

def raw41153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw41153Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw41153step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw41153step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41153step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41153step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41153 raw41153Labels = mixedMoment B node1293 node1293Labels := by
  calc
    mixedMoment B raw41153 raw41153Labels = mixedMoment B raw41153step0 raw41153step0Labels := by
      have hz : ∀ j, raw41153 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41153step0 = (fun i j => raw41153 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41153step0 raw41153; decide +kernel
      have hl : raw41153step0Labels = raw41153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41153 raw41153Labels permutation520 hz
    mixedMoment B raw41153step0 raw41153step0Labels = mixedMoment B raw41153step1 raw41153step1Labels := by
      have ha : raw41153step1 = (fun i j => raw41153step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41153step1 raw41153step0; decide +kernel
      have hl : raw41153step1Labels = raw41153step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41153step0 raw41153step0Labels permutation50 permutation6
    mixedMoment B raw41153step1 raw41153step1Labels = mixedMoment B raw41153step2 raw41153step2Labels := by
      have ha : raw41153step2 = -raw41153step1 := by apply Matrix.ext; change ∀ i j, raw41153step2 i j = -(raw41153step1 i j); unfold raw41153step2 raw41153step1; decide +kernel
      have hl : raw41153step2Labels = raw41153step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1293 node1293Labels := by rfl

def raw41154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw41154Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41154step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41154step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41154step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41154 raw41154Labels = mixedMoment B node1135 node1135Labels := by
  calc
    mixedMoment B raw41154 raw41154Labels = mixedMoment B raw41154step0 raw41154step0Labels := by
      have ha : raw41154step0 = (fun i j => raw41154 (permutation224 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41154step0 raw41154; decide +kernel
      have hl : raw41154step0Labels = raw41154Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41154 raw41154Labels permutation224 permutation6
    mixedMoment B raw41154step0 raw41154step0Labels = mixedMoment B raw41154step1 raw41154step1Labels := by
      have ha : raw41154step1 = -raw41154step0 := by apply Matrix.ext; change ∀ i j, raw41154step1 i j = -(raw41154step0 i j); unfold raw41154step1 raw41154step0; decide +kernel
      have hl : raw41154step1Labels = raw41154step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1135 node1135Labels := by rfl

def raw41155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41155Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw41155step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41155step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41155step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41155 raw41155Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw41155 raw41155Labels = mixedMoment B raw41155step0 raw41155step0Labels := by
      have ha : raw41155step0 = (fun i j => raw41155 (permutation260 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41155step0 raw41155; decide +kernel
      have hl : raw41155step0Labels = raw41155Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41155 raw41155Labels permutation260 permutation6
    mixedMoment B raw41155step0 raw41155step0Labels = mixedMoment B raw41155step1 raw41155step1Labels := by
      have ha : raw41155step1 = -raw41155step0 := by apply Matrix.ext; change ∀ i j, raw41155step1 i j = -(raw41155step0 i j); unfold raw41155step1 raw41155step0; decide +kernel
      have hl : raw41155step1Labels = raw41155step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1235 node1235Labels := by rfl

def raw41156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw41156Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw41156step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41156step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41156step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41156step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41156 raw41156Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw41156 raw41156Labels = mixedMoment B raw41156step0 raw41156step0Labels := by
      have hz : ∀ j, raw41156 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41156step0 = (fun i j => raw41156 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41156step0 raw41156; decide +kernel
      have hl : raw41156step0Labels = raw41156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41156 raw41156Labels permutation434 hz
    mixedMoment B raw41156step0 raw41156step0Labels = mixedMoment B raw41156step1 raw41156step1Labels := by
      have ha : raw41156step1 = (fun i j => raw41156step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41156step1 raw41156step0; decide +kernel
      have hl : raw41156step1Labels = raw41156step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41156step0 raw41156step0Labels permutation50 permutation6
    mixedMoment B raw41156step1 raw41156step1Labels = mixedMoment B raw41156step2 raw41156step2Labels := by
      have ha : raw41156step2 = -raw41156step1 := by apply Matrix.ext; change ∀ i j, raw41156step2 i j = -(raw41156step1 i j); unfold raw41156step2 raw41156step1; decide +kernel
      have hl : raw41156step2Labels = raw41156step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1240 node1240Labels := by rfl

def raw41157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw41157Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41157step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41157step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41157step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41157 raw41157Labels = mixedMoment B node1129 node1129Labels := by
  calc
    mixedMoment B raw41157 raw41157Labels = mixedMoment B raw41157step0 raw41157step0Labels := by
      have ha : raw41157step0 = (fun i j => raw41157 (permutation218 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41157step0 raw41157; decide +kernel
      have hl : raw41157step0Labels = raw41157Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41157 raw41157Labels permutation218 permutation6
    mixedMoment B raw41157step0 raw41157step0Labels = mixedMoment B raw41157step1 raw41157step1Labels := by
      have ha : raw41157step1 = -raw41157step0 := by apply Matrix.ext; change ∀ i j, raw41157step1 i j = -(raw41157step0 i j); unfold raw41157step1 raw41157step0; decide +kernel
      have hl : raw41157step1Labels = raw41157step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1129 node1129Labels := by rfl

def raw41158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 2, -4]]
def raw41158Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 2, -4]]
def raw41158step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41158step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, -1, 1], ![2, 2, -4]]
def raw41158step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41158step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw41158step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41158 raw41158Labels = mixedMoment B node1140 node1140Labels := by
  calc
    mixedMoment B raw41158 raw41158Labels = mixedMoment B raw41158step0 raw41158step0Labels := by
      have hz : ∀ j, raw41158 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41158step0 = (fun i j => raw41158 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41158step0 raw41158; decide +kernel
      have hl : raw41158step0Labels = raw41158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41158 raw41158Labels permutation434 hz
    mixedMoment B raw41158step0 raw41158step0Labels = mixedMoment B raw41158step1 raw41158step1Labels := by
      have hz : ∀ j, raw41158step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41158step1 = (fun i j => raw41158step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41158step1 raw41158step0; decide +kernel
      have hl : raw41158step1Labels = raw41158step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41158step0 raw41158step0Labels permutation80 hz
    mixedMoment B raw41158step1 raw41158step1Labels = mixedMoment B raw41158step2 raw41158step2Labels := by
      have ha : raw41158step2 = (fun i j => raw41158step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41158step2 raw41158step1; decide +kernel
      have hl : raw41158step2Labels = raw41158step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41158step1 raw41158step1Labels permutation29 permutation6
    _ = mixedMoment B node1140 node1140Labels := by rfl

def raw41159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw41159Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw41159step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41159step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0]]
def raw41159step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41159step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw41159step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41159step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw41159step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41159 raw41159Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw41159 raw41159Labels = mixedMoment B raw41159step0 raw41159step0Labels := by
      have hz : ∀ j, raw41159 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41159step0 = (fun i j => raw41159 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41159step0 raw41159; decide +kernel
      have hl : raw41159step0Labels = raw41159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41159 raw41159Labels permutation434 hz
    mixedMoment B raw41159step0 raw41159step0Labels = mixedMoment B raw41159step1 raw41159step1Labels := by
      have hz : ∀ j, raw41159step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41159step1 = (fun i j => raw41159step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41159step1 raw41159step0; decide +kernel
      have hl : raw41159step1Labels = raw41159step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41159step0 raw41159step0Labels permutation80 hz
    mixedMoment B raw41159step1 raw41159step1Labels = mixedMoment B raw41159step2 raw41159step2Labels := by
      have ha : raw41159step2 = (fun i j => raw41159step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41159step2 raw41159step1; decide +kernel
      have hl : raw41159step2Labels = raw41159step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41159step1 raw41159step1Labels permutation12 permutation6
    mixedMoment B raw41159step2 raw41159step2Labels = mixedMoment B raw41159step3 raw41159step3Labels := by
      have ha : raw41159step3 = -raw41159step2 := by apply Matrix.ext; change ∀ i j, raw41159step3 i j = -(raw41159step2 i j); unfold raw41159step3 raw41159step2; decide +kernel
      have hl : raw41159step3Labels = raw41159step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1242 node1242Labels := by rfl

def raw41160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw41160Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw41160step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw41160step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41160step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw41160step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41160 raw41160Labels = mixedMoment B node1131 node1131Labels := by
  calc
    mixedMoment B raw41160 raw41160Labels = mixedMoment B raw41160step0 raw41160step0Labels := by
      have hz : ∀ j, raw41160 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41160step0 = (fun i j => raw41160 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41160step0 raw41160; decide +kernel
      have hl : raw41160step0Labels = raw41160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41160 raw41160Labels permutation346 hz
    mixedMoment B raw41160step0 raw41160step0Labels = mixedMoment B raw41160step1 raw41160step1Labels := by
      have ha : raw41160step1 = (fun i j => raw41160step0 (permutation42 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41160step1 raw41160step0; decide +kernel
      have hl : raw41160step1Labels = raw41160step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41160step0 raw41160step0Labels permutation42 permutation6
    mixedMoment B raw41160step1 raw41160step1Labels = mixedMoment B raw41160step2 raw41160step2Labels := by
      have ha : raw41160step2 = -raw41160step1 := by apply Matrix.ext; change ∀ i j, raw41160step2 i j = -(raw41160step1 i j); unfold raw41160step2 raw41160step1; decide +kernel
      have hl : raw41160step2Labels = raw41160step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1131 node1131Labels := by rfl

def raw41161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw41161Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw41161step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw41161step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41161step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41161step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41161 raw41161Labels = mixedMoment B node1139 node1139Labels := by
  calc
    mixedMoment B raw41161 raw41161Labels = mixedMoment B raw41161step0 raw41161step0Labels := by
      have hz : ∀ j, raw41161 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41161step0 = (fun i j => raw41161 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41161step0 raw41161; decide +kernel
      have hl : raw41161step0Labels = raw41161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41161 raw41161Labels permutation346 hz
    mixedMoment B raw41161step0 raw41161step0Labels = mixedMoment B raw41161step1 raw41161step1Labels := by
      have ha : raw41161step1 = (fun i j => raw41161step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41161step1 raw41161step0; decide +kernel
      have hl : raw41161step1Labels = raw41161step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41161step0 raw41161step0Labels permutation38 permutation6
    mixedMoment B raw41161step1 raw41161step1Labels = mixedMoment B raw41161step2 raw41161step2Labels := by
      have ha : raw41161step2 = -raw41161step1 := by apply Matrix.ext; change ∀ i j, raw41161step2 i j = -(raw41161step1 i j); unfold raw41161step2 raw41161step1; decide +kernel
      have hl : raw41161step2Labels = raw41161step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1139 node1139Labels := by rfl

def raw41162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw41162Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw41162step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41162step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw41162step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41162step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![2, 3, -5]]
def raw41162step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41162step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw41162step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41162 raw41162Labels = mixedMoment B node615 node615Labels := by
  calc
    mixedMoment B raw41162 raw41162Labels = mixedMoment B raw41162step0 raw41162step0Labels := by
      have hz : ∀ j, raw41162 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41162step0 = (fun i j => raw41162 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41162step0 raw41162; decide +kernel
      have hl : raw41162step0Labels = raw41162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41162 raw41162Labels permutation434 hz
    mixedMoment B raw41162step0 raw41162step0Labels = mixedMoment B raw41162step1 raw41162step1Labels := by
      have hz : ∀ j, raw41162step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41162step1 = (fun i j => raw41162step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41162step1 raw41162step0; decide +kernel
      have hl : raw41162step1Labels = raw41162step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41162step0 raw41162step0Labels permutation80 hz
    mixedMoment B raw41162step1 raw41162step1Labels = mixedMoment B raw41162step2 raw41162step2Labels := by
      have hz : ∀ j, raw41162step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41162step2 = (fun i j => raw41162step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41162step2 raw41162step1; decide +kernel
      have hl : raw41162step2Labels = raw41162step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41162step1 raw41162step1Labels permutation14 hz
    mixedMoment B raw41162step2 raw41162step2Labels = mixedMoment B raw41162step3 raw41162step3Labels := by
      have ha : raw41162step3 = (fun i j => raw41162step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41162step3 raw41162step2; decide +kernel
      have hl : raw41162step3Labels = raw41162step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41162step2 raw41162step2Labels permutation7 permutation6
    _ = mixedMoment B node615 node615Labels := by rfl

def raw41163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0]]
def raw41163Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0]]
def raw41163step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41163step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0]]
def raw41163step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41163step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 3, -4], ![1, -1, 0]]
def raw41163step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41163step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw41163step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41163 raw41163Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw41163 raw41163Labels = mixedMoment B raw41163step0 raw41163step0Labels := by
      have hz : ∀ j, raw41163 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41163step0 = (fun i j => raw41163 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41163step0 raw41163; decide +kernel
      have hl : raw41163step0Labels = raw41163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41163 raw41163Labels permutation434 hz
    mixedMoment B raw41163step0 raw41163step0Labels = mixedMoment B raw41163step1 raw41163step1Labels := by
      have hz : ∀ j, raw41163step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41163step1 = (fun i j => raw41163step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41163step1 raw41163step0; decide +kernel
      have hl : raw41163step1Labels = raw41163step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41163step0 raw41163step0Labels permutation80 hz
    mixedMoment B raw41163step1 raw41163step1Labels = mixedMoment B raw41163step2 raw41163step2Labels := by
      have hz : ∀ j, raw41163step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41163step2 = (fun i j => raw41163step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41163step2 raw41163step1; decide +kernel
      have hl : raw41163step2Labels = raw41163step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41163step1 raw41163step1Labels permutation14 hz
    mixedMoment B raw41163step2 raw41163step2Labels = mixedMoment B raw41163step3 raw41163step3Labels := by
      have ha : raw41163step3 = (fun i j => raw41163step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41163step3 raw41163step2; decide +kernel
      have hl : raw41163step3Labels = raw41163step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41163step2 raw41163step2Labels permutation5 permutation6
    _ = mixedMoment B node1051 node1051Labels := by rfl

def raw41164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw41164Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw41164step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41164step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw41164step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41164step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw41164step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41164 raw41164Labels = mixedMoment B node934 node934Labels := by
  calc
    mixedMoment B raw41164 raw41164Labels = mixedMoment B raw41164step0 raw41164step0Labels := by
      have hz : ∀ j, raw41164 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41164step0 = (fun i j => raw41164 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41164step0 raw41164; decide +kernel
      have hl : raw41164step0Labels = raw41164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41164 raw41164Labels permutation346 hz
    mixedMoment B raw41164step0 raw41164step0Labels = mixedMoment B raw41164step1 raw41164step1Labels := by
      have hz : ∀ j, raw41164step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41164step1 = (fun i j => raw41164step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41164step1 raw41164step0; decide +kernel
      have hl : raw41164step1Labels = raw41164step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41164step0 raw41164step0Labels permutation56 hz
    mixedMoment B raw41164step1 raw41164step1Labels = mixedMoment B raw41164step2 raw41164step2Labels := by
      have ha : raw41164step2 = (fun i j => raw41164step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41164step2 raw41164step1; decide +kernel
      have hl : raw41164step2Labels = raw41164step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41164step1 raw41164step1Labels permutation25 permutation6
    _ = mixedMoment B node934 node934Labels := by rfl

def raw41165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2]]
def raw41165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2]]
def raw41165step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41165step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2]]
def raw41165step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41165step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, 1, 1], ![-3, 1, 2]]
def raw41165step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41165step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw41165step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41165 raw41165Labels = mixedMoment B node1144 node1144Labels := by
  calc
    mixedMoment B raw41165 raw41165Labels = mixedMoment B raw41165step0 raw41165step0Labels := by
      have hz : ∀ j, raw41165 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41165step0 = (fun i j => raw41165 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41165step0 raw41165; decide +kernel
      have hl : raw41165step0Labels = raw41165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41165 raw41165Labels permutation346 hz
    mixedMoment B raw41165step0 raw41165step0Labels = mixedMoment B raw41165step1 raw41165step1Labels := by
      have hz : ∀ j, raw41165step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41165step1 = (fun i j => raw41165step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41165step1 raw41165step0; decide +kernel
      have hl : raw41165step1Labels = raw41165step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41165step0 raw41165step0Labels permutation56 hz
    mixedMoment B raw41165step1 raw41165step1Labels = mixedMoment B raw41165step2 raw41165step2Labels := by
      have ha : raw41165step2 = (fun i j => raw41165step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41165step2 raw41165step1; decide +kernel
      have hl : raw41165step2Labels = raw41165step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41165step1 raw41165step1Labels permutation9 permutation6
    mixedMoment B raw41165step2 raw41165step2Labels = mixedMoment B raw41165step3 raw41165step3Labels := by
      have ha : raw41165step3 = -raw41165step2 := by apply Matrix.ext; change ∀ i j, raw41165step3 i j = -(raw41165step2 i j); unfold raw41165step3 raw41165step2; decide +kernel
      have hl : raw41165step3Labels = raw41165step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1144 node1144Labels := by rfl

def raw41166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw41166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw41166step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![0, 0, 0], ![2, 0, -2]]
def raw41166step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41166step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 3, -3], ![2, 0, -2]]
def raw41166step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41166step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-2, 2, 0], ![-3, 0, 3]]
def raw41166step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41166step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw41166step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41166 raw41166Labels = mixedMoment B node618 node618Labels := by
  calc
    mixedMoment B raw41166 raw41166Labels = mixedMoment B raw41166step0 raw41166step0Labels := by
      have hz : ∀ j, raw41166 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41166step0 = (fun i j => raw41166 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41166step0 raw41166; decide +kernel
      have hl : raw41166step0Labels = raw41166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41166 raw41166Labels permutation520 hz
    mixedMoment B raw41166step0 raw41166step0Labels = mixedMoment B raw41166step1 raw41166step1Labels := by
      have hz : ∀ j, raw41166step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41166step1 = (fun i j => raw41166step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41166step1 raw41166step0; decide +kernel
      have hl : raw41166step1Labels = raw41166step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41166step0 raw41166step0Labels permutation104 hz
    mixedMoment B raw41166step1 raw41166step1Labels = mixedMoment B raw41166step2 raw41166step2Labels := by
      have hz : ∀ j, raw41166step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41166step2 = (fun i j => raw41166step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41166step2 raw41166step1; decide +kernel
      have hl : raw41166step2Labels = raw41166step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41166step1 raw41166step1Labels permutation20 hz
    mixedMoment B raw41166step2 raw41166step2Labels = mixedMoment B raw41166step3 raw41166step3Labels := by
      have ha : raw41166step3 = (fun i j => raw41166step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41166step3 raw41166step2; decide +kernel
      have hl : raw41166step3Labels = raw41166step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41166step2 raw41166step2Labels permutation3 permutation6
    mixedMoment B raw41166step3 raw41166step3Labels = mixedMoment B raw41166step4 raw41166step4Labels := by
      have ha : raw41166step4 = -raw41166step3 := by apply Matrix.ext; change ∀ i j, raw41166step4 i j = -(raw41166step3 i j); unfold raw41166step4 raw41166step3; decide +kernel
      have hl : raw41166step4Labels = raw41166step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node618 node618Labels := by rfl

def raw41167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw41167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw41167step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41167step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![2, 0, -2]]
def raw41167step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41167step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41167step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41167step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41167step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41167 raw41167Labels = mixedMoment B node613 node613Labels := by
  calc
    mixedMoment B raw41167 raw41167Labels = mixedMoment B raw41167step0 raw41167step0Labels := by
      have hz : ∀ j, raw41167 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41167step0 = (fun i j => raw41167 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41167step0 raw41167; decide +kernel
      have hl : raw41167step0Labels = raw41167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41167 raw41167Labels permutation520 hz
    mixedMoment B raw41167step0 raw41167step0Labels = mixedMoment B raw41167step1 raw41167step1Labels := by
      have hz : ∀ j, raw41167step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41167step1 = (fun i j => raw41167step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41167step1 raw41167step0; decide +kernel
      have hl : raw41167step1Labels = raw41167step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41167step0 raw41167step0Labels permutation104 hz
    mixedMoment B raw41167step1 raw41167step1Labels = mixedMoment B raw41167step2 raw41167step2Labels := by
      have ha : raw41167step2 = (fun i j => raw41167step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41167step2 raw41167step1; decide +kernel
      have hl : raw41167step2Labels = raw41167step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41167step1 raw41167step1Labels permutation11 permutation6
    mixedMoment B raw41167step2 raw41167step2Labels = mixedMoment B raw41167step3 raw41167step3Labels := by
      have ha : raw41167step3 = -raw41167step2 := by apply Matrix.ext; change ∀ i j, raw41167step3 i j = -(raw41167step2 i j); unfold raw41167step3 raw41167step2; decide +kernel
      have hl : raw41167step3Labels = raw41167step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node613 node613Labels := by rfl

def raw41168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41168step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw41168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41168 raw41168Labels = mixedMoment B node600 node600Labels := by
  calc
    mixedMoment B raw41168 raw41168Labels = mixedMoment B raw41168step0 raw41168step0Labels := by
      have hz : ∀ j, raw41168 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41168step0 = (fun i j => raw41168 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41168step0 raw41168; decide +kernel
      have hl : raw41168step0Labels = raw41168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41168 raw41168Labels permutation434 hz
    mixedMoment B raw41168step0 raw41168step0Labels = mixedMoment B raw41168step1 raw41168step1Labels := by
      have ha : raw41168step1 = (fun i j => raw41168step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41168step1 raw41168step0; decide +kernel
      have hl : raw41168step1Labels = raw41168step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41168step0 raw41168step0Labels permutation49 permutation6
    mixedMoment B raw41168step1 raw41168step1Labels = mixedMoment B raw41168step2 raw41168step2Labels := by
      have ha : raw41168step2 = -raw41168step1 := by apply Matrix.ext; change ∀ i j, raw41168step2 i j = -(raw41168step1 i j); unfold raw41168step2 raw41168step1; decide +kernel
      have hl : raw41168step2Labels = raw41168step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node600 node600Labels := by rfl

def raw41169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw41169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw41169step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41169step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 0, 0], ![2, 1, -3]]
def raw41169step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41169step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![2, 1, -3]]
def raw41169step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41169step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-2, 0, 2], ![-3, 2, 1]]
def raw41169step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41169step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw41169step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41169 raw41169Labels = mixedMoment B node620 node620Labels := by
  calc
    mixedMoment B raw41169 raw41169Labels = mixedMoment B raw41169step0 raw41169step0Labels := by
      have hz : ∀ j, raw41169 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41169step0 = (fun i j => raw41169 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41169step0 raw41169; decide +kernel
      have hl : raw41169step0Labels = raw41169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41169 raw41169Labels permutation520 hz
    mixedMoment B raw41169step0 raw41169step0Labels = mixedMoment B raw41169step1 raw41169step1Labels := by
      have hz : ∀ j, raw41169step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41169step1 = (fun i j => raw41169step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41169step1 raw41169step0; decide +kernel
      have hl : raw41169step1Labels = raw41169step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41169step0 raw41169step0Labels permutation104 hz
    mixedMoment B raw41169step1 raw41169step1Labels = mixedMoment B raw41169step2 raw41169step2Labels := by
      have hz : ∀ j, raw41169step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41169step2 = (fun i j => raw41169step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41169step2 raw41169step1; decide +kernel
      have hl : raw41169step2Labels = raw41169step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41169step1 raw41169step1Labels permutation20 hz
    mixedMoment B raw41169step2 raw41169step2Labels = mixedMoment B raw41169step3 raw41169step3Labels := by
      have ha : raw41169step3 = (fun i j => raw41169step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41169step3 raw41169step2; decide +kernel
      have hl : raw41169step3Labels = raw41169step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41169step2 raw41169step2Labels permutation2 permutation6
    mixedMoment B raw41169step3 raw41169step3Labels = mixedMoment B raw41169step4 raw41169step4Labels := by
      have ha : raw41169step4 = -raw41169step3 := by apply Matrix.ext; change ∀ i j, raw41169step4 i j = -(raw41169step3 i j); unfold raw41169step4 raw41169step3; decide +kernel
      have hl : raw41169step4Labels = raw41169step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node620 node620Labels := by rfl

def raw41170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw41170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw41170step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1]]
def raw41170step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41170step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw41170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41170step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41170step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41170 raw41170Labels = mixedMoment B node608 node608Labels := by
  calc
    mixedMoment B raw41170 raw41170Labels = mixedMoment B raw41170step0 raw41170step0Labels := by
      have hz : ∀ j, raw41170 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41170step0 = (fun i j => raw41170 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41170step0 raw41170; decide +kernel
      have hl : raw41170step0Labels = raw41170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41170 raw41170Labels permutation434 hz
    mixedMoment B raw41170step0 raw41170step0Labels = mixedMoment B raw41170step1 raw41170step1Labels := by
      have hz : ∀ j, raw41170step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41170step1 = (fun i j => raw41170step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41170step1 raw41170step0; decide +kernel
      have hl : raw41170step1Labels = raw41170step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41170step0 raw41170step0Labels permutation80 hz
    mixedMoment B raw41170step1 raw41170step1Labels = mixedMoment B raw41170step2 raw41170step2Labels := by
      have ha : raw41170step2 = (fun i j => raw41170step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41170step2 raw41170step1; decide +kernel
      have hl : raw41170step2Labels = raw41170step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41170step1 raw41170step1Labels permutation13 permutation6
    mixedMoment B raw41170step2 raw41170step2Labels = mixedMoment B raw41170step3 raw41170step3Labels := by
      have ha : raw41170step3 = -raw41170step2 := by apply Matrix.ext; change ∀ i j, raw41170step3 i j = -(raw41170step2 i j); unfold raw41170step3 raw41170step2; decide +kernel
      have hl : raw41170step3Labels = raw41170step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node608 node608Labels := by rfl

def raw41171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw41171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw41171step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41171step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41171step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41171 raw41171Labels = mixedMoment B node610 node610Labels := by
  calc
    mixedMoment B raw41171 raw41171Labels = mixedMoment B raw41171step0 raw41171step0Labels := by
      have hz : ∀ j, raw41171 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41171step0 = (fun i j => raw41171 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41171step0 raw41171; decide +kernel
      have hl : raw41171step0Labels = raw41171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41171 raw41171Labels permutation520 hz
    mixedMoment B raw41171step0 raw41171step0Labels = mixedMoment B raw41171step1 raw41171step1Labels := by
      have ha : raw41171step1 = (fun i j => raw41171step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41171step1 raw41171step0; decide +kernel
      have hl : raw41171step1Labels = raw41171step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41171step0 raw41171step0Labels permutation32 permutation6
    mixedMoment B raw41171step1 raw41171step1Labels = mixedMoment B raw41171step2 raw41171step2Labels := by
      have ha : raw41171step2 = -raw41171step1 := by apply Matrix.ext; change ∀ i j, raw41171step2 i j = -(raw41171step1 i j); unfold raw41171step2 raw41171step1; decide +kernel
      have hl : raw41171step2Labels = raw41171step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node610 node610Labels := by rfl

def raw41172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41172step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw41172step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41172step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41172 raw41172Labels = mixedMoment B node599 node599Labels := by
  calc
    mixedMoment B raw41172 raw41172Labels = mixedMoment B raw41172step0 raw41172step0Labels := by
      have ha : raw41172step0 = (fun i j => raw41172 (permutation240 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41172step0 raw41172; decide +kernel
      have hl : raw41172step0Labels = raw41172Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41172 raw41172Labels permutation240 permutation6
    mixedMoment B raw41172step0 raw41172step0Labels = mixedMoment B raw41172step1 raw41172step1Labels := by
      have ha : raw41172step1 = -raw41172step0 := by apply Matrix.ext; change ∀ i j, raw41172step1 i j = -(raw41172step0 i j); unfold raw41172step1 raw41172step0; decide +kernel
      have hl : raw41172step1Labels = raw41172step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node599 node599Labels := by rfl

def raw41173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw41173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3]]
def raw41173step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]
def raw41173step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41173step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw41173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41173step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41173step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41173 raw41173Labels = mixedMoment B node611 node611Labels := by
  calc
    mixedMoment B raw41173 raw41173Labels = mixedMoment B raw41173step0 raw41173step0Labels := by
      have hz : ∀ j, raw41173 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41173step0 = (fun i j => raw41173 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41173step0 raw41173; decide +kernel
      have hl : raw41173step0Labels = raw41173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41173 raw41173Labels permutation520 hz
    mixedMoment B raw41173step0 raw41173step0Labels = mixedMoment B raw41173step1 raw41173step1Labels := by
      have hz : ∀ j, raw41173step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41173step1 = (fun i j => raw41173step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41173step1 raw41173step0; decide +kernel
      have hl : raw41173step1Labels = raw41173step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41173step0 raw41173step0Labels permutation104 hz
    mixedMoment B raw41173step1 raw41173step1Labels = mixedMoment B raw41173step2 raw41173step2Labels := by
      have ha : raw41173step2 = (fun i j => raw41173step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41173step2 raw41173step1; decide +kernel
      have hl : raw41173step2Labels = raw41173step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41173step1 raw41173step1Labels permutation8 permutation6
    mixedMoment B raw41173step2 raw41173step2Labels = mixedMoment B raw41173step3 raw41173step3Labels := by
      have ha : raw41173step3 = -raw41173step2 := by apply Matrix.ext; change ∀ i j, raw41173step3 i j = -(raw41173step2 i j); unfold raw41173step3 raw41173step2; decide +kernel
      have hl : raw41173step3Labels = raw41173step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node611 node611Labels := by rfl

def raw41174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw41174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1]]
def raw41174step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41174step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41174 raw41174Labels = mixedMoment B node603 node603Labels := by
  calc
    mixedMoment B raw41174 raw41174Labels = mixedMoment B raw41174step0 raw41174step0Labels := by
      have hz : ∀ j, raw41174 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41174step0 = (fun i j => raw41174 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41174step0 raw41174; decide +kernel
      have hl : raw41174step0Labels = raw41174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41174 raw41174Labels permutation434 hz
    mixedMoment B raw41174step0 raw41174step0Labels = mixedMoment B raw41174step1 raw41174step1Labels := by
      have ha : raw41174step1 = (fun i j => raw41174step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41174step1 raw41174step0; decide +kernel
      have hl : raw41174step1Labels = raw41174step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41174step0 raw41174step0Labels permutation50 permutation6
    mixedMoment B raw41174step1 raw41174step1Labels = mixedMoment B raw41174step2 raw41174step2Labels := by
      have ha : raw41174step2 = -raw41174step1 := by apply Matrix.ext; change ∀ i j, raw41174step2 i j = -(raw41174step1 i j); unfold raw41174step2 raw41174step1; decide +kernel
      have hl : raw41174step2Labels = raw41174step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node603 node603Labels := by rfl

def raw41175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw41175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw41175step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41175step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 0, 0], ![2, 2, -4]]
def raw41175step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41175step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![2, 2, -4]]
def raw41175step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41175step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-4, 2, 2]]
def raw41175step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41175step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw41175step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41175 raw41175Labels = mixedMoment B node615 node615Labels := by
  calc
    mixedMoment B raw41175 raw41175Labels = mixedMoment B raw41175step0 raw41175step0Labels := by
      have hz : ∀ j, raw41175 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41175step0 = (fun i j => raw41175 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41175step0 raw41175; decide +kernel
      have hl : raw41175step0Labels = raw41175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41175 raw41175Labels permutation520 hz
    mixedMoment B raw41175step0 raw41175step0Labels = mixedMoment B raw41175step1 raw41175step1Labels := by
      have hz : ∀ j, raw41175step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41175step1 = (fun i j => raw41175step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41175step1 raw41175step0; decide +kernel
      have hl : raw41175step1Labels = raw41175step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41175step0 raw41175step0Labels permutation104 hz
    mixedMoment B raw41175step1 raw41175step1Labels = mixedMoment B raw41175step2 raw41175step2Labels := by
      have hz : ∀ j, raw41175step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41175step2 = (fun i j => raw41175step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41175step2 raw41175step1; decide +kernel
      have hl : raw41175step2Labels = raw41175step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41175step1 raw41175step1Labels permutation20 hz
    mixedMoment B raw41175step2 raw41175step2Labels = mixedMoment B raw41175step3 raw41175step3Labels := by
      have ha : raw41175step3 = (fun i j => raw41175step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41175step3 raw41175step2; decide +kernel
      have hl : raw41175step3Labels = raw41175step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41175step2 raw41175step2Labels permutation2 permutation6
    mixedMoment B raw41175step3 raw41175step3Labels = mixedMoment B raw41175step4 raw41175step4Labels := by
      have ha : raw41175step4 = -raw41175step3 := by apply Matrix.ext; change ∀ i j, raw41175step4 i j = -(raw41175step3 i j); unfold raw41175step4 raw41175step3; decide +kernel
      have hl : raw41175step4Labels = raw41175step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node615 node615Labels := by rfl

def raw41176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1]]
def raw41176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1]]
def raw41176step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41176step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1]]
def raw41176step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41176step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw41176step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41176step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw41176step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41176 raw41176Labels = mixedMoment B node605 node605Labels := by
  calc
    mixedMoment B raw41176 raw41176Labels = mixedMoment B raw41176step0 raw41176step0Labels := by
      have hz : ∀ j, raw41176 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41176step0 = (fun i j => raw41176 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41176step0 raw41176; decide +kernel
      have hl : raw41176step0Labels = raw41176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41176 raw41176Labels permutation434 hz
    mixedMoment B raw41176step0 raw41176step0Labels = mixedMoment B raw41176step1 raw41176step1Labels := by
      have hz : ∀ j, raw41176step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41176step1 = (fun i j => raw41176step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41176step1 raw41176step0; decide +kernel
      have hl : raw41176step1Labels = raw41176step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41176step0 raw41176step0Labels permutation80 hz
    mixedMoment B raw41176step1 raw41176step1Labels = mixedMoment B raw41176step2 raw41176step2Labels := by
      have ha : raw41176step2 = (fun i j => raw41176step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41176step2 raw41176step1; decide +kernel
      have hl : raw41176step2Labels = raw41176step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41176step1 raw41176step1Labels permutation12 permutation6
    mixedMoment B raw41176step2 raw41176step2Labels = mixedMoment B raw41176step3 raw41176step3Labels := by
      have ha : raw41176step3 = -raw41176step2 := by apply Matrix.ext; change ∀ i j, raw41176step3 i j = -(raw41176step2 i j); unfold raw41176step3 raw41176step2; decide +kernel
      have hl : raw41176step3Labels = raw41176step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node605 node605Labels := by rfl

def raw41177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2]]
def raw41177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2]]
def raw41177step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41177step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]
def raw41177step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41177step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw41177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41177step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41177step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41177 raw41177Labels = mixedMoment B node614 node614Labels := by
  calc
    mixedMoment B raw41177 raw41177Labels = mixedMoment B raw41177step0 raw41177step0Labels := by
      have hz : ∀ j, raw41177 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41177step0 = (fun i j => raw41177 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41177step0 raw41177; decide +kernel
      have hl : raw41177step0Labels = raw41177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41177 raw41177Labels permutation434 hz
    mixedMoment B raw41177step0 raw41177step0Labels = mixedMoment B raw41177step1 raw41177step1Labels := by
      have hz : ∀ j, raw41177step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41177step1 = (fun i j => raw41177step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41177step1 raw41177step0; decide +kernel
      have hl : raw41177step1Labels = raw41177step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41177step0 raw41177step0Labels permutation80 hz
    mixedMoment B raw41177step1 raw41177step1Labels = mixedMoment B raw41177step2 raw41177step2Labels := by
      have ha : raw41177step2 = (fun i j => raw41177step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41177step2 raw41177step1; decide +kernel
      have hl : raw41177step2Labels = raw41177step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41177step1 raw41177step1Labels permutation8 permutation6
    mixedMoment B raw41177step2 raw41177step2Labels = mixedMoment B raw41177step3 raw41177step3Labels := by
      have ha : raw41177step3 = -raw41177step2 := by apply Matrix.ext; change ∀ i j, raw41177step3 i j = -(raw41177step2 i j); unfold raw41177step3 raw41177step2; decide +kernel
      have hl : raw41177step3Labels = raw41177step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node614 node614Labels := by rfl

def raw41178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 3, -5]]
def raw41178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 3, -5]]
def raw41178step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41178step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 0, 0], ![0, 0, 0], ![2, 3, -5]]
def raw41178step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41178step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 0, 0], ![2, 3, -5]]
def raw41178step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41178step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, -3, 5], ![2, 3, -5]]
def raw41178step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41178step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def raw41178step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41178 raw41178Labels = mixedMoment B node622 node622Labels := by
  calc
    mixedMoment B raw41178 raw41178Labels = mixedMoment B raw41178step0 raw41178step0Labels := by
      have hz : ∀ j, raw41178 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41178step0 = (fun i j => raw41178 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41178step0 raw41178; decide +kernel
      have hl : raw41178step0Labels = raw41178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41178 raw41178Labels permutation520 hz
    mixedMoment B raw41178step0 raw41178step0Labels = mixedMoment B raw41178step1 raw41178step1Labels := by
      have hz : ∀ j, raw41178step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41178step1 = (fun i j => raw41178step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41178step1 raw41178step0; decide +kernel
      have hl : raw41178step1Labels = raw41178step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41178step0 raw41178step0Labels permutation104 hz
    mixedMoment B raw41178step1 raw41178step1Labels = mixedMoment B raw41178step2 raw41178step2Labels := by
      have hz : ∀ j, raw41178step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41178step2 = (fun i j => raw41178step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41178step2 raw41178step1; decide +kernel
      have hl : raw41178step2Labels = raw41178step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41178step1 raw41178step1Labels permutation20 hz
    mixedMoment B raw41178step2 raw41178step2Labels = mixedMoment B raw41178step3 raw41178step3Labels := by
      have hz : ∀ j, raw41178step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw41178step3 = (fun i j => raw41178step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw41178step3 raw41178step2; decide +kernel
      have hl : raw41178step3Labels = raw41178step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41178step2 raw41178step2Labels permutation4 hz
    mixedMoment B raw41178step3 raw41178step3Labels = mixedMoment B raw41178step4 raw41178step4Labels := by
      have ha : raw41178step4 = (fun i j => raw41178step3 (permutation1 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41178step4 raw41178step3; decide +kernel
      have hl : raw41178step4Labels = raw41178step3Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41178step3 raw41178step3Labels permutation1 permutation6
    _ = mixedMoment B node622 node622Labels := by rfl

def raw41179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2]]
def raw41179Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2]]
def raw41179step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41179step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -3, 5], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2]]
def raw41179step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41179step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -3, 5], ![1, 2, -3], ![1, 1, -2]]
def raw41179step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41179step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-2, 1, 1], ![-3, 1, 2]]
def raw41179step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41179step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw41179step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41179 raw41179Labels = mixedMoment B node619 node619Labels := by
  calc
    mixedMoment B raw41179 raw41179Labels = mixedMoment B raw41179step0 raw41179step0Labels := by
      have hz : ∀ j, raw41179 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41179step0 = (fun i j => raw41179 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41179step0 raw41179; decide +kernel
      have hl : raw41179step0Labels = raw41179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41179 raw41179Labels permutation434 hz
    mixedMoment B raw41179step0 raw41179step0Labels = mixedMoment B raw41179step1 raw41179step1Labels := by
      have hz : ∀ j, raw41179step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41179step1 = (fun i j => raw41179step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41179step1 raw41179step0; decide +kernel
      have hl : raw41179step1Labels = raw41179step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41179step0 raw41179step0Labels permutation80 hz
    mixedMoment B raw41179step1 raw41179step1Labels = mixedMoment B raw41179step2 raw41179step2Labels := by
      have hz : ∀ j, raw41179step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41179step2 = (fun i j => raw41179step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41179step2 raw41179step1; decide +kernel
      have hl : raw41179step2Labels = raw41179step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41179step1 raw41179step1Labels permutation14 hz
    mixedMoment B raw41179step2 raw41179step2Labels = mixedMoment B raw41179step3 raw41179step3Labels := by
      have ha : raw41179step3 = (fun i j => raw41179step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41179step3 raw41179step2; decide +kernel
      have hl : raw41179step3Labels = raw41179step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41179step2 raw41179step2Labels permutation3 permutation6
    mixedMoment B raw41179step3 raw41179step3Labels = mixedMoment B raw41179step4 raw41179step4Labels := by
      have ha : raw41179step4 = -raw41179step3 := by apply Matrix.ext; change ∀ i j, raw41179step4 i j = -(raw41179step3 i j); unfold raw41179step4 raw41179step3; decide +kernel
      have hl : raw41179step4Labels = raw41179step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node619 node619Labels := by rfl

def raw41180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw41180Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -2, -1]]
def raw41180step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw41180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41180step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41180 raw41180Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw41180 raw41180Labels = mixedMoment B raw41180step0 raw41180step0Labels := by
      have hz : ∀ j, raw41180 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41180step0 = (fun i j => raw41180 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41180step0 raw41180; decide +kernel
      have hl : raw41180step0Labels = raw41180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41180 raw41180Labels permutation434 hz
    mixedMoment B raw41180step0 raw41180step0Labels = mixedMoment B raw41180step1 raw41180step1Labels := by
      have ha : raw41180step1 = (fun i j => raw41180step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41180step1 raw41180step0; decide +kernel
      have hl : raw41180step1Labels = raw41180step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41180step0 raw41180step0Labels permutation149 permutation3
    mixedMoment B raw41180step1 raw41180step1Labels = mixedMoment B raw41180step2 raw41180step2Labels := by
      have ha : raw41180step2 = -raw41180step1 := by apply Matrix.ext; change ∀ i j, raw41180step2 i j = -(raw41180step1 i j); unfold raw41180step2 raw41180step1; decide +kernel
      have hl : raw41180step2Labels = raw41180step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2738 node2738Labels := by rfl

def raw41181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw41181Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![3, -1, -2]]
def raw41181step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw41181step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41181step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41181step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41181 raw41181Labels = mixedMoment B node3050 node3050Labels := by
  calc
    mixedMoment B raw41181 raw41181Labels = mixedMoment B raw41181step0 raw41181step0Labels := by
      have hz : ∀ j, raw41181 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41181step0 = (fun i j => raw41181 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41181step0 raw41181; decide +kernel
      have hl : raw41181step0Labels = raw41181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41181 raw41181Labels permutation434 hz
    mixedMoment B raw41181step0 raw41181step0Labels = mixedMoment B raw41181step1 raw41181step1Labels := by
      have ha : raw41181step1 = (fun i j => raw41181step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41181step1 raw41181step0; decide +kernel
      have hl : raw41181step1Labels = raw41181step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41181step0 raw41181step0Labels permutation149 permutation3
    mixedMoment B raw41181step1 raw41181step1Labels = mixedMoment B raw41181step2 raw41181step2Labels := by
      have ha : raw41181step2 = -raw41181step1 := by apply Matrix.ext; change ∀ i j, raw41181step2 i j = -(raw41181step1 i j); unfold raw41181step2 raw41181step1; decide +kernel
      have hl : raw41181step2Labels = raw41181step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3050 node3050Labels := by rfl

def raw41182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41182Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0]]
def raw41182step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41182step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41182 raw41182Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw41182 raw41182Labels = mixedMoment B raw41182step0 raw41182step0Labels := by
      have hz : ∀ j, raw41182 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41182step0 = (fun i j => raw41182 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41182step0 raw41182; decide +kernel
      have hl : raw41182step0Labels = raw41182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41182 raw41182Labels permutation434 hz
    mixedMoment B raw41182step0 raw41182step0Labels = mixedMoment B raw41182step1 raw41182step1Labels := by
      have ha : raw41182step1 = (fun i j => raw41182step0 (permutation48 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41182step1 raw41182step0; decide +kernel
      have hl : raw41182step1Labels = raw41182step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41182step0 raw41182step0Labels permutation48 permutation6
    _ = mixedMoment B node3625 node3625Labels := by rfl

def raw41183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41183Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1]]
def raw41183step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41183step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41183 raw41183Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw41183 raw41183Labels = mixedMoment B raw41183step0 raw41183step0Labels := by
      have hz : ∀ j, raw41183 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41183step0 = (fun i j => raw41183 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41183step0 raw41183; decide +kernel
      have hl : raw41183step0Labels = raw41183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41183 raw41183Labels permutation434 hz
    mixedMoment B raw41183step0 raw41183step0Labels = mixedMoment B raw41183step1 raw41183step1Labels := by
      have ha : raw41183step1 = (fun i j => raw41183step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41183step1 raw41183step0; decide +kernel
      have hl : raw41183step1Labels = raw41183step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41183step0 raw41183step0Labels permutation50 permutation6
    _ = mixedMoment B node3580 node3580Labels := by rfl

def raw41184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw41184Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41184step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw41184step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41184step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41184 raw41184Labels = mixedMoment B node3073 node3073Labels := by
  calc
    mixedMoment B raw41184 raw41184Labels = mixedMoment B raw41184step0 raw41184step0Labels := by
      have ha : raw41184step0 = (fun i j => raw41184 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41184step0 raw41184; decide +kernel
      have hl : raw41184step0Labels = raw41184Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41184 raw41184Labels permutation662 permutation3
    mixedMoment B raw41184step0 raw41184step0Labels = mixedMoment B raw41184step1 raw41184step1Labels := by
      have ha : raw41184step1 = -raw41184step0 := by apply Matrix.ext; change ∀ i j, raw41184step1 i j = -(raw41184step0 i j); unfold raw41184step1 raw41184step0; decide +kernel
      have hl : raw41184step1Labels = raw41184step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3073 node3073Labels := by rfl

def raw41185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41185Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41185step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41185step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41185 raw41185Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw41185 raw41185Labels = mixedMoment B raw41185step0 raw41185step0Labels := by
      have ha : raw41185step0 = (fun i j => raw41185 (permutation260 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41185step0 raw41185; decide +kernel
      have hl : raw41185step0Labels = raw41185Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41185 raw41185Labels permutation260 permutation6
    _ = mixedMoment B node3571 node3571Labels := by rfl

def raw41186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41186Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41186step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41186step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41186 raw41186Labels = mixedMoment B node3388 node3388Labels := by
  calc
    mixedMoment B raw41186 raw41186Labels = mixedMoment B raw41186step0 raw41186step0Labels := by
      have ha : raw41186step0 = (fun i j => raw41186 (permutation246 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41186step0 raw41186; decide +kernel
      have hl : raw41186step0Labels = raw41186Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41186 raw41186Labels permutation246 permutation6
    _ = mixedMoment B node3388 node3388Labels := by rfl

def raw41187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41187Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41187step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41187 raw41187Labels = mixedMoment B node3375 node3375Labels := by
  calc
    mixedMoment B raw41187 raw41187Labels = mixedMoment B raw41187step0 raw41187step0Labels := by
      have ha : raw41187step0 = (fun i j => raw41187 (permutation260 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41187step0 raw41187; decide +kernel
      have hl : raw41187step0Labels = raw41187Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41187 raw41187Labels permutation260 permutation6
    _ = mixedMoment B node3375 node3375Labels := by rfl

def raw41188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw41188Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![3, -2, -1]]
def raw41188step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41188step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![3, -2, -1]]
def raw41188step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41188step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3]]
def raw41188step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41188step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw41188step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41188 raw41188Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw41188 raw41188Labels = mixedMoment B raw41188step0 raw41188step0Labels := by
      have hz : ∀ j, raw41188 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41188step0 = (fun i j => raw41188 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41188step0 raw41188; decide +kernel
      have hl : raw41188step0Labels = raw41188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41188 raw41188Labels permutation520 hz
    mixedMoment B raw41188step0 raw41188step0Labels = mixedMoment B raw41188step1 raw41188step1Labels := by
      have hz : ∀ j, raw41188step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41188step1 = (fun i j => raw41188step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41188step1 raw41188step0; decide +kernel
      have hl : raw41188step1Labels = raw41188step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41188step0 raw41188step0Labels permutation104 hz
    mixedMoment B raw41188step1 raw41188step1Labels = mixedMoment B raw41188step2 raw41188step2Labels := by
      have ha : raw41188step2 = (fun i j => raw41188step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41188step2 raw41188step1; decide +kernel
      have hl : raw41188step2Labels = raw41188step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41188step1 raw41188step1Labels permutation31 permutation3
    mixedMoment B raw41188step2 raw41188step2Labels = mixedMoment B raw41188step3 raw41188step3Labels := by
      have ha : raw41188step3 = -raw41188step2 := by apply Matrix.ext; change ∀ i j, raw41188step3 i j = -(raw41188step2 i j); unfold raw41188step3 raw41188step2; decide +kernel
      have hl : raw41188step3Labels = raw41188step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2781 node2781Labels := by rfl

def raw41189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw41189Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![3, -1, -2]]
def raw41189step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3]]
def raw41189step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw41189step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41189 raw41189Labels = mixedMoment B node3096 node3096Labels := by
  calc
    mixedMoment B raw41189 raw41189Labels = mixedMoment B raw41189step0 raw41189step0Labels := by
      have hz : ∀ j, raw41189 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41189step0 = (fun i j => raw41189 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41189step0 raw41189; decide +kernel
      have hl : raw41189step0Labels = raw41189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41189 raw41189Labels permutation434 hz
    mixedMoment B raw41189step0 raw41189step0Labels = mixedMoment B raw41189step1 raw41189step1Labels := by
      have ha : raw41189step1 = (fun i j => raw41189step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41189step1 raw41189step0; decide +kernel
      have hl : raw41189step1Labels = raw41189step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41189step0 raw41189step0Labels permutation151 permutation3
    mixedMoment B raw41189step1 raw41189step1Labels = mixedMoment B raw41189step2 raw41189step2Labels := by
      have ha : raw41189step2 = -raw41189step1 := by apply Matrix.ext; change ∀ i j, raw41189step2 i j = -(raw41189step1 i j); unfold raw41189step2 raw41189step1; decide +kernel
      have hl : raw41189step2Labels = raw41189step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3096 node3096Labels := by rfl

def raw41190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw41190Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1]]
def raw41190step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41190step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41190 raw41190Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw41190 raw41190Labels = mixedMoment B raw41190step0 raw41190step0Labels := by
      have hz : ∀ j, raw41190 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41190step0 = (fun i j => raw41190 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41190step0 raw41190; decide +kernel
      have hl : raw41190step0Labels = raw41190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41190 raw41190Labels permutation434 hz
    mixedMoment B raw41190step0 raw41190step0Labels = mixedMoment B raw41190step1 raw41190step1Labels := by
      have ha : raw41190step1 = (fun i j => raw41190step0 (permutation54 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41190step1 raw41190step0; decide +kernel
      have hl : raw41190step1Labels = raw41190step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41190step0 raw41190step0Labels permutation54 permutation6
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw41191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw41191Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 0, -2]]
def raw41191step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41191step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41191 raw41191Labels = mixedMoment B node3392 node3392Labels := by
  calc
    mixedMoment B raw41191 raw41191Labels = mixedMoment B raw41191step0 raw41191step0Labels := by
      have hz : ∀ j, raw41191 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41191step0 = (fun i j => raw41191 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41191step0 raw41191; decide +kernel
      have hl : raw41191step0Labels = raw41191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41191 raw41191Labels permutation434 hz
    mixedMoment B raw41191step0 raw41191step0Labels = mixedMoment B raw41191step1 raw41191step1Labels := by
      have ha : raw41191step1 = (fun i j => raw41191step0 (permutation51 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41191step1 raw41191step0; decide +kernel
      have hl : raw41191step1Labels = raw41191step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41191step0 raw41191step0Labels permutation51 permutation6
    _ = mixedMoment B node3392 node3392Labels := by rfl

def raw41192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41192Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw41192step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41192 raw41192Labels = mixedMoment B node3376 node3376Labels := by
  calc
    mixedMoment B raw41192 raw41192Labels = mixedMoment B raw41192step0 raw41192step0Labels := by
      have ha : raw41192step0 = (fun i j => raw41192 (permutation261 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41192step0 raw41192; decide +kernel
      have hl : raw41192step0Labels = raw41192Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41192 raw41192Labels permutation261 permutation6
    _ = mixedMoment B node3376 node3376Labels := by rfl

def raw41193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw41193Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![3, -1, -2]]
def raw41193step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41193step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -2, 3], ![3, -1, -2]]
def raw41193step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41193step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 3, -1], ![-2, -1, 3]]
def raw41193step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41193step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw41193step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41193 raw41193Labels = mixedMoment B node2603 node2603Labels := by
  calc
    mixedMoment B raw41193 raw41193Labels = mixedMoment B raw41193step0 raw41193step0Labels := by
      have hz : ∀ j, raw41193 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41193step0 = (fun i j => raw41193 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41193step0 raw41193; decide +kernel
      have hl : raw41193step0Labels = raw41193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41193 raw41193Labels permutation520 hz
    mixedMoment B raw41193step0 raw41193step0Labels = mixedMoment B raw41193step1 raw41193step1Labels := by
      have hz : ∀ j, raw41193step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41193step1 = (fun i j => raw41193step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41193step1 raw41193step0; decide +kernel
      have hl : raw41193step1Labels = raw41193step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41193step0 raw41193step0Labels permutation104 hz
    mixedMoment B raw41193step1 raw41193step1Labels = mixedMoment B raw41193step2 raw41193step2Labels := by
      have ha : raw41193step2 = (fun i j => raw41193step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41193step2 raw41193step1; decide +kernel
      have hl : raw41193step2Labels = raw41193step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41193step1 raw41193step1Labels permutation23 permutation6
    mixedMoment B raw41193step2 raw41193step2Labels = mixedMoment B raw41193step3 raw41193step3Labels := by
      have ha : raw41193step3 = -raw41193step2 := by apply Matrix.ext; change ∀ i j, raw41193step3 i j = -(raw41193step2 i j); unfold raw41193step3 raw41193step2; decide +kernel
      have hl : raw41193step3Labels = raw41193step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2603 node2603Labels := by rfl

def raw41194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41194Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 0, -2]]
def raw41194step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw41194step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw41194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41194 raw41194Labels = mixedMoment B node2560 node2560Labels := by
  calc
    mixedMoment B raw41194 raw41194Labels = mixedMoment B raw41194step0 raw41194step0Labels := by
      have hz : ∀ j, raw41194 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41194step0 = (fun i j => raw41194 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41194step0 raw41194; decide +kernel
      have hl : raw41194step0Labels = raw41194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41194 raw41194Labels permutation434 hz
    mixedMoment B raw41194step0 raw41194step0Labels = mixedMoment B raw41194step1 raw41194step1Labels := by
      have ha : raw41194step1 = (fun i j => raw41194step0 (permutation89 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41194step1 raw41194step0; decide +kernel
      have hl : raw41194step1Labels = raw41194step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41194step0 raw41194step0Labels permutation89 permutation6
    mixedMoment B raw41194step1 raw41194step1Labels = mixedMoment B raw41194step2 raw41194step2Labels := by
      have ha : raw41194step2 = -raw41194step1 := by apply Matrix.ext; change ∀ i j, raw41194step2 i j = -(raw41194step1 i j); unfold raw41194step2 raw41194step1; decide +kernel
      have hl : raw41194step2Labels = raw41194step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2560 node2560Labels := by rfl

def raw41195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw41195Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw41195step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41195step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41195 raw41195Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw41195 raw41195Labels = mixedMoment B raw41195step0 raw41195step0Labels := by
      have hz : ∀ j, raw41195 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41195step0 = (fun i j => raw41195 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41195step0 raw41195; decide +kernel
      have hl : raw41195step0Labels = raw41195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41195 raw41195Labels permutation346 hz
    mixedMoment B raw41195step0 raw41195step0Labels = mixedMoment B raw41195step1 raw41195step1Labels := by
      have ha : raw41195step1 = (fun i j => raw41195step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41195step1 raw41195step0; decide +kernel
      have hl : raw41195step1Labels = raw41195step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41195step0 raw41195step0Labels permutation50 permutation6
    _ = mixedMoment B node3581 node3581Labels := by rfl

def raw41196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw41196Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw41196step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41196step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41196 raw41196Labels = mixedMoment B node3391 node3391Labels := by
  calc
    mixedMoment B raw41196 raw41196Labels = mixedMoment B raw41196step0 raw41196step0Labels := by
      have hz : ∀ j, raw41196 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41196step0 = (fun i j => raw41196 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41196step0 raw41196; decide +kernel
      have hl : raw41196step0Labels = raw41196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41196 raw41196Labels permutation346 hz
    mixedMoment B raw41196step0 raw41196step0Labels = mixedMoment B raw41196step1 raw41196step1Labels := by
      have ha : raw41196step1 = (fun i j => raw41196step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41196step1 raw41196step0; decide +kernel
      have hl : raw41196step1Labels = raw41196step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41196step0 raw41196step0Labels permutation50 permutation6
    _ = mixedMoment B node3391 node3391Labels := by rfl

def raw41197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw41197Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw41197step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41197step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41197 raw41197Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw41197 raw41197Labels = mixedMoment B raw41197step0 raw41197step0Labels := by
      have hz : ∀ j, raw41197 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41197step0 = (fun i j => raw41197 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41197step0 raw41197; decide +kernel
      have hl : raw41197step0Labels = raw41197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41197 raw41197Labels permutation346 hz
    mixedMoment B raw41197step0 raw41197step0Labels = mixedMoment B raw41197step1 raw41197step1Labels := by
      have ha : raw41197step1 = (fun i j => raw41197step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41197step1 raw41197step0; decide +kernel
      have hl : raw41197step1Labels = raw41197step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41197step0 raw41197step0Labels permutation44 permutation6
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw41198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw41198Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw41198step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw41198step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41198 raw41198Labels = mixedMoment B node3622 node3622Labels := by
  calc
    mixedMoment B raw41198 raw41198Labels = mixedMoment B raw41198step0 raw41198step0Labels := by
      have hz : ∀ j, raw41198 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41198step0 = (fun i j => raw41198 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41198step0 raw41198; decide +kernel
      have hl : raw41198step0Labels = raw41198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41198 raw41198Labels permutation346 hz
    mixedMoment B raw41198step0 raw41198step0Labels = mixedMoment B raw41198step1 raw41198step1Labels := by
      have ha : raw41198step1 = (fun i j => raw41198step0 (permutation48 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41198step1 raw41198step0; decide +kernel
      have hl : raw41198step1Labels = raw41198step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41198step0 raw41198step0Labels permutation48 permutation6
    _ = mixedMoment B node3622 node3622Labels := by rfl

def raw41199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw41199Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw41199step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41199step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41199 raw41199Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw41199 raw41199Labels = mixedMoment B raw41199step0 raw41199step0Labels := by
      have hz : ∀ j, raw41199 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41199step0 = (fun i j => raw41199 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41199step0 raw41199; decide +kernel
      have hl : raw41199step0Labels = raw41199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41199 raw41199Labels permutation346 hz
    mixedMoment B raw41199step0 raw41199step0Labels = mixedMoment B raw41199step1 raw41199step1Labels := by
      have ha : raw41199step1 = (fun i j => raw41199step0 (permutation48 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41199step1 raw41199step0; decide +kernel
      have hl : raw41199step1Labels = raw41199step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41199step0 raw41199step0Labels permutation48 permutation6
    _ = mixedMoment B node3533 node3533Labels := by rfl

def raw41200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw41200Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41200step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41200 raw41200Labels = mixedMoment B node3390 node3390Labels := by
  calc
    mixedMoment B raw41200 raw41200Labels = mixedMoment B raw41200step0 raw41200step0Labels := by
      have ha : raw41200step0 = (fun i j => raw41200 (permutation246 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41200step0 raw41200; decide +kernel
      have hl : raw41200step0Labels = raw41200Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41200 raw41200Labels permutation246 permutation6
    _ = mixedMoment B node3390 node3390Labels := by rfl

def raw41201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw41201Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41201 raw41201Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw41201 raw41201Labels = mixedMoment B raw41201step0 raw41201step0Labels := by
      have ha : raw41201step0 = (fun i j => raw41201 (permutation240 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41201step0 raw41201; decide +kernel
      have hl : raw41201step0Labels = raw41201Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41201 raw41201Labels permutation240 permutation6
    _ = mixedMoment B node3532 node3532Labels := by rfl

def raw41202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw41202Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![3, -1, -2]]
def raw41202step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41202step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2], ![3, -1, -2]]
def raw41202step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41202step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![-1, 2, -1], ![-1, 2, -1], ![-1, -2, 3]]
def raw41202step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41202step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -2, 1], ![1, 2, -3]]
def raw41202step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41202 raw41202Labels = mixedMoment B node3118 node3118Labels := by
  calc
    mixedMoment B raw41202 raw41202Labels = mixedMoment B raw41202step0 raw41202step0Labels := by
      have hz : ∀ j, raw41202 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41202step0 = (fun i j => raw41202 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41202step0 raw41202; decide +kernel
      have hl : raw41202step0Labels = raw41202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41202 raw41202Labels permutation520 hz
    mixedMoment B raw41202step0 raw41202step0Labels = mixedMoment B raw41202step1 raw41202step1Labels := by
      have hz : ∀ j, raw41202step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41202step1 = (fun i j => raw41202step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41202step1 raw41202step0; decide +kernel
      have hl : raw41202step1Labels = raw41202step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41202step0 raw41202step0Labels permutation104 hz
    mixedMoment B raw41202step1 raw41202step1Labels = mixedMoment B raw41202step2 raw41202step2Labels := by
      have ha : raw41202step2 = (fun i j => raw41202step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41202step2 raw41202step1; decide +kernel
      have hl : raw41202step2Labels = raw41202step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41202step1 raw41202step1Labels permutation29 permutation3
    mixedMoment B raw41202step2 raw41202step2Labels = mixedMoment B raw41202step3 raw41202step3Labels := by
      have ha : raw41202step3 = -raw41202step2 := by apply Matrix.ext; change ∀ i j, raw41202step3 i j = -(raw41202step2 i j); unfold raw41202step3 raw41202step2; decide +kernel
      have hl : raw41202step3Labels = raw41202step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3118 node3118Labels := by rfl

def raw41203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw41203Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41203step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41203step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41203 raw41203Labels = mixedMoment B node3380 node3380Labels := by
  calc
    mixedMoment B raw41203 raw41203Labels = mixedMoment B raw41203step0 raw41203step0Labels := by
      have hz : ∀ j, raw41203 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41203step0 = (fun i j => raw41203 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41203step0 raw41203; decide +kernel
      have hl : raw41203step0Labels = raw41203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41203 raw41203Labels permutation434 hz
    mixedMoment B raw41203step0 raw41203step0Labels = mixedMoment B raw41203step1 raw41203step1Labels := by
      have ha : raw41203step1 = (fun i j => raw41203step0 (permutation54 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41203step1 raw41203step0; decide +kernel
      have hl : raw41203step1Labels = raw41203step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41203step0 raw41203step0Labels permutation54 permutation6
    _ = mixedMoment B node3380 node3380Labels := by rfl

def raw41204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw41204Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw41204step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41204step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0]]
def raw41204step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41204step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![2, -2, 0]]
def raw41204step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41204step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw41204step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41204 raw41204Labels = mixedMoment B node3633 node3633Labels := by
  calc
    mixedMoment B raw41204 raw41204Labels = mixedMoment B raw41204step0 raw41204step0Labels := by
      have hz : ∀ j, raw41204 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41204step0 = (fun i j => raw41204 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41204step0 raw41204; decide +kernel
      have hl : raw41204step0Labels = raw41204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41204 raw41204Labels permutation520 hz
    mixedMoment B raw41204step0 raw41204step0Labels = mixedMoment B raw41204step1 raw41204step1Labels := by
      have hz : ∀ j, raw41204step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41204step1 = (fun i j => raw41204step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41204step1 raw41204step0; decide +kernel
      have hl : raw41204step1Labels = raw41204step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41204step0 raw41204step0Labels permutation104 hz
    mixedMoment B raw41204step1 raw41204step1Labels = mixedMoment B raw41204step2 raw41204step2Labels := by
      have hz : ∀ j, raw41204step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41204step2 = (fun i j => raw41204step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41204step2 raw41204step1; decide +kernel
      have hl : raw41204step2Labels = raw41204step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41204step1 raw41204step1Labels permutation20 hz
    mixedMoment B raw41204step2 raw41204step2Labels = mixedMoment B raw41204step3 raw41204step3Labels := by
      have ha : raw41204step3 = (fun i j => raw41204step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41204step3 raw41204step2; decide +kernel
      have hl : raw41204step3Labels = raw41204step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41204step2 raw41204step2Labels permutation3 permutation6
    _ = mixedMoment B node3633 node3633Labels := by rfl

def raw41205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw41205Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw41205step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1]]
def raw41205step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41205step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41205step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41205 raw41205Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw41205 raw41205Labels = mixedMoment B raw41205step0 raw41205step0Labels := by
      have hz : ∀ j, raw41205 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41205step0 = (fun i j => raw41205 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41205step0 raw41205; decide +kernel
      have hl : raw41205step0Labels = raw41205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41205 raw41205Labels permutation434 hz
    mixedMoment B raw41205step0 raw41205step0Labels = mixedMoment B raw41205step1 raw41205step1Labels := by
      have hz : ∀ j, raw41205step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41205step1 = (fun i j => raw41205step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41205step1 raw41205step0; decide +kernel
      have hl : raw41205step1Labels = raw41205step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41205step0 raw41205step0Labels permutation80 hz
    mixedMoment B raw41205step1 raw41205step1Labels = mixedMoment B raw41205step2 raw41205step2Labels := by
      have ha : raw41205step2 = (fun i j => raw41205step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41205step2 raw41205step1; decide +kernel
      have hl : raw41205step2Labels = raw41205step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41205step1 raw41205step1Labels permutation13 permutation6
    _ = mixedMoment B node3583 node3583Labels := by rfl

def raw41206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw41206Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw41206step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41206step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, -2, 2], ![2, 0, -2]]
def raw41206step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41206step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41206step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41206 raw41206Labels = mixedMoment B node3397 node3397Labels := by
  calc
    mixedMoment B raw41206 raw41206Labels = mixedMoment B raw41206step0 raw41206step0Labels := by
      have hz : ∀ j, raw41206 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41206step0 = (fun i j => raw41206 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41206step0 raw41206; decide +kernel
      have hl : raw41206step0Labels = raw41206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41206 raw41206Labels permutation434 hz
    mixedMoment B raw41206step0 raw41206step0Labels = mixedMoment B raw41206step1 raw41206step1Labels := by
      have hz : ∀ j, raw41206step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41206step1 = (fun i j => raw41206step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41206step1 raw41206step0; decide +kernel
      have hl : raw41206step1Labels = raw41206step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41206step0 raw41206step0Labels permutation80 hz
    mixedMoment B raw41206step1 raw41206step1Labels = mixedMoment B raw41206step2 raw41206step2Labels := by
      have ha : raw41206step2 = (fun i j => raw41206step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41206step2 raw41206step1; decide +kernel
      have hl : raw41206step2Labels = raw41206step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41206step1 raw41206step1Labels permutation12 permutation6
    _ = mixedMoment B node3397 node3397Labels := by rfl

def raw41207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw41207Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1]]
def raw41207step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41207step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![1, 0, -1], ![1, -2, 1]]
def raw41207step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41207step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw41207step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41207 raw41207Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw41207 raw41207Labels = mixedMoment B raw41207step0 raw41207step0Labels := by
      have hz : ∀ j, raw41207 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41207step0 = (fun i j => raw41207 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41207step0 raw41207; decide +kernel
      have hl : raw41207step0Labels = raw41207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41207 raw41207Labels permutation434 hz
    mixedMoment B raw41207step0 raw41207step0Labels = mixedMoment B raw41207step1 raw41207step1Labels := by
      have hz : ∀ j, raw41207step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41207step1 = (fun i j => raw41207step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41207step1 raw41207step0; decide +kernel
      have hl : raw41207step1Labels = raw41207step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41207step0 raw41207step0Labels permutation80 hz
    mixedMoment B raw41207step1 raw41207step1Labels = mixedMoment B raw41207step2 raw41207step2Labels := by
      have ha : raw41207step2 = (fun i j => raw41207step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41207step2 raw41207step1; decide +kernel
      have hl : raw41207step2Labels = raw41207step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41207step1 raw41207step1Labels permutation11 permutation6
    _ = mixedMoment B node3548 node3548Labels := by rfl

def raw41208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41208Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41208step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41208step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0]]
def raw41208step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41208step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw41208step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41208 raw41208Labels = mixedMoment B node3623 node3623Labels := by
  calc
    mixedMoment B raw41208 raw41208Labels = mixedMoment B raw41208step0 raw41208step0Labels := by
      have hz : ∀ j, raw41208 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41208step0 = (fun i j => raw41208 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41208step0 raw41208; decide +kernel
      have hl : raw41208step0Labels = raw41208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41208 raw41208Labels permutation434 hz
    mixedMoment B raw41208step0 raw41208step0Labels = mixedMoment B raw41208step1 raw41208step1Labels := by
      have hz : ∀ j, raw41208step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41208step1 = (fun i j => raw41208step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41208step1 raw41208step0; decide +kernel
      have hl : raw41208step1Labels = raw41208step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41208step0 raw41208step0Labels permutation80 hz
    mixedMoment B raw41208step1 raw41208step1Labels = mixedMoment B raw41208step2 raw41208step2Labels := by
      have ha : raw41208step2 = (fun i j => raw41208step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41208step2 raw41208step1; decide +kernel
      have hl : raw41208step2Labels = raw41208step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41208step1 raw41208step1Labels permutation11 permutation6
    _ = mixedMoment B node3623 node3623Labels := by rfl

def raw41209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw41209Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw41209step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41209step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41209 raw41209Labels = mixedMoment B node3394 node3394Labels := by
  calc
    mixedMoment B raw41209 raw41209Labels = mixedMoment B raw41209step0 raw41209step0Labels := by
      have hz : ∀ j, raw41209 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41209step0 = (fun i j => raw41209 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41209step0 raw41209; decide +kernel
      have hl : raw41209step0Labels = raw41209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41209 raw41209Labels permutation346 hz
    mixedMoment B raw41209step0 raw41209step0Labels = mixedMoment B raw41209step1 raw41209step1Labels := by
      have ha : raw41209step1 = (fun i j => raw41209step0 (permutation53 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41209step1 raw41209step0; decide +kernel
      have hl : raw41209step1Labels = raw41209step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41209step0 raw41209step0Labels permutation53 permutation6
    _ = mixedMoment B node3394 node3394Labels := by rfl

def raw41210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw41210Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw41210step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41210step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41210 raw41210Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw41210 raw41210Labels = mixedMoment B raw41210step0 raw41210step0Labels := by
      have hz : ∀ j, raw41210 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41210step0 = (fun i j => raw41210 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41210step0 raw41210; decide +kernel
      have hl : raw41210step0Labels = raw41210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41210 raw41210Labels permutation346 hz
    mixedMoment B raw41210step0 raw41210step0Labels = mixedMoment B raw41210step1 raw41210step1Labels := by
      have ha : raw41210step1 = (fun i j => raw41210step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41210step1 raw41210step0; decide +kernel
      have hl : raw41210step1Labels = raw41210step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41210step0 raw41210step0Labels permutation49 permutation6
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw41211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41211Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41211step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41211 raw41211Labels = mixedMoment B node3496 node3496Labels := by
  calc
    mixedMoment B raw41211 raw41211Labels = mixedMoment B raw41211step0 raw41211step0Labels := by
      have ha : raw41211step0 = (fun i j => raw41211 (permutation243 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41211step0 raw41211; decide +kernel
      have hl : raw41211step0Labels = raw41211Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41211 raw41211Labels permutation243 permutation6
    _ = mixedMoment B node3496 node3496Labels := by rfl

def raw41212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw41212Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw41212step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41212step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![2, -1, -1]]
def raw41212step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41212step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![2, -1, -1]]
def raw41212step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41212step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-2, -1, 3]]
def raw41212step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41212step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw41212step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41212 raw41212Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw41212 raw41212Labels = mixedMoment B raw41212step0 raw41212step0Labels := by
      have hz : ∀ j, raw41212 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41212step0 = (fun i j => raw41212 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41212step0 raw41212; decide +kernel
      have hl : raw41212step0Labels = raw41212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41212 raw41212Labels permutation520 hz
    mixedMoment B raw41212step0 raw41212step0Labels = mixedMoment B raw41212step1 raw41212step1Labels := by
      have hz : ∀ j, raw41212step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41212step1 = (fun i j => raw41212step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41212step1 raw41212step0; decide +kernel
      have hl : raw41212step1Labels = raw41212step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41212step0 raw41212step0Labels permutation104 hz
    mixedMoment B raw41212step1 raw41212step1Labels = mixedMoment B raw41212step2 raw41212step2Labels := by
      have hz : ∀ j, raw41212step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41212step2 = (fun i j => raw41212step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41212step2 raw41212step1; decide +kernel
      have hl : raw41212step2Labels = raw41212step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41212step1 raw41212step1Labels permutation20 hz
    mixedMoment B raw41212step2 raw41212step2Labels = mixedMoment B raw41212step3 raw41212step3Labels := by
      have ha : raw41212step3 = (fun i j => raw41212step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41212step3 raw41212step2; decide +kernel
      have hl : raw41212step3Labels = raw41212step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41212step2 raw41212step2Labels permutation5 permutation6
    mixedMoment B raw41212step3 raw41212step3Labels = mixedMoment B raw41212step4 raw41212step4Labels := by
      have ha : raw41212step4 = -raw41212step3 := by apply Matrix.ext; change ∀ i j, raw41212step4 i j = -(raw41212step3 i j); unfold raw41212step4 raw41212step3; decide +kernel
      have hl : raw41212step4Labels = raw41212step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2783 node2783Labels := by rfl

def raw41213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw41213Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw41213step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, -1, 1], ![2, 0, -2]]
def raw41213step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41213step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw41213step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41213step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw41213step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41213 raw41213Labels = mixedMoment B node2522 node2522Labels := by
  calc
    mixedMoment B raw41213 raw41213Labels = mixedMoment B raw41213step0 raw41213step0Labels := by
      have hz : ∀ j, raw41213 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41213step0 = (fun i j => raw41213 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41213step0 raw41213; decide +kernel
      have hl : raw41213step0Labels = raw41213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41213 raw41213Labels permutation434 hz
    mixedMoment B raw41213step0 raw41213step0Labels = mixedMoment B raw41213step1 raw41213step1Labels := by
      have hz : ∀ j, raw41213step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41213step1 = (fun i j => raw41213step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41213step1 raw41213step0; decide +kernel
      have hl : raw41213step1Labels = raw41213step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41213step0 raw41213step0Labels permutation80 hz
    mixedMoment B raw41213step1 raw41213step1Labels = mixedMoment B raw41213step2 raw41213step2Labels := by
      have ha : raw41213step2 = (fun i j => raw41213step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41213step2 raw41213step1; decide +kernel
      have hl : raw41213step2Labels = raw41213step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41213step1 raw41213step1Labels permutation17 permutation6
    mixedMoment B raw41213step2 raw41213step2Labels = mixedMoment B raw41213step3 raw41213step3Labels := by
      have ha : raw41213step3 = -raw41213step2 := by apply Matrix.ext; change ∀ i j, raw41213step3 i j = -(raw41213step2 i j); unfold raw41213step3 raw41213step2; decide +kernel
      have hl : raw41213step3Labels = raw41213step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2522 node2522Labels := by rfl

def raw41214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw41214Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw41214step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41214step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -2, 3], ![1, 0, -1], ![1, -1, 0]]
def raw41214step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41214step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-2, -1, 3]]
def raw41214step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41214step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41214step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41214 raw41214Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw41214 raw41214Labels = mixedMoment B raw41214step0 raw41214step0Labels := by
      have hz : ∀ j, raw41214 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41214step0 = (fun i j => raw41214 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41214step0 raw41214; decide +kernel
      have hl : raw41214step0Labels = raw41214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41214 raw41214Labels permutation434 hz
    mixedMoment B raw41214step0 raw41214step0Labels = mixedMoment B raw41214step1 raw41214step1Labels := by
      have hz : ∀ j, raw41214step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41214step1 = (fun i j => raw41214step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41214step1 raw41214step0; decide +kernel
      have hl : raw41214step1Labels = raw41214step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41214step0 raw41214step0Labels permutation80 hz
    mixedMoment B raw41214step1 raw41214step1Labels = mixedMoment B raw41214step2 raw41214step2Labels := by
      have ha : raw41214step2 = (fun i j => raw41214step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41214step2 raw41214step1; decide +kernel
      have hl : raw41214step2Labels = raw41214step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41214step1 raw41214step1Labels permutation19 permutation6
    mixedMoment B raw41214step2 raw41214step2Labels = mixedMoment B raw41214step3 raw41214step3Labels := by
      have ha : raw41214step3 = -raw41214step2 := by apply Matrix.ext; change ∀ i j, raw41214step3 i j = -(raw41214step2 i j); unfold raw41214step3 raw41214step2; decide +kernel
      have hl : raw41214step3Labels = raw41214step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw41215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -3, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw41215Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -3, 4], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw41215step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41215step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -3, 4], ![0, 0, 0], ![2, 0, -2]]
def raw41215step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41215step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 3, -2], ![-1, -3, 4], ![2, 0, -2]]
def raw41215step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41215step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-2, 2, 0], ![-2, -1, 3]]
def raw41215step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41215step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw41215step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41215 raw41215Labels = mixedMoment B node1094 node1094Labels := by
  calc
    mixedMoment B raw41215 raw41215Labels = mixedMoment B raw41215step0 raw41215step0Labels := by
      have hz : ∀ j, raw41215 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41215step0 = (fun i j => raw41215 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41215step0 raw41215; decide +kernel
      have hl : raw41215step0Labels = raw41215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41215 raw41215Labels permutation520 hz
    mixedMoment B raw41215step0 raw41215step0Labels = mixedMoment B raw41215step1 raw41215step1Labels := by
      have hz : ∀ j, raw41215step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41215step1 = (fun i j => raw41215step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41215step1 raw41215step0; decide +kernel
      have hl : raw41215step1Labels = raw41215step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41215step0 raw41215step0Labels permutation104 hz
    mixedMoment B raw41215step1 raw41215step1Labels = mixedMoment B raw41215step2 raw41215step2Labels := by
      have hz : ∀ j, raw41215step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41215step2 = (fun i j => raw41215step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41215step2 raw41215step1; decide +kernel
      have hl : raw41215step2Labels = raw41215step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41215step1 raw41215step1Labels permutation20 hz
    mixedMoment B raw41215step2 raw41215step2Labels = mixedMoment B raw41215step3 raw41215step3Labels := by
      have ha : raw41215step3 = (fun i j => raw41215step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41215step3 raw41215step2; decide +kernel
      have hl : raw41215step3Labels = raw41215step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41215step2 raw41215step2Labels permutation5 permutation6
    mixedMoment B raw41215step3 raw41215step3Labels = mixedMoment B raw41215step4 raw41215step4Labels := by
      have ha : raw41215step4 = -raw41215step3 := by apply Matrix.ext; change ∀ i j, raw41215step4 i j = -(raw41215step3 i j); unfold raw41215step4 raw41215step3; decide +kernel
      have hl : raw41215step4Labels = raw41215step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1094 node1094Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
