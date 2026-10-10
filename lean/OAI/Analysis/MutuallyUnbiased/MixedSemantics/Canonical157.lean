import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw20096 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20096Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20096step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20096step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20096step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -3, 1], ![2, 2, -4]]
def raw20096step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20096 raw20096Labels = mixedMoment B node2064 node2064Labels := by
  calc
    mixedMoment B raw20096 raw20096Labels = mixedMoment B raw20096step0 raw20096step0Labels := by
      have hz : ∀ j, raw20096 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20096step0 = (fun i j => raw20096 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20096step0 raw20096; decide +kernel
      have hl : raw20096step0Labels = raw20096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20096 raw20096Labels permutation346 hz
    mixedMoment B raw20096step0 raw20096step0Labels = mixedMoment B raw20096step1 raw20096step1Labels := by
      have hz : ∀ j, raw20096step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20096step1 = (fun i j => raw20096step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20096step1 raw20096step0; decide +kernel
      have hl : raw20096step1Labels = raw20096step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20096step0 raw20096step0Labels permutation56 hz
    mixedMoment B raw20096step1 raw20096step1Labels = mixedMoment B raw20096step2 raw20096step2Labels := by
      have ha : raw20096step2 = (fun i j => raw20096step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20096step2 raw20096step1; decide +kernel
      have hl : raw20096step2Labels = raw20096step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20096step1 raw20096step1Labels permutation29 permutation2
    _ = mixedMoment B node2064 node2064Labels := by rfl

def raw20097 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20097Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20097step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20097step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20097step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-3, 0, 3]]
def raw20097step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20097step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]
def raw20097step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20097 raw20097Labels = mixedMoment B node2289 node2289Labels := by
  calc
    mixedMoment B raw20097 raw20097Labels = mixedMoment B raw20097step0 raw20097step0Labels := by
      have hz : ∀ j, raw20097 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20097step0 = (fun i j => raw20097 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20097step0 raw20097; decide +kernel
      have hl : raw20097step0Labels = raw20097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20097 raw20097Labels permutation434 hz
    mixedMoment B raw20097step0 raw20097step0Labels = mixedMoment B raw20097step1 raw20097step1Labels := by
      have hz : ∀ j, raw20097step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20097step1 = (fun i j => raw20097step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20097step1 raw20097step0; decide +kernel
      have hl : raw20097step1Labels = raw20097step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20097step0 raw20097step0Labels permutation80 hz
    mixedMoment B raw20097step1 raw20097step1Labels = mixedMoment B raw20097step2 raw20097step2Labels := by
      have hz : ∀ j, raw20097step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20097step2 = (fun i j => raw20097step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20097step2 raw20097step1; decide +kernel
      have hl : raw20097step2Labels = raw20097step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20097step1 raw20097step1Labels permutation14 hz
    mixedMoment B raw20097step2 raw20097step2Labels = mixedMoment B raw20097step3 raw20097step3Labels := by
      have ha : raw20097step3 = (fun i j => raw20097step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20097step3 raw20097step2; decide +kernel
      have hl : raw20097step3Labels = raw20097step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20097step2 raw20097step2Labels permutation7 permutation2
    _ = mixedMoment B node2289 node2289Labels := by rfl

def raw20098 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-4, 1, 3]]
def raw20098Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-4, 1, 3]]
def raw20098step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20098step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -3, 1], ![-4, 1, 3]]
def raw20098step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20098step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![2, -3, 1], ![-4, 1, 3]]
def raw20098step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20098step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -3, 1], ![2, 2, -4]]
def raw20098step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20098 raw20098Labels = mixedMoment B node1093 node1093Labels := by
  calc
    mixedMoment B raw20098 raw20098Labels = mixedMoment B raw20098step0 raw20098step0Labels := by
      have hz : ∀ j, raw20098 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20098step0 = (fun i j => raw20098 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20098step0 raw20098; decide +kernel
      have hl : raw20098step0Labels = raw20098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20098 raw20098Labels permutation434 hz
    mixedMoment B raw20098step0 raw20098step0Labels = mixedMoment B raw20098step1 raw20098step1Labels := by
      have hz : ∀ j, raw20098step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20098step1 = (fun i j => raw20098step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20098step1 raw20098step0; decide +kernel
      have hl : raw20098step1Labels = raw20098step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20098step0 raw20098step0Labels permutation80 hz
    mixedMoment B raw20098step1 raw20098step1Labels = mixedMoment B raw20098step2 raw20098step2Labels := by
      have hz : ∀ j, raw20098step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20098step2 = (fun i j => raw20098step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20098step2 raw20098step1; decide +kernel
      have hl : raw20098step2Labels = raw20098step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20098step1 raw20098step1Labels permutation14 hz
    mixedMoment B raw20098step2 raw20098step2Labels = mixedMoment B raw20098step3 raw20098step3Labels := by
      have ha : raw20098step3 = (fun i j => raw20098step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20098step3 raw20098step2; decide +kernel
      have hl : raw20098step3Labels = raw20098step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20098step2 raw20098step2Labels permutation7 permutation2
    _ = mixedMoment B node1093 node1093Labels := by rfl

def raw20099 : Matrix (Fin 6) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![-3, 3]]
def raw20099Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20099step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![0, 0], ![-1, 1], ![-3, 3]]
def raw20099step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20099step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![-1, 1], ![-3, 3]]
def raw20099step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20099step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-3, 3]]
def raw20099step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20099step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw20099step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20099 raw20099Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw20099 raw20099Labels = mixedMoment B raw20099step0 raw20099step0Labels := by
      have hz : ∀ j, raw20099 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20099step0 = (fun i j => raw20099 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20099step0 raw20099; decide +kernel
      have hl : raw20099step0Labels = raw20099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20099 raw20099Labels permutation434 hz
    mixedMoment B raw20099step0 raw20099step0Labels = mixedMoment B raw20099step1 raw20099step1Labels := by
      have hz : ∀ j, raw20099step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20099step1 = (fun i j => raw20099step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20099step1 raw20099step0; decide +kernel
      have hl : raw20099step1Labels = raw20099step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20099step0 raw20099step0Labels permutation80 hz
    mixedMoment B raw20099step1 raw20099step1Labels = mixedMoment B raw20099step2 raw20099step2Labels := by
      have hz : ∀ j, raw20099step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20099step2 = (fun i j => raw20099step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20099step2 raw20099step1; decide +kernel
      have hl : raw20099step2Labels = raw20099step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20099step1 raw20099step1Labels permutation14 hz
    mixedMoment B raw20099step2 raw20099step2Labels = mixedMoment B raw20099step3 raw20099step3Labels := by
      have ha : raw20099step3 = -raw20099step2 := by apply Matrix.ext; change ∀ i j, raw20099step3 i j = -(raw20099step2 i j); unfold raw20099step3 raw20099step2; decide +kernel
      have hl : raw20099step3Labels = raw20099step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

def raw20100 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20100Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20100step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20100step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20100step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20100step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw20100step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20100step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw20100step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20100 raw20100Labels = mixedMoment B node1745 node1745Labels := by
  calc
    mixedMoment B raw20100 raw20100Labels = mixedMoment B raw20100step0 raw20100step0Labels := by
      have hz : ∀ j, raw20100 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20100step0 = (fun i j => raw20100 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20100step0 raw20100; decide +kernel
      have hl : raw20100step0Labels = raw20100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20100 raw20100Labels permutation434 hz
    mixedMoment B raw20100step0 raw20100step0Labels = mixedMoment B raw20100step1 raw20100step1Labels := by
      have hz : ∀ j, raw20100step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20100step1 = (fun i j => raw20100step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20100step1 raw20100step0; decide +kernel
      have hl : raw20100step1Labels = raw20100step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20100step0 raw20100step0Labels permutation80 hz
    mixedMoment B raw20100step1 raw20100step1Labels = mixedMoment B raw20100step2 raw20100step2Labels := by
      have ha : raw20100step2 = (fun i j => raw20100step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20100step2 raw20100step1; decide +kernel
      have hl : raw20100step2Labels = raw20100step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20100step1 raw20100step1Labels permutation12 permutation4
    mixedMoment B raw20100step2 raw20100step2Labels = mixedMoment B raw20100step3 raw20100step3Labels := by
      have ha : raw20100step3 = -raw20100step2 := by apply Matrix.ext; change ∀ i j, raw20100step3 i j = -(raw20100step2 i j); unfold raw20100step3 raw20100step2; decide +kernel
      have hl : raw20100step3Labels = raw20100step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1745 node1745Labels := by rfl

def raw20101 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20101Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20101step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20101step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw20101step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20101step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw20101step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20101 raw20101Labels = mixedMoment B node1745 node1745Labels := by
  calc
    mixedMoment B raw20101 raw20101Labels = mixedMoment B raw20101step0 raw20101step0Labels := by
      have hz : ∀ j, raw20101 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20101step0 = (fun i j => raw20101 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20101step0 raw20101; decide +kernel
      have hl : raw20101step0Labels = raw20101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20101 raw20101Labels permutation434 hz
    mixedMoment B raw20101step0 raw20101step0Labels = mixedMoment B raw20101step1 raw20101step1Labels := by
      have hz : ∀ j, raw20101step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20101step1 = (fun i j => raw20101step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20101step1 raw20101step0; decide +kernel
      have hl : raw20101step1Labels = raw20101step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20101step0 raw20101step0Labels permutation56 hz
    mixedMoment B raw20101step1 raw20101step1Labels = mixedMoment B raw20101step2 raw20101step2Labels := by
      have ha : raw20101step2 = (fun i j => raw20101step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20101step2 raw20101step1; decide +kernel
      have hl : raw20101step2Labels = raw20101step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20101step1 raw20101step1Labels permutation12 permutation4
    mixedMoment B raw20101step2 raw20101step2Labels = mixedMoment B raw20101step3 raw20101step3Labels := by
      have ha : raw20101step3 = -raw20101step2 := by apply Matrix.ext; change ∀ i j, raw20101step3 i j = -(raw20101step2 i j); unfold raw20101step3 raw20101step2; decide +kernel
      have hl : raw20101step3Labels = raw20101step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1745 node1745Labels := by rfl

def raw20102 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20102Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20102step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20102step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20102step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20102step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw20102step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20102step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw20102step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20102 raw20102Labels = mixedMoment B node1745 node1745Labels := by
  calc
    mixedMoment B raw20102 raw20102Labels = mixedMoment B raw20102step0 raw20102step0Labels := by
      have hz : ∀ j, raw20102 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20102step0 = (fun i j => raw20102 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20102step0 raw20102; decide +kernel
      have hl : raw20102step0Labels = raw20102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20102 raw20102Labels permutation346 hz
    mixedMoment B raw20102step0 raw20102step0Labels = mixedMoment B raw20102step1 raw20102step1Labels := by
      have hz : ∀ j, raw20102step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20102step1 = (fun i j => raw20102step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20102step1 raw20102step0; decide +kernel
      have hl : raw20102step1Labels = raw20102step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20102step0 raw20102step0Labels permutation56 hz
    mixedMoment B raw20102step1 raw20102step1Labels = mixedMoment B raw20102step2 raw20102step2Labels := by
      have ha : raw20102step2 = (fun i j => raw20102step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20102step2 raw20102step1; decide +kernel
      have hl : raw20102step2Labels = raw20102step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20102step1 raw20102step1Labels permutation12 permutation4
    mixedMoment B raw20102step2 raw20102step2Labels = mixedMoment B raw20102step3 raw20102step3Labels := by
      have ha : raw20102step3 = -raw20102step2 := by apply Matrix.ext; change ∀ i j, raw20102step3 i j = -(raw20102step2 i j); unfold raw20102step3 raw20102step2; decide +kernel
      have hl : raw20102step3Labels = raw20102step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1745 node1745Labels := by rfl

def raw20103 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20103Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20103step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20103step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20103step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20103step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![-2, -1, 3]]
def raw20103step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20103step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -2, 3], ![-2, 1, 1]]
def raw20103step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20103step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw20103step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20103 raw20103Labels = mixedMoment B node1756 node1756Labels := by
  calc
    mixedMoment B raw20103 raw20103Labels = mixedMoment B raw20103step0 raw20103step0Labels := by
      have hz : ∀ j, raw20103 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20103step0 = (fun i j => raw20103 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20103step0 raw20103; decide +kernel
      have hl : raw20103step0Labels = raw20103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20103 raw20103Labels permutation434 hz
    mixedMoment B raw20103step0 raw20103step0Labels = mixedMoment B raw20103step1 raw20103step1Labels := by
      have hz : ∀ j, raw20103step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20103step1 = (fun i j => raw20103step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20103step1 raw20103step0; decide +kernel
      have hl : raw20103step1Labels = raw20103step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20103step0 raw20103step0Labels permutation80 hz
    mixedMoment B raw20103step1 raw20103step1Labels = mixedMoment B raw20103step2 raw20103step2Labels := by
      have hz : ∀ j, raw20103step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20103step2 = (fun i j => raw20103step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20103step2 raw20103step1; decide +kernel
      have hl : raw20103step2Labels = raw20103step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20103step1 raw20103step1Labels permutation14 hz
    mixedMoment B raw20103step2 raw20103step2Labels = mixedMoment B raw20103step3 raw20103step3Labels := by
      have ha : raw20103step3 = (fun i j => raw20103step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20103step3 raw20103step2; decide +kernel
      have hl : raw20103step3Labels = raw20103step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20103step2 raw20103step2Labels permutation3 permutation4
    mixedMoment B raw20103step3 raw20103step3Labels = mixedMoment B raw20103step4 raw20103step4Labels := by
      have ha : raw20103step4 = -raw20103step3 := by apply Matrix.ext; change ∀ i j, raw20103step4 i j = -(raw20103step3 i j); unfold raw20103step4 raw20103step3; decide +kernel
      have hl : raw20103step4Labels = raw20103step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1756 node1756Labels := by rfl

def raw20104 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw20104Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw20104step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw20104step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20104step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![2, -3, 1], ![-2, -1, 3]]
def raw20104step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20104step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![-1, -2, 3], ![-3, 2, 1]]
def raw20104step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20104step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw20104step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20104 raw20104Labels = mixedMoment B node860 node860Labels := by
  calc
    mixedMoment B raw20104 raw20104Labels = mixedMoment B raw20104step0 raw20104step0Labels := by
      have hz : ∀ j, raw20104 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20104step0 = (fun i j => raw20104 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20104step0 raw20104; decide +kernel
      have hl : raw20104step0Labels = raw20104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20104 raw20104Labels permutation434 hz
    mixedMoment B raw20104step0 raw20104step0Labels = mixedMoment B raw20104step1 raw20104step1Labels := by
      have hz : ∀ j, raw20104step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20104step1 = (fun i j => raw20104step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20104step1 raw20104step0; decide +kernel
      have hl : raw20104step1Labels = raw20104step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20104step0 raw20104step0Labels permutation80 hz
    mixedMoment B raw20104step1 raw20104step1Labels = mixedMoment B raw20104step2 raw20104step2Labels := by
      have hz : ∀ j, raw20104step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20104step2 = (fun i j => raw20104step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20104step2 raw20104step1; decide +kernel
      have hl : raw20104step2Labels = raw20104step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20104step1 raw20104step1Labels permutation14 hz
    mixedMoment B raw20104step2 raw20104step2Labels = mixedMoment B raw20104step3 raw20104step3Labels := by
      have ha : raw20104step3 = (fun i j => raw20104step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20104step3 raw20104step2; decide +kernel
      have hl : raw20104step3Labels = raw20104step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20104step2 raw20104step2Labels permutation3 permutation4
    mixedMoment B raw20104step3 raw20104step3Labels = mixedMoment B raw20104step4 raw20104step4Labels := by
      have ha : raw20104step4 = -raw20104step3 := by apply Matrix.ext; change ∀ i j, raw20104step4 i j = -(raw20104step3 i j); unfold raw20104step4 raw20104step3; decide +kernel
      have hl : raw20104step4Labels = raw20104step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node860 node860Labels := by rfl

def raw20105 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw20105Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw20105step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw20105step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -2, 3], ![-3, 2, 1]]
def raw20105step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20105step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 2, -3], ![3, -2, -1]]
def raw20105step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20105 raw20105Labels = mixedMoment B node1628 node1628Labels := by
  calc
    mixedMoment B raw20105 raw20105Labels = mixedMoment B raw20105step0 raw20105step0Labels := by
      have hz : ∀ j, raw20105 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20105step0 = (fun i j => raw20105 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20105step0 raw20105; decide +kernel
      have hl : raw20105step0Labels = raw20105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20105 raw20105Labels permutation434 hz
    mixedMoment B raw20105step0 raw20105step0Labels = mixedMoment B raw20105step1 raw20105step1Labels := by
      have hz : ∀ j, raw20105step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20105step1 = (fun i j => raw20105step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20105step1 raw20105step0; decide +kernel
      have hl : raw20105step1Labels = raw20105step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20105step0 raw20105step0Labels permutation80 hz
    mixedMoment B raw20105step1 raw20105step1Labels = mixedMoment B raw20105step2 raw20105step2Labels := by
      have ha : raw20105step2 = (fun i j => raw20105step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20105step2 raw20105step1; decide +kernel
      have hl : raw20105step2Labels = raw20105step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20105step1 raw20105step1Labels permutation9 permutation4
    mixedMoment B raw20105step2 raw20105step2Labels = mixedMoment B raw20105step3 raw20105step3Labels := by
      have ha : raw20105step3 = -raw20105step2 := by apply Matrix.ext; change ∀ i j, raw20105step3 i j = -(raw20105step2 i j); unfold raw20105step3 raw20105step2; decide +kernel
      have hl : raw20105step3Labels = raw20105step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1628 node1628Labels := by rfl

def raw20106 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw20106Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw20106step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20106step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw20106step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20106step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -2, 3], ![-3, 2, 1]]
def raw20106step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20106step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 2, -3], ![3, -2, -1]]
def raw20106step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20106 raw20106Labels = mixedMoment B node1628 node1628Labels := by
  calc
    mixedMoment B raw20106 raw20106Labels = mixedMoment B raw20106step0 raw20106step0Labels := by
      have hz : ∀ j, raw20106 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20106step0 = (fun i j => raw20106 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20106step0 raw20106; decide +kernel
      have hl : raw20106step0Labels = raw20106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20106 raw20106Labels permutation434 hz
    mixedMoment B raw20106step0 raw20106step0Labels = mixedMoment B raw20106step1 raw20106step1Labels := by
      have hz : ∀ j, raw20106step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20106step1 = (fun i j => raw20106step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20106step1 raw20106step0; decide +kernel
      have hl : raw20106step1Labels = raw20106step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20106step0 raw20106step0Labels permutation56 hz
    mixedMoment B raw20106step1 raw20106step1Labels = mixedMoment B raw20106step2 raw20106step2Labels := by
      have ha : raw20106step2 = (fun i j => raw20106step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20106step2 raw20106step1; decide +kernel
      have hl : raw20106step2Labels = raw20106step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20106step1 raw20106step1Labels permutation9 permutation4
    mixedMoment B raw20106step2 raw20106step2Labels = mixedMoment B raw20106step3 raw20106step3Labels := by
      have ha : raw20106step3 = -raw20106step2 := by apply Matrix.ext; change ∀ i j, raw20106step3 i j = -(raw20106step2 i j); unfold raw20106step3 raw20106step2; decide +kernel
      have hl : raw20106step3Labels = raw20106step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1628 node1628Labels := by rfl

def raw20107 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw20107Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw20107step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20107step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw20107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20107step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -2, 3], ![-3, 2, 1]]
def raw20107step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20107step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 2, -3], ![3, -2, -1]]
def raw20107step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20107 raw20107Labels = mixedMoment B node1628 node1628Labels := by
  calc
    mixedMoment B raw20107 raw20107Labels = mixedMoment B raw20107step0 raw20107step0Labels := by
      have hz : ∀ j, raw20107 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20107step0 = (fun i j => raw20107 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20107step0 raw20107; decide +kernel
      have hl : raw20107step0Labels = raw20107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20107 raw20107Labels permutation346 hz
    mixedMoment B raw20107step0 raw20107step0Labels = mixedMoment B raw20107step1 raw20107step1Labels := by
      have hz : ∀ j, raw20107step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20107step1 = (fun i j => raw20107step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20107step1 raw20107step0; decide +kernel
      have hl : raw20107step1Labels = raw20107step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20107step0 raw20107step0Labels permutation56 hz
    mixedMoment B raw20107step1 raw20107step1Labels = mixedMoment B raw20107step2 raw20107step2Labels := by
      have ha : raw20107step2 = (fun i j => raw20107step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20107step2 raw20107step1; decide +kernel
      have hl : raw20107step2Labels = raw20107step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20107step1 raw20107step1Labels permutation9 permutation4
    mixedMoment B raw20107step2 raw20107step2Labels = mixedMoment B raw20107step3 raw20107step3Labels := by
      have ha : raw20107step3 = -raw20107step2 := by apply Matrix.ext; change ∀ i j, raw20107step3 i j = -(raw20107step2 i j); unfold raw20107step3 raw20107step2; decide +kernel
      have hl : raw20107step3Labels = raw20107step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1628 node1628Labels := by rfl

def raw20108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20108Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20108step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20108step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20108step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20108 raw20108Labels = mixedMoment B node612 node612Labels := by
  calc
    mixedMoment B raw20108 raw20108Labels = mixedMoment B raw20108step0 raw20108step0Labels := by
      have hz : ∀ j, raw20108 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20108step0 = (fun i j => raw20108 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20108step0 raw20108; decide +kernel
      have hl : raw20108step0Labels = raw20108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20108 raw20108Labels permutation346 hz
    mixedMoment B raw20108step0 raw20108step0Labels = mixedMoment B raw20108step1 raw20108step1Labels := by
      have hz : ∀ j, raw20108step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20108step1 = (fun i j => raw20108step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20108step1 raw20108step0; decide +kernel
      have hl : raw20108step1Labels = raw20108step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20108step0 raw20108step0Labels permutation56 hz
    _ = mixedMoment B node612 node612Labels := by rfl

def raw20109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20109Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20109step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20109 raw20109Labels = mixedMoment B node931 node931Labels := by
  calc
    mixedMoment B raw20109 raw20109Labels = mixedMoment B raw20109step0 raw20109step0Labels := by
      have hz : ∀ j, raw20109 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20109step0 = (fun i j => raw20109 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20109step0 raw20109; decide +kernel
      have hl : raw20109step0Labels = raw20109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20109 raw20109Labels permutation346 hz
    _ = mixedMoment B node931 node931Labels := by rfl

def raw20110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20110Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20110step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20110 raw20110Labels = mixedMoment B node931 node931Labels := by
  calc
    mixedMoment B raw20110 raw20110Labels = mixedMoment B raw20110step0 raw20110step0Labels := by
      have hz : ∀ j, raw20110 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20110step0 = (fun i j => raw20110 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20110step0 raw20110; decide +kernel
      have hl : raw20110step0Labels = raw20110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20110 raw20110Labels permutation265 hz
    _ = mixedMoment B node931 node931Labels := by rfl

def raw20111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw20111Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw20111step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20111step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw20111step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20111 raw20111Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw20111 raw20111Labels = mixedMoment B raw20111step0 raw20111step0Labels := by
      have hz : ∀ j, raw20111 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20111step0 = (fun i j => raw20111 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20111step0 raw20111; decide +kernel
      have hl : raw20111step0Labels = raw20111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20111 raw20111Labels permutation346 hz
    mixedMoment B raw20111step0 raw20111step0Labels = mixedMoment B raw20111step1 raw20111step1Labels := by
      have hz : ∀ j, raw20111step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20111step1 = (fun i j => raw20111step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20111step1 raw20111step0; decide +kernel
      have hl : raw20111step1Labels = raw20111step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20111step0 raw20111step0Labels permutation56 hz
    _ = mixedMoment B node1087 node1087Labels := by rfl

def raw20112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20112Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20112step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20112step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20112step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20112 raw20112Labels = mixedMoment B node590 node590Labels := by
  calc
    mixedMoment B raw20112 raw20112Labels = mixedMoment B raw20112step0 raw20112step0Labels := by
      have hz : ∀ j, raw20112 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20112step0 = (fun i j => raw20112 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20112step0 raw20112; decide +kernel
      have hl : raw20112step0Labels = raw20112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20112 raw20112Labels permutation346 hz
    mixedMoment B raw20112step0 raw20112step0Labels = mixedMoment B raw20112step1 raw20112step1Labels := by
      have hz : ∀ j, raw20112step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20112step1 = (fun i j => raw20112step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20112step1 raw20112step0; decide +kernel
      have hl : raw20112step1Labels = raw20112step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20112step0 raw20112step0Labels permutation56 hz
    _ = mixedMoment B node590 node590Labels := by rfl

def raw20113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20113Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20113step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20113 raw20113Labels = mixedMoment B node914 node914Labels := by
  calc
    mixedMoment B raw20113 raw20113Labels = mixedMoment B raw20113step0 raw20113step0Labels := by
      have hz : ∀ j, raw20113 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20113step0 = (fun i j => raw20113 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20113step0 raw20113; decide +kernel
      have hl : raw20113step0Labels = raw20113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20113 raw20113Labels permutation346 hz
    _ = mixedMoment B node914 node914Labels := by rfl

def raw20114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20114Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20114step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20114 raw20114Labels = mixedMoment B node914 node914Labels := by
  calc
    mixedMoment B raw20114 raw20114Labels = mixedMoment B raw20114step0 raw20114step0Labels := by
      have hz : ∀ j, raw20114 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20114step0 = (fun i j => raw20114 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20114step0 raw20114; decide +kernel
      have hl : raw20114step0Labels = raw20114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20114 raw20114Labels permutation265 hz
    _ = mixedMoment B node914 node914Labels := by rfl

def raw20115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20115Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20115step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20115step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20115 raw20115Labels = mixedMoment B node954 node954Labels := by
  calc
    mixedMoment B raw20115 raw20115Labels = mixedMoment B raw20115step0 raw20115step0Labels := by
      have hz : ∀ j, raw20115 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20115step0 = (fun i j => raw20115 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20115step0 raw20115; decide +kernel
      have hl : raw20115step0Labels = raw20115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20115 raw20115Labels permutation346 hz
    mixedMoment B raw20115step0 raw20115step0Labels = mixedMoment B raw20115step1 raw20115step1Labels := by
      have hz : ∀ j, raw20115step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20115step1 = (fun i j => raw20115step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20115step1 raw20115step0; decide +kernel
      have hl : raw20115step1Labels = raw20115step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20115step0 raw20115step0Labels permutation56 hz
    _ = mixedMoment B node954 node954Labels := by rfl

def raw20116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw20116Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw20116step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20116step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw20116step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20116step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw20116step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20116 raw20116Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw20116 raw20116Labels = mixedMoment B raw20116step0 raw20116step0Labels := by
      have hz : ∀ j, raw20116 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20116step0 = (fun i j => raw20116 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20116step0 raw20116; decide +kernel
      have hl : raw20116step0Labels = raw20116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20116 raw20116Labels permutation346 hz
    mixedMoment B raw20116step0 raw20116step0Labels = mixedMoment B raw20116step1 raw20116step1Labels := by
      have hz : ∀ j, raw20116step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20116step1 = (fun i j => raw20116step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20116step1 raw20116step0; decide +kernel
      have hl : raw20116step1Labels = raw20116step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20116step0 raw20116step0Labels permutation56 hz
    mixedMoment B raw20116step1 raw20116step1Labels = mixedMoment B raw20116step2 raw20116step2Labels := by
      have ha : raw20116step2 = (fun i j => raw20116step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20116step2 raw20116step1; decide +kernel
      have hl : raw20116step2Labels = raw20116step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20116step1 raw20116step1Labels permutation9 permutation2
    _ = mixedMoment B node1049 node1049Labels := by rfl

def raw20117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20117Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20117step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20117step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20117 raw20117Labels = mixedMoment B node1336 node1336Labels := by
  calc
    mixedMoment B raw20117 raw20117Labels = mixedMoment B raw20117step0 raw20117step0Labels := by
      have hz : ∀ j, raw20117 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20117step0 = (fun i j => raw20117 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20117step0 raw20117; decide +kernel
      have hl : raw20117step0Labels = raw20117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20117 raw20117Labels permutation346 hz
    mixedMoment B raw20117step0 raw20117step0Labels = mixedMoment B raw20117step1 raw20117step1Labels := by
      have ha : raw20117step1 = (fun i j => raw20117step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20117step1 raw20117step0; decide +kernel
      have hl : raw20117step1Labels = raw20117step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20117step0 raw20117step0Labels permutation40 permutation2
    _ = mixedMoment B node1336 node1336Labels := by rfl

def raw20118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20118Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20118step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20118 raw20118Labels = mixedMoment B node1336 node1336Labels := by
  calc
    mixedMoment B raw20118 raw20118Labels = mixedMoment B raw20118step0 raw20118step0Labels := by
      have hz : ∀ j, raw20118 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20118step0 = (fun i j => raw20118 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20118step0 raw20118; decide +kernel
      have hl : raw20118step0Labels = raw20118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20118 raw20118Labels permutation265 hz
    mixedMoment B raw20118step0 raw20118step0Labels = mixedMoment B raw20118step1 raw20118step1Labels := by
      have ha : raw20118step1 = (fun i j => raw20118step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20118step1 raw20118step0; decide +kernel
      have hl : raw20118step1Labels = raw20118step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20118step0 raw20118step0Labels permutation40 permutation2
    _ = mixedMoment B node1336 node1336Labels := by rfl

def raw20119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def raw20119Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def raw20119step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def raw20119step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20119 raw20119Labels = mixedMoment B node1348 node1348Labels := by
  calc
    mixedMoment B raw20119 raw20119Labels = mixedMoment B raw20119step0 raw20119step0Labels := by
      have hz : ∀ j, raw20119 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20119step0 = (fun i j => raw20119 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20119step0 raw20119; decide +kernel
      have hl : raw20119step0Labels = raw20119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20119 raw20119Labels permutation346 hz
    mixedMoment B raw20119step0 raw20119step0Labels = mixedMoment B raw20119step1 raw20119step1Labels := by
      have hz : ∀ j, raw20119step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20119step1 = (fun i j => raw20119step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20119step1 raw20119step0; decide +kernel
      have hl : raw20119step1Labels = raw20119step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20119step0 raw20119step0Labels permutation56 hz
    _ = mixedMoment B node1348 node1348Labels := by rfl

def raw20120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![4, -1, -3]]
def raw20120Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![4, -1, -3]]
def raw20120step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![4, -1, -3]]
def raw20120step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20120step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 0, 1], ![-4, 3, 1]]
def raw20120step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20120step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![4, -3, -1]]
def raw20120step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20120 raw20120Labels = mixedMoment B node951 node951Labels := by
  calc
    mixedMoment B raw20120 raw20120Labels = mixedMoment B raw20120step0 raw20120step0Labels := by
      have hz : ∀ j, raw20120 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20120step0 = (fun i j => raw20120 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20120step0 raw20120; decide +kernel
      have hl : raw20120step0Labels = raw20120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20120 raw20120Labels permutation346 hz
    mixedMoment B raw20120step0 raw20120step0Labels = mixedMoment B raw20120step1 raw20120step1Labels := by
      have hz : ∀ j, raw20120step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20120step1 = (fun i j => raw20120step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20120step1 raw20120step0; decide +kernel
      have hl : raw20120step1Labels = raw20120step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20120step0 raw20120step0Labels permutation56 hz
    mixedMoment B raw20120step1 raw20120step1Labels = mixedMoment B raw20120step2 raw20120step2Labels := by
      have ha : raw20120step2 = (fun i j => raw20120step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20120step2 raw20120step1; decide +kernel
      have hl : raw20120step2Labels = raw20120step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20120step1 raw20120step1Labels permutation31 permutation2
    mixedMoment B raw20120step2 raw20120step2Labels = mixedMoment B raw20120step3 raw20120step3Labels := by
      have ha : raw20120step3 = -raw20120step2 := by apply Matrix.ext; change ∀ i j, raw20120step3 i j = -(raw20120step2 i j); unfold raw20120step3 raw20120step2; decide +kernel
      have hl : raw20120step3Labels = raw20120step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node951 node951Labels := by rfl

def raw20121 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20121Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20121step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20121step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20121 raw20121Labels = mixedMoment B node2045 node2045Labels := by
  calc
    mixedMoment B raw20121 raw20121Labels = mixedMoment B raw20121step0 raw20121step0Labels := by
      have hz : ∀ j, raw20121 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20121step0 = (fun i j => raw20121 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20121step0 raw20121; decide +kernel
      have hl : raw20121step0Labels = raw20121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20121 raw20121Labels permutation346 hz
    mixedMoment B raw20121step0 raw20121step0Labels = mixedMoment B raw20121step1 raw20121step1Labels := by
      have ha : raw20121step1 = (fun i j => raw20121step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20121step1 raw20121step0; decide +kernel
      have hl : raw20121step1Labels = raw20121step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20121step0 raw20121step0Labels permutation139 permutation2
    _ = mixedMoment B node2045 node2045Labels := by rfl

def raw20122 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20122Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20122step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20122 raw20122Labels = mixedMoment B node2045 node2045Labels := by
  calc
    mixedMoment B raw20122 raw20122Labels = mixedMoment B raw20122step0 raw20122step0Labels := by
      have hz : ∀ j, raw20122 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20122step0 = (fun i j => raw20122 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20122step0 raw20122; decide +kernel
      have hl : raw20122step0Labels = raw20122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20122 raw20122Labels permutation265 hz
    mixedMoment B raw20122step0 raw20122step0Labels = mixedMoment B raw20122step1 raw20122step1Labels := by
      have ha : raw20122step1 = (fun i j => raw20122step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20122step1 raw20122step0; decide +kernel
      have hl : raw20122step1Labels = raw20122step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20122step0 raw20122step0Labels permutation139 permutation2
    _ = mixedMoment B node2045 node2045Labels := by rfl

def raw20123 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20123Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20123step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20123step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20123step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20123step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20123step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20123 raw20123Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw20123 raw20123Labels = mixedMoment B raw20123step0 raw20123step0Labels := by
      have hz : ∀ j, raw20123 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20123step0 = (fun i j => raw20123 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20123step0 raw20123; decide +kernel
      have hl : raw20123step0Labels = raw20123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20123 raw20123Labels permutation346 hz
    mixedMoment B raw20123step0 raw20123step0Labels = mixedMoment B raw20123step1 raw20123step1Labels := by
      have hz : ∀ j, raw20123step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20123step1 = (fun i j => raw20123step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20123step1 raw20123step0; decide +kernel
      have hl : raw20123step1Labels = raw20123step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20123step0 raw20123step0Labels permutation56 hz
    mixedMoment B raw20123step1 raw20123step1Labels = mixedMoment B raw20123step2 raw20123step2Labels := by
      have ha : raw20123step2 = (fun i j => raw20123step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20123step2 raw20123step1; decide +kernel
      have hl : raw20123step2Labels = raw20123step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20123step1 raw20123step1Labels permutation31 permutation2
    _ = mixedMoment B node2226 node2226Labels := by rfl

def raw20124 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw20124Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw20124step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20124step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw20124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20124step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20124step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20124 raw20124Labels = mixedMoment B node1072 node1072Labels := by
  calc
    mixedMoment B raw20124 raw20124Labels = mixedMoment B raw20124step0 raw20124step0Labels := by
      have hz : ∀ j, raw20124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20124step0 = (fun i j => raw20124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20124step0 raw20124; decide +kernel
      have hl : raw20124step0Labels = raw20124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20124 raw20124Labels permutation346 hz
    mixedMoment B raw20124step0 raw20124step0Labels = mixedMoment B raw20124step1 raw20124step1Labels := by
      have hz : ∀ j, raw20124step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20124step1 = (fun i j => raw20124step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20124step1 raw20124step0; decide +kernel
      have hl : raw20124step1Labels = raw20124step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20124step0 raw20124step0Labels permutation56 hz
    mixedMoment B raw20124step1 raw20124step1Labels = mixedMoment B raw20124step2 raw20124step2Labels := by
      have ha : raw20124step2 = (fun i j => raw20124step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20124step2 raw20124step1; decide +kernel
      have hl : raw20124step2Labels = raw20124step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20124step1 raw20124step1Labels permutation31 permutation2
    _ = mixedMoment B node1072 node1072Labels := by rfl

def raw20125 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20125Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20125step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw20125step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20125step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw20125step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20125 raw20125Labels = mixedMoment B node834 node834Labels := by
  calc
    mixedMoment B raw20125 raw20125Labels = mixedMoment B raw20125step0 raw20125step0Labels := by
      have hz : ∀ j, raw20125 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20125step0 = (fun i j => raw20125 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20125step0 raw20125; decide +kernel
      have hl : raw20125step0Labels = raw20125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20125 raw20125Labels permutation346 hz
    mixedMoment B raw20125step0 raw20125step0Labels = mixedMoment B raw20125step1 raw20125step1Labels := by
      have ha : raw20125step1 = (fun i j => raw20125step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20125step1 raw20125step0; decide +kernel
      have hl : raw20125step1Labels = raw20125step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20125step0 raw20125step0Labels permutation50 permutation4
    mixedMoment B raw20125step1 raw20125step1Labels = mixedMoment B raw20125step2 raw20125step2Labels := by
      have ha : raw20125step2 = -raw20125step1 := by apply Matrix.ext; change ∀ i j, raw20125step2 i j = -(raw20125step1 i j); unfold raw20125step2 raw20125step1; decide +kernel
      have hl : raw20125step2Labels = raw20125step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node834 node834Labels := by rfl

def raw20126 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20126Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20126step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw20126step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw20126step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20126 raw20126Labels = mixedMoment B node834 node834Labels := by
  calc
    mixedMoment B raw20126 raw20126Labels = mixedMoment B raw20126step0 raw20126step0Labels := by
      have hz : ∀ j, raw20126 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20126step0 = (fun i j => raw20126 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20126step0 raw20126; decide +kernel
      have hl : raw20126step0Labels = raw20126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20126 raw20126Labels permutation265 hz
    mixedMoment B raw20126step0 raw20126step0Labels = mixedMoment B raw20126step1 raw20126step1Labels := by
      have ha : raw20126step1 = (fun i j => raw20126step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20126step1 raw20126step0; decide +kernel
      have hl : raw20126step1Labels = raw20126step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20126step0 raw20126step0Labels permutation50 permutation4
    mixedMoment B raw20126step1 raw20126step1Labels = mixedMoment B raw20126step2 raw20126step2Labels := by
      have ha : raw20126step2 = -raw20126step1 := by apply Matrix.ext; change ∀ i j, raw20126step2 i j = -(raw20126step1 i j); unfold raw20126step2 raw20126step1; decide +kernel
      have hl : raw20126step2Labels = raw20126step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node834 node834Labels := by rfl

def raw20127 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20127Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20127step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20127step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20127step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20127step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -3, 3], ![-2, 2, 0], ![-2, 1, 1]]
def raw20127step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20127step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![2, -2, 0], ![2, -1, -1]]
def raw20127step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20127 raw20127Labels = mixedMoment B node838 node838Labels := by
  calc
    mixedMoment B raw20127 raw20127Labels = mixedMoment B raw20127step0 raw20127step0Labels := by
      have hz : ∀ j, raw20127 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20127step0 = (fun i j => raw20127 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20127step0 raw20127; decide +kernel
      have hl : raw20127step0Labels = raw20127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20127 raw20127Labels permutation346 hz
    mixedMoment B raw20127step0 raw20127step0Labels = mixedMoment B raw20127step1 raw20127step1Labels := by
      have hz : ∀ j, raw20127step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20127step1 = (fun i j => raw20127step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20127step1 raw20127step0; decide +kernel
      have hl : raw20127step1Labels = raw20127step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20127step0 raw20127step0Labels permutation56 hz
    mixedMoment B raw20127step1 raw20127step1Labels = mixedMoment B raw20127step2 raw20127step2Labels := by
      have ha : raw20127step2 = (fun i j => raw20127step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20127step2 raw20127step1; decide +kernel
      have hl : raw20127step2Labels = raw20127step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20127step1 raw20127step1Labels permutation12 permutation4
    mixedMoment B raw20127step2 raw20127step2Labels = mixedMoment B raw20127step3 raw20127step3Labels := by
      have ha : raw20127step3 = -raw20127step2 := by apply Matrix.ext; change ∀ i j, raw20127step3 i j = -(raw20127step2 i j); unfold raw20127step3 raw20127step2; decide +kernel
      have hl : raw20127step3Labels = raw20127step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node838 node838Labels := by rfl

def raw20128 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20128Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20128step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20128step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20128step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -3, 3], ![-1, 1, 0], ![-3, 2, 1]]
def raw20128step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20128step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![3, -2, -1]]
def raw20128step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20128 raw20128Labels = mixedMoment B node836 node836Labels := by
  calc
    mixedMoment B raw20128 raw20128Labels = mixedMoment B raw20128step0 raw20128step0Labels := by
      have hz : ∀ j, raw20128 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20128step0 = (fun i j => raw20128 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20128step0 raw20128; decide +kernel
      have hl : raw20128step0Labels = raw20128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20128 raw20128Labels permutation346 hz
    mixedMoment B raw20128step0 raw20128step0Labels = mixedMoment B raw20128step1 raw20128step1Labels := by
      have hz : ∀ j, raw20128step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20128step1 = (fun i j => raw20128step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20128step1 raw20128step0; decide +kernel
      have hl : raw20128step1Labels = raw20128step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20128step0 raw20128step0Labels permutation56 hz
    mixedMoment B raw20128step1 raw20128step1Labels = mixedMoment B raw20128step2 raw20128step2Labels := by
      have ha : raw20128step2 = (fun i j => raw20128step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20128step2 raw20128step1; decide +kernel
      have hl : raw20128step2Labels = raw20128step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20128step1 raw20128step1Labels permutation12 permutation4
    mixedMoment B raw20128step2 raw20128step2Labels = mixedMoment B raw20128step3 raw20128step3Labels := by
      have ha : raw20128step3 = -raw20128step2 := by apply Matrix.ext; change ∀ i j, raw20128step3 i j = -(raw20128step2 i j); unfold raw20128step3 raw20128step2; decide +kernel
      have hl : raw20128step3Labels = raw20128step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node836 node836Labels := by rfl

def raw20129 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20129Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20129step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20129step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20129step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20129step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw20129step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20129step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw20129step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20129 raw20129Labels = mixedMoment B node853 node853Labels := by
  calc
    mixedMoment B raw20129 raw20129Labels = mixedMoment B raw20129step0 raw20129step0Labels := by
      have hz : ∀ j, raw20129 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20129step0 = (fun i j => raw20129 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20129step0 raw20129; decide +kernel
      have hl : raw20129step0Labels = raw20129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20129 raw20129Labels permutation346 hz
    mixedMoment B raw20129step0 raw20129step0Labels = mixedMoment B raw20129step1 raw20129step1Labels := by
      have hz : ∀ j, raw20129step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20129step1 = (fun i j => raw20129step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20129step1 raw20129step0; decide +kernel
      have hl : raw20129step1Labels = raw20129step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20129step0 raw20129step0Labels permutation56 hz
    mixedMoment B raw20129step1 raw20129step1Labels = mixedMoment B raw20129step2 raw20129step2Labels := by
      have ha : raw20129step2 = (fun i j => raw20129step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20129step2 raw20129step1; decide +kernel
      have hl : raw20129step2Labels = raw20129step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20129step1 raw20129step1Labels permutation9 permutation4
    mixedMoment B raw20129step2 raw20129step2Labels = mixedMoment B raw20129step3 raw20129step3Labels := by
      have ha : raw20129step3 = -raw20129step2 := by apply Matrix.ext; change ∀ i j, raw20129step3 i j = -(raw20129step2 i j); unfold raw20129step3 raw20129step2; decide +kernel
      have hl : raw20129step3Labels = raw20129step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node853 node853Labels := by rfl

def raw20130 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20130Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20130step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw20130step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw20130step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20130 raw20130Labels = mixedMoment B node1744 node1744Labels := by
  calc
    mixedMoment B raw20130 raw20130Labels = mixedMoment B raw20130step0 raw20130step0Labels := by
      have hz : ∀ j, raw20130 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20130step0 = (fun i j => raw20130 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20130step0 raw20130; decide +kernel
      have hl : raw20130step0Labels = raw20130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20130 raw20130Labels permutation346 hz
    mixedMoment B raw20130step0 raw20130step0Labels = mixedMoment B raw20130step1 raw20130step1Labels := by
      have ha : raw20130step1 = (fun i j => raw20130step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20130step1 raw20130step0; decide +kernel
      have hl : raw20130step1Labels = raw20130step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20130step0 raw20130step0Labels permutation50 permutation4
    mixedMoment B raw20130step1 raw20130step1Labels = mixedMoment B raw20130step2 raw20130step2Labels := by
      have ha : raw20130step2 = -raw20130step1 := by apply Matrix.ext; change ∀ i j, raw20130step2 i j = -(raw20130step1 i j); unfold raw20130step2 raw20130step1; decide +kernel
      have hl : raw20130step2Labels = raw20130step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1744 node1744Labels := by rfl

def raw20131 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20131Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20131step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw20131step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20131step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw20131step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20131 raw20131Labels = mixedMoment B node1744 node1744Labels := by
  calc
    mixedMoment B raw20131 raw20131Labels = mixedMoment B raw20131step0 raw20131step0Labels := by
      have hz : ∀ j, raw20131 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20131step0 = (fun i j => raw20131 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20131step0 raw20131; decide +kernel
      have hl : raw20131step0Labels = raw20131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20131 raw20131Labels permutation265 hz
    mixedMoment B raw20131step0 raw20131step0Labels = mixedMoment B raw20131step1 raw20131step1Labels := by
      have ha : raw20131step1 = (fun i j => raw20131step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20131step1 raw20131step0; decide +kernel
      have hl : raw20131step1Labels = raw20131step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20131step0 raw20131step0Labels permutation50 permutation4
    mixedMoment B raw20131step1 raw20131step1Labels = mixedMoment B raw20131step2 raw20131step2Labels := by
      have ha : raw20131step2 = -raw20131step1 := by apply Matrix.ext; change ∀ i j, raw20131step2 i j = -(raw20131step1 i j); unfold raw20131step2 raw20131step1; decide +kernel
      have hl : raw20131step2Labels = raw20131step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1744 node1744Labels := by rfl

def raw20132 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20132Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20132step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20132step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20132step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20132step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 0, 1], ![-2, 2, 0]]
def raw20132step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20132step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw20132step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20132 raw20132Labels = mixedMoment B node1746 node1746Labels := by
  calc
    mixedMoment B raw20132 raw20132Labels = mixedMoment B raw20132step0 raw20132step0Labels := by
      have hz : ∀ j, raw20132 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20132step0 = (fun i j => raw20132 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20132step0 raw20132; decide +kernel
      have hl : raw20132step0Labels = raw20132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20132 raw20132Labels permutation346 hz
    mixedMoment B raw20132step0 raw20132step0Labels = mixedMoment B raw20132step1 raw20132step1Labels := by
      have hz : ∀ j, raw20132step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20132step1 = (fun i j => raw20132step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20132step1 raw20132step0; decide +kernel
      have hl : raw20132step1Labels = raw20132step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20132step0 raw20132step0Labels permutation56 hz
    mixedMoment B raw20132step1 raw20132step1Labels = mixedMoment B raw20132step2 raw20132step2Labels := by
      have ha : raw20132step2 = (fun i j => raw20132step1 (permutation13 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20132step2 raw20132step1; decide +kernel
      have hl : raw20132step2Labels = raw20132step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20132step1 raw20132step1Labels permutation13 permutation4
    mixedMoment B raw20132step2 raw20132step2Labels = mixedMoment B raw20132step3 raw20132step3Labels := by
      have ha : raw20132step3 = -raw20132step2 := by apply Matrix.ext; change ∀ i j, raw20132step3 i j = -(raw20132step2 i j); unfold raw20132step3 raw20132step2; decide +kernel
      have hl : raw20132step3Labels = raw20132step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1746 node1746Labels := by rfl

def raw20133 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20133Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20133step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20133step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20133step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20133step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20133step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20133step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20133step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20133 raw20133Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw20133 raw20133Labels = mixedMoment B raw20133step0 raw20133step0Labels := by
      have hz : ∀ j, raw20133 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20133step0 = (fun i j => raw20133 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20133step0 raw20133; decide +kernel
      have hl : raw20133step0Labels = raw20133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20133 raw20133Labels permutation346 hz
    mixedMoment B raw20133step0 raw20133step0Labels = mixedMoment B raw20133step1 raw20133step1Labels := by
      have hz : ∀ j, raw20133step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20133step1 = (fun i j => raw20133step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20133step1 raw20133step0; decide +kernel
      have hl : raw20133step1Labels = raw20133step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20133step0 raw20133step0Labels permutation56 hz
    mixedMoment B raw20133step1 raw20133step1Labels = mixedMoment B raw20133step2 raw20133step2Labels := by
      have ha : raw20133step2 = (fun i j => raw20133step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20133step2 raw20133step1; decide +kernel
      have hl : raw20133step2Labels = raw20133step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20133step1 raw20133step1Labels permutation8 permutation4
    mixedMoment B raw20133step2 raw20133step2Labels = mixedMoment B raw20133step3 raw20133step3Labels := by
      have ha : raw20133step3 = -raw20133step2 := by apply Matrix.ext; change ∀ i j, raw20133step3 i j = -(raw20133step2 i j); unfold raw20133step3 raw20133step2; decide +kernel
      have hl : raw20133step3Labels = raw20133step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1750 node1750Labels := by rfl

def raw20134 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20134Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20134step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw20134step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20134step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw20134step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20134 raw20134Labels = mixedMoment B node1619 node1619Labels := by
  calc
    mixedMoment B raw20134 raw20134Labels = mixedMoment B raw20134step0 raw20134step0Labels := by
      have hz : ∀ j, raw20134 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20134step0 = (fun i j => raw20134 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20134step0 raw20134; decide +kernel
      have hl : raw20134step0Labels = raw20134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20134 raw20134Labels permutation346 hz
    mixedMoment B raw20134step0 raw20134step0Labels = mixedMoment B raw20134step1 raw20134step1Labels := by
      have ha : raw20134step1 = (fun i j => raw20134step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20134step1 raw20134step0; decide +kernel
      have hl : raw20134step1Labels = raw20134step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20134step0 raw20134step0Labels permutation33 permutation4
    mixedMoment B raw20134step1 raw20134step1Labels = mixedMoment B raw20134step2 raw20134step2Labels := by
      have ha : raw20134step2 = -raw20134step1 := by apply Matrix.ext; change ∀ i j, raw20134step2 i j = -(raw20134step1 i j); unfold raw20134step2 raw20134step1; decide +kernel
      have hl : raw20134step2Labels = raw20134step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1619 node1619Labels := by rfl

def raw20135 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20135Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20135step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw20135step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20135step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw20135step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20135 raw20135Labels = mixedMoment B node1619 node1619Labels := by
  calc
    mixedMoment B raw20135 raw20135Labels = mixedMoment B raw20135step0 raw20135step0Labels := by
      have hz : ∀ j, raw20135 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20135step0 = (fun i j => raw20135 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20135step0 raw20135; decide +kernel
      have hl : raw20135step0Labels = raw20135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20135 raw20135Labels permutation265 hz
    mixedMoment B raw20135step0 raw20135step0Labels = mixedMoment B raw20135step1 raw20135step1Labels := by
      have ha : raw20135step1 = (fun i j => raw20135step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20135step1 raw20135step0; decide +kernel
      have hl : raw20135step1Labels = raw20135step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20135step0 raw20135step0Labels permutation33 permutation4
    mixedMoment B raw20135step1 raw20135step1Labels = mixedMoment B raw20135step2 raw20135step2Labels := by
      have ha : raw20135step2 = -raw20135step1 := by apply Matrix.ext; change ∀ i j, raw20135step2 i j = -(raw20135step1 i j); unfold raw20135step2 raw20135step1; decide +kernel
      have hl : raw20135step2Labels = raw20135step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1619 node1619Labels := by rfl

def raw20136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw20136Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw20136step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20136step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw20136step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20136step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20136step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20136 raw20136Labels = mixedMoment B node606 node606Labels := by
  calc
    mixedMoment B raw20136 raw20136Labels = mixedMoment B raw20136step0 raw20136step0Labels := by
      have hz : ∀ j, raw20136 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20136step0 = (fun i j => raw20136 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20136step0 raw20136; decide +kernel
      have hl : raw20136step0Labels = raw20136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20136 raw20136Labels permutation346 hz
    mixedMoment B raw20136step0 raw20136step0Labels = mixedMoment B raw20136step1 raw20136step1Labels := by
      have hz : ∀ j, raw20136step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20136step1 = (fun i j => raw20136step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20136step1 raw20136step0; decide +kernel
      have hl : raw20136step1Labels = raw20136step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20136step0 raw20136step0Labels permutation56 hz
    mixedMoment B raw20136step1 raw20136step1Labels = mixedMoment B raw20136step2 raw20136step2Labels := by
      have ha : raw20136step2 = (fun i j => raw20136step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20136step2 raw20136step1; decide +kernel
      have hl : raw20136step2Labels = raw20136step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20136step1 raw20136step1Labels permutation10 permutation2
    _ = mixedMoment B node606 node606Labels := by rfl

def raw20137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw20137Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw20137step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20137step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20137 raw20137Labels = mixedMoment B node925 node925Labels := by
  calc
    mixedMoment B raw20137 raw20137Labels = mixedMoment B raw20137step0 raw20137step0Labels := by
      have hz : ∀ j, raw20137 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20137step0 = (fun i j => raw20137 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20137step0 raw20137; decide +kernel
      have hl : raw20137step0Labels = raw20137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20137 raw20137Labels permutation346 hz
    mixedMoment B raw20137step0 raw20137step0Labels = mixedMoment B raw20137step1 raw20137step1Labels := by
      have ha : raw20137step1 = (fun i j => raw20137step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20137step1 raw20137step0; decide +kernel
      have hl : raw20137step1Labels = raw20137step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20137step0 raw20137step0Labels permutation34 permutation2
    _ = mixedMoment B node925 node925Labels := by rfl

def raw20138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw20138Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw20138step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20138step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20138 raw20138Labels = mixedMoment B node925 node925Labels := by
  calc
    mixedMoment B raw20138 raw20138Labels = mixedMoment B raw20138step0 raw20138step0Labels := by
      have hz : ∀ j, raw20138 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20138step0 = (fun i j => raw20138 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20138step0 raw20138; decide +kernel
      have hl : raw20138step0Labels = raw20138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20138 raw20138Labels permutation265 hz
    mixedMoment B raw20138step0 raw20138step0Labels = mixedMoment B raw20138step1 raw20138step1Labels := by
      have ha : raw20138step1 = (fun i j => raw20138step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20138step1 raw20138step0; decide +kernel
      have hl : raw20138step1Labels = raw20138step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20138step0 raw20138step0Labels permutation34 permutation2
    _ = mixedMoment B node925 node925Labels := by rfl

def raw20139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw20139Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw20139step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20139step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw20139step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20139 raw20139Labels = mixedMoment B node1059 node1059Labels := by
  calc
    mixedMoment B raw20139 raw20139Labels = mixedMoment B raw20139step0 raw20139step0Labels := by
      have hz : ∀ j, raw20139 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20139step0 = (fun i j => raw20139 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20139step0 raw20139; decide +kernel
      have hl : raw20139step0Labels = raw20139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20139 raw20139Labels permutation346 hz
    mixedMoment B raw20139step0 raw20139step0Labels = mixedMoment B raw20139step1 raw20139step1Labels := by
      have hz : ∀ j, raw20139step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20139step1 = (fun i j => raw20139step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20139step1 raw20139step0; decide +kernel
      have hl : raw20139step1Labels = raw20139step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20139step0 raw20139step0Labels permutation56 hz
    _ = mixedMoment B node1059 node1059Labels := by rfl

def raw20140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![3, -2, -1]]
def raw20140Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20140step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20140step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20140step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20140step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw20140step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20140 raw20140Labels = mixedMoment B node1091 node1091Labels := by
  calc
    mixedMoment B raw20140 raw20140Labels = mixedMoment B raw20140step0 raw20140step0Labels := by
      have hz : ∀ j, raw20140 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20140step0 = (fun i j => raw20140 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20140step0 raw20140; decide +kernel
      have hl : raw20140step0Labels = raw20140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20140 raw20140Labels permutation520 hz
    mixedMoment B raw20140step0 raw20140step0Labels = mixedMoment B raw20140step1 raw20140step1Labels := by
      have hz : ∀ j, raw20140step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20140step1 = (fun i j => raw20140step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20140step1 raw20140step0; decide +kernel
      have hl : raw20140step1Labels = raw20140step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20140step0 raw20140step0Labels permutation80 hz
    mixedMoment B raw20140step1 raw20140step1Labels = mixedMoment B raw20140step2 raw20140step2Labels := by
      have hz : ∀ j, raw20140step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20140step2 = (fun i j => raw20140step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20140step2 raw20140step1; decide +kernel
      have hl : raw20140step2Labels = raw20140step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20140step1 raw20140step1Labels permutation14 hz
    _ = mixedMoment B node1091 node1091Labels := by rfl

def raw20141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw20141Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw20141step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20141step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw20141step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20141step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw20141step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20141 raw20141Labels = mixedMoment B node1083 node1083Labels := by
  calc
    mixedMoment B raw20141 raw20141Labels = mixedMoment B raw20141step0 raw20141step0Labels := by
      have hz : ∀ j, raw20141 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20141step0 = (fun i j => raw20141 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20141step0 raw20141; decide +kernel
      have hl : raw20141step0Labels = raw20141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20141 raw20141Labels permutation346 hz
    mixedMoment B raw20141step0 raw20141step0Labels = mixedMoment B raw20141step1 raw20141step1Labels := by
      have hz : ∀ j, raw20141step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20141step1 = (fun i j => raw20141step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20141step1 raw20141step0; decide +kernel
      have hl : raw20141step1Labels = raw20141step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20141step0 raw20141step0Labels permutation56 hz
    mixedMoment B raw20141step1 raw20141step1Labels = mixedMoment B raw20141step2 raw20141step2Labels := by
      have ha : raw20141step2 = (fun i j => raw20141step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20141step2 raw20141step1; decide +kernel
      have hl : raw20141step2Labels = raw20141step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20141step1 raw20141step1Labels permutation10 permutation2
    _ = mixedMoment B node1083 node1083Labels := by rfl

def raw20142 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![0, 0], ![1, -1]]
def raw20142Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20142step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]
def raw20142step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20142step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1]]
def raw20142step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20142step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw20142step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20142step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw20142step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20142 raw20142Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw20142 raw20142Labels = mixedMoment B raw20142step0 raw20142step0Labels := by
      have hz : ∀ j, raw20142 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20142step0 = (fun i j => raw20142 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20142step0 raw20142; decide +kernel
      have hl : raw20142step0Labels = raw20142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20142 raw20142Labels permutation520 hz
    mixedMoment B raw20142step0 raw20142step0Labels = mixedMoment B raw20142step1 raw20142step1Labels := by
      have hz : ∀ j, raw20142step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20142step1 = (fun i j => raw20142step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20142step1 raw20142step0; decide +kernel
      have hl : raw20142step1Labels = raw20142step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20142step0 raw20142step0Labels permutation80 hz
    mixedMoment B raw20142step1 raw20142step1Labels = mixedMoment B raw20142step2 raw20142step2Labels := by
      have hz : ∀ j, raw20142step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20142step2 = (fun i j => raw20142step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20142step2 raw20142step1; decide +kernel
      have hl : raw20142step2Labels = raw20142step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20142step1 raw20142step1Labels permutation14 hz
    mixedMoment B raw20142step2 raw20142step2Labels = mixedMoment B raw20142step3 raw20142step3Labels := by
      have ha : raw20142step3 = (fun i j => raw20142step2 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20142step3 raw20142step2; decide +kernel
      have hl : raw20142step3Labels = raw20142step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20142step2 raw20142step2Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw20143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20143Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20143step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20143step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20143step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20143step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw20143step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20143step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20143step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20143 raw20143Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw20143 raw20143Labels = mixedMoment B raw20143step0 raw20143step0Labels := by
      have hz : ∀ j, raw20143 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20143step0 = (fun i j => raw20143 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20143step0 raw20143; decide +kernel
      have hl : raw20143step0Labels = raw20143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20143 raw20143Labels permutation346 hz
    mixedMoment B raw20143step0 raw20143step0Labels = mixedMoment B raw20143step1 raw20143step1Labels := by
      have hz : ∀ j, raw20143step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20143step1 = (fun i j => raw20143step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20143step1 raw20143step0; decide +kernel
      have hl : raw20143step1Labels = raw20143step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20143step0 raw20143step0Labels permutation56 hz
    mixedMoment B raw20143step1 raw20143step1Labels = mixedMoment B raw20143step2 raw20143step2Labels := by
      have ha : raw20143step2 = (fun i j => raw20143step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20143step2 raw20143step1; decide +kernel
      have hl : raw20143step2Labels = raw20143step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20143step1 raw20143step1Labels permutation31 permutation2
    mixedMoment B raw20143step2 raw20143step2Labels = mixedMoment B raw20143step3 raw20143step3Labels := by
      have ha : raw20143step3 = -raw20143step2 := by apply Matrix.ext; change ∀ i j, raw20143step3 i j = -(raw20143step2 i j); unfold raw20143step3 raw20143step2; decide +kernel
      have hl : raw20143step3Labels = raw20143step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2519 node2519Labels := by rfl

def raw20144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20144Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20144step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20144step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20144 raw20144Labels = mixedMoment B node1317 node1317Labels := by
  calc
    mixedMoment B raw20144 raw20144Labels = mixedMoment B raw20144step0 raw20144step0Labels := by
      have hz : ∀ j, raw20144 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20144step0 = (fun i j => raw20144 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20144step0 raw20144; decide +kernel
      have hl : raw20144step0Labels = raw20144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20144 raw20144Labels permutation346 hz
    mixedMoment B raw20144step0 raw20144step0Labels = mixedMoment B raw20144step1 raw20144step1Labels := by
      have ha : raw20144step1 = (fun i j => raw20144step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20144step1 raw20144step0; decide +kernel
      have hl : raw20144step1Labels = raw20144step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20144step0 raw20144step0Labels permutation38 permutation2
    _ = mixedMoment B node1317 node1317Labels := by rfl

def raw20145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20145Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20145step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20145step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20145 raw20145Labels = mixedMoment B node1317 node1317Labels := by
  calc
    mixedMoment B raw20145 raw20145Labels = mixedMoment B raw20145step0 raw20145step0Labels := by
      have hz : ∀ j, raw20145 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20145step0 = (fun i j => raw20145 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20145step0 raw20145; decide +kernel
      have hl : raw20145step0Labels = raw20145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20145 raw20145Labels permutation265 hz
    mixedMoment B raw20145step0 raw20145step0Labels = mixedMoment B raw20145step1 raw20145step1Labels := by
      have ha : raw20145step1 = (fun i j => raw20145step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20145step1 raw20145step0; decide +kernel
      have hl : raw20145step1Labels = raw20145step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20145step0 raw20145step0Labels permutation38 permutation2
    _ = mixedMoment B node1317 node1317Labels := by rfl

def raw20146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def raw20146Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def raw20146step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20146step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def raw20146step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20146 raw20146Labels = mixedMoment B node1324 node1324Labels := by
  calc
    mixedMoment B raw20146 raw20146Labels = mixedMoment B raw20146step0 raw20146step0Labels := by
      have hz : ∀ j, raw20146 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20146step0 = (fun i j => raw20146 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20146step0 raw20146; decide +kernel
      have hl : raw20146step0Labels = raw20146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20146 raw20146Labels permutation346 hz
    mixedMoment B raw20146step0 raw20146step0Labels = mixedMoment B raw20146step1 raw20146step1Labels := by
      have hz : ∀ j, raw20146step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20146step1 = (fun i j => raw20146step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20146step1 raw20146step0; decide +kernel
      have hl : raw20146step1Labels = raw20146step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20146step0 raw20146step0Labels permutation56 hz
    _ = mixedMoment B node1324 node1324Labels := by rfl

def raw20147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![4, -2, -2]]
def raw20147Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![4, -2, -2]]
def raw20147step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20147step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![4, -2, -2]]
def raw20147step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20147step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, -1, 2], ![-4, 3, 1]]
def raw20147step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20147step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![4, -3, -1]]
def raw20147step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20147 raw20147Labels = mixedMoment B node1142 node1142Labels := by
  calc
    mixedMoment B raw20147 raw20147Labels = mixedMoment B raw20147step0 raw20147step0Labels := by
      have hz : ∀ j, raw20147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20147step0 = (fun i j => raw20147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20147step0 raw20147; decide +kernel
      have hl : raw20147step0Labels = raw20147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20147 raw20147Labels permutation346 hz
    mixedMoment B raw20147step0 raw20147step0Labels = mixedMoment B raw20147step1 raw20147step1Labels := by
      have hz : ∀ j, raw20147step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20147step1 = (fun i j => raw20147step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20147step1 raw20147step0; decide +kernel
      have hl : raw20147step1Labels = raw20147step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20147step0 raw20147step0Labels permutation56 hz
    mixedMoment B raw20147step1 raw20147step1Labels = mixedMoment B raw20147step2 raw20147step2Labels := by
      have ha : raw20147step2 = (fun i j => raw20147step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20147step2 raw20147step1; decide +kernel
      have hl : raw20147step2Labels = raw20147step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20147step1 raw20147step1Labels permutation31 permutation2
    mixedMoment B raw20147step2 raw20147step2Labels = mixedMoment B raw20147step3 raw20147step3Labels := by
      have ha : raw20147step3 = -raw20147step2 := by apply Matrix.ext; change ∀ i j, raw20147step3 i j = -(raw20147step2 i j); unfold raw20147step3 raw20147step2; decide +kernel
      have hl : raw20147step3Labels = raw20147step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1142 node1142Labels := by rfl

def raw20148 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20148Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20148step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20148step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20148step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20148step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw20148step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20148step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw20148step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20148 raw20148Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw20148 raw20148Labels = mixedMoment B raw20148step0 raw20148step0Labels := by
      have hz : ∀ j, raw20148 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20148step0 = (fun i j => raw20148 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20148step0 raw20148; decide +kernel
      have hl : raw20148step0Labels = raw20148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20148 raw20148Labels permutation346 hz
    mixedMoment B raw20148step0 raw20148step0Labels = mixedMoment B raw20148step1 raw20148step1Labels := by
      have hz : ∀ j, raw20148step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20148step1 = (fun i j => raw20148step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20148step1 raw20148step0; decide +kernel
      have hl : raw20148step1Labels = raw20148step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20148step0 raw20148step0Labels permutation56 hz
    mixedMoment B raw20148step1 raw20148step1Labels = mixedMoment B raw20148step2 raw20148step2Labels := by
      have ha : raw20148step2 = (fun i j => raw20148step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20148step2 raw20148step1; decide +kernel
      have hl : raw20148step2Labels = raw20148step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20148step1 raw20148step1Labels permutation11 permutation4
    mixedMoment B raw20148step2 raw20148step2Labels = mixedMoment B raw20148step3 raw20148step3Labels := by
      have ha : raw20148step3 = -raw20148step2 := by apply Matrix.ext; change ∀ i j, raw20148step3 i j = -(raw20148step2 i j); unfold raw20148step3 raw20148step2; decide +kernel
      have hl : raw20148step3Labels = raw20148step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1729 node1729Labels := by rfl

def raw20149 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20149Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20149step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20149step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20149step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20149step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20149 raw20149Labels = mixedMoment B node3242 node3242Labels := by
  calc
    mixedMoment B raw20149 raw20149Labels = mixedMoment B raw20149step0 raw20149step0Labels := by
      have hz : ∀ j, raw20149 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20149step0 = (fun i j => raw20149 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20149step0 raw20149; decide +kernel
      have hl : raw20149step0Labels = raw20149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20149 raw20149Labels permutation346 hz
    mixedMoment B raw20149step0 raw20149step0Labels = mixedMoment B raw20149step1 raw20149step1Labels := by
      have ha : raw20149step1 = (fun i j => raw20149step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20149step1 raw20149step0; decide +kernel
      have hl : raw20149step1Labels = raw20149step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20149step0 raw20149step0Labels permutation38 permutation2
    mixedMoment B raw20149step1 raw20149step1Labels = mixedMoment B raw20149step2 raw20149step2Labels := by
      have ha : raw20149step2 = -raw20149step1 := by apply Matrix.ext; change ∀ i j, raw20149step2 i j = -(raw20149step1 i j); unfold raw20149step2 raw20149step1; decide +kernel
      have hl : raw20149step2Labels = raw20149step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3242 node3242Labels := by rfl

def raw20150 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20150Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20150step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20150step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20150step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20150 raw20150Labels = mixedMoment B node3242 node3242Labels := by
  calc
    mixedMoment B raw20150 raw20150Labels = mixedMoment B raw20150step0 raw20150step0Labels := by
      have hz : ∀ j, raw20150 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20150step0 = (fun i j => raw20150 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20150step0 raw20150; decide +kernel
      have hl : raw20150step0Labels = raw20150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20150 raw20150Labels permutation265 hz
    mixedMoment B raw20150step0 raw20150step0Labels = mixedMoment B raw20150step1 raw20150step1Labels := by
      have ha : raw20150step1 = (fun i j => raw20150step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20150step1 raw20150step0; decide +kernel
      have hl : raw20150step1Labels = raw20150step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20150step0 raw20150step0Labels permutation38 permutation2
    mixedMoment B raw20150step1 raw20150step1Labels = mixedMoment B raw20150step2 raw20150step2Labels := by
      have ha : raw20150step2 = -raw20150step1 := by apply Matrix.ext; change ∀ i j, raw20150step2 i j = -(raw20150step1 i j); unfold raw20150step2 raw20150step1; decide +kernel
      have hl : raw20150step2Labels = raw20150step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3242 node3242Labels := by rfl

def raw20151 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20151Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20151step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20151step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20151step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20151step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20151step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20151 raw20151Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw20151 raw20151Labels = mixedMoment B raw20151step0 raw20151step0Labels := by
      have hz : ∀ j, raw20151 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20151step0 = (fun i j => raw20151 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20151step0 raw20151; decide +kernel
      have hl : raw20151step0Labels = raw20151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20151 raw20151Labels permutation346 hz
    mixedMoment B raw20151step0 raw20151step0Labels = mixedMoment B raw20151step1 raw20151step1Labels := by
      have hz : ∀ j, raw20151step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20151step1 = (fun i j => raw20151step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20151step1 raw20151step0; decide +kernel
      have hl : raw20151step1Labels = raw20151step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20151step0 raw20151step0Labels permutation56 hz
    mixedMoment B raw20151step1 raw20151step1Labels = mixedMoment B raw20151step2 raw20151step2Labels := by
      have ha : raw20151step2 = -raw20151step1 := by apply Matrix.ext; change ∀ i j, raw20151step2 i j = -(raw20151step1 i j); unfold raw20151step2 raw20151step1; decide +kernel
      have hl : raw20151step2Labels = raw20151step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3300 node3300Labels := by rfl

def raw20152 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw20152Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw20152step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20152step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw20152step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20152step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![2, -1, -1], ![2, 1, -3]]
def raw20152step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20152 raw20152Labels = mixedMoment B node3247 node3247Labels := by
  calc
    mixedMoment B raw20152 raw20152Labels = mixedMoment B raw20152step0 raw20152step0Labels := by
      have hz : ∀ j, raw20152 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20152step0 = (fun i j => raw20152 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20152step0 raw20152; decide +kernel
      have hl : raw20152step0Labels = raw20152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20152 raw20152Labels permutation346 hz
    mixedMoment B raw20152step0 raw20152step0Labels = mixedMoment B raw20152step1 raw20152step1Labels := by
      have hz : ∀ j, raw20152step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20152step1 = (fun i j => raw20152step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20152step1 raw20152step0; decide +kernel
      have hl : raw20152step1Labels = raw20152step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20152step0 raw20152step0Labels permutation56 hz
    mixedMoment B raw20152step1 raw20152step1Labels = mixedMoment B raw20152step2 raw20152step2Labels := by
      have ha : raw20152step2 = -raw20152step1 := by apply Matrix.ext; change ∀ i j, raw20152step2 i j = -(raw20152step1 i j); unfold raw20152step2 raw20152step1; decide +kernel
      have hl : raw20152step2Labels = raw20152step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3247 node3247Labels := by rfl

def raw20153 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw20153Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw20153step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20153step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw20153step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20153step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![2, -2, 0], ![2, 2, -4]]
def raw20153step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20153 raw20153Labels = mixedMoment B node1952 node1952Labels := by
  calc
    mixedMoment B raw20153 raw20153Labels = mixedMoment B raw20153step0 raw20153step0Labels := by
      have hz : ∀ j, raw20153 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20153step0 = (fun i j => raw20153 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20153step0 raw20153; decide +kernel
      have hl : raw20153step0Labels = raw20153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20153 raw20153Labels permutation346 hz
    mixedMoment B raw20153step0 raw20153step0Labels = mixedMoment B raw20153step1 raw20153step1Labels := by
      have hz : ∀ j, raw20153step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20153step1 = (fun i j => raw20153step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20153step1 raw20153step0; decide +kernel
      have hl : raw20153step1Labels = raw20153step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20153step0 raw20153step0Labels permutation56 hz
    mixedMoment B raw20153step1 raw20153step1Labels = mixedMoment B raw20153step2 raw20153step2Labels := by
      have ha : raw20153step2 = (fun i j => raw20153step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20153step2 raw20153step1; decide +kernel
      have hl : raw20153step2Labels = raw20153step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20153step1 raw20153step1Labels permutation31 permutation2
    _ = mixedMoment B node1952 node1952Labels := by rfl

def raw20154 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20154Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20154step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw20154step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20154step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw20154step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20154 raw20154Labels = mixedMoment B node808 node808Labels := by
  calc
    mixedMoment B raw20154 raw20154Labels = mixedMoment B raw20154step0 raw20154step0Labels := by
      have hz : ∀ j, raw20154 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20154step0 = (fun i j => raw20154 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20154step0 raw20154; decide +kernel
      have hl : raw20154step0Labels = raw20154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20154 raw20154Labels permutation346 hz
    mixedMoment B raw20154step0 raw20154step0Labels = mixedMoment B raw20154step1 raw20154step1Labels := by
      have ha : raw20154step1 = (fun i j => raw20154step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20154step1 raw20154step0; decide +kernel
      have hl : raw20154step1Labels = raw20154step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20154step0 raw20154step0Labels permutation45 permutation4
    mixedMoment B raw20154step1 raw20154step1Labels = mixedMoment B raw20154step2 raw20154step2Labels := by
      have ha : raw20154step2 = -raw20154step1 := by apply Matrix.ext; change ∀ i j, raw20154step2 i j = -(raw20154step1 i j); unfold raw20154step2 raw20154step1; decide +kernel
      have hl : raw20154step2Labels = raw20154step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node808 node808Labels := by rfl

def raw20155 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20155Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20155step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw20155step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20155step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw20155step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20155 raw20155Labels = mixedMoment B node808 node808Labels := by
  calc
    mixedMoment B raw20155 raw20155Labels = mixedMoment B raw20155step0 raw20155step0Labels := by
      have hz : ∀ j, raw20155 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20155step0 = (fun i j => raw20155 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20155step0 raw20155; decide +kernel
      have hl : raw20155step0Labels = raw20155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20155 raw20155Labels permutation265 hz
    mixedMoment B raw20155step0 raw20155step0Labels = mixedMoment B raw20155step1 raw20155step1Labels := by
      have ha : raw20155step1 = (fun i j => raw20155step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20155step1 raw20155step0; decide +kernel
      have hl : raw20155step1Labels = raw20155step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20155step0 raw20155step0Labels permutation45 permutation4
    mixedMoment B raw20155step1 raw20155step1Labels = mixedMoment B raw20155step2 raw20155step2Labels := by
      have ha : raw20155step2 = -raw20155step1 := by apply Matrix.ext; change ∀ i j, raw20155step2 i j = -(raw20155step1 i j); unfold raw20155step2 raw20155step1; decide +kernel
      have hl : raw20155step2Labels = raw20155step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node808 node808Labels := by rfl

def raw20156 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20156Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20156step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20156step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![3, -3, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20156step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20156step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, -2, 3], ![-3, 3, 0]]
def raw20156step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20156step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def raw20156step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20156 raw20156Labels = mixedMoment B node814 node814Labels := by
  calc
    mixedMoment B raw20156 raw20156Labels = mixedMoment B raw20156step0 raw20156step0Labels := by
      have hz : ∀ j, raw20156 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20156step0 = (fun i j => raw20156 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20156step0 raw20156; decide +kernel
      have hl : raw20156step0Labels = raw20156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20156 raw20156Labels permutation346 hz
    mixedMoment B raw20156step0 raw20156step0Labels = mixedMoment B raw20156step1 raw20156step1Labels := by
      have hz : ∀ j, raw20156step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20156step1 = (fun i j => raw20156step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20156step1 raw20156step0; decide +kernel
      have hl : raw20156step1Labels = raw20156step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20156step0 raw20156step0Labels permutation56 hz
    mixedMoment B raw20156step1 raw20156step1Labels = mixedMoment B raw20156step2 raw20156step2Labels := by
      have ha : raw20156step2 = (fun i j => raw20156step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20156step2 raw20156step1; decide +kernel
      have hl : raw20156step2Labels = raw20156step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20156step1 raw20156step1Labels permutation11 permutation4
    mixedMoment B raw20156step2 raw20156step2Labels = mixedMoment B raw20156step3 raw20156step3Labels := by
      have ha : raw20156step3 = -raw20156step2 := by apply Matrix.ext; change ∀ i j, raw20156step3 i j = -(raw20156step2 i j); unfold raw20156step3 raw20156step2; decide +kernel
      have hl : raw20156step3Labels = raw20156step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node814 node814Labels := by rfl

def raw20157 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20157Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20157step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20157step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20157step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20157step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw20157step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20157step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw20157step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20157 raw20157Labels = mixedMoment B node857 node857Labels := by
  calc
    mixedMoment B raw20157 raw20157Labels = mixedMoment B raw20157step0 raw20157step0Labels := by
      have hz : ∀ j, raw20157 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20157step0 = (fun i j => raw20157 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20157step0 raw20157; decide +kernel
      have hl : raw20157step0Labels = raw20157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20157 raw20157Labels permutation346 hz
    mixedMoment B raw20157step0 raw20157step0Labels = mixedMoment B raw20157step1 raw20157step1Labels := by
      have hz : ∀ j, raw20157step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20157step1 = (fun i j => raw20157step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20157step1 raw20157step0; decide +kernel
      have hl : raw20157step1Labels = raw20157step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20157step0 raw20157step0Labels permutation56 hz
    mixedMoment B raw20157step1 raw20157step1Labels = mixedMoment B raw20157step2 raw20157step2Labels := by
      have ha : raw20157step2 = (fun i j => raw20157step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20157step2 raw20157step1; decide +kernel
      have hl : raw20157step2Labels = raw20157step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20157step1 raw20157step1Labels permutation11 permutation4
    mixedMoment B raw20157step2 raw20157step2Labels = mixedMoment B raw20157step3 raw20157step3Labels := by
      have ha : raw20157step3 = -raw20157step2 := by apply Matrix.ext; change ∀ i j, raw20157step3 i j = -(raw20157step2 i j); unfold raw20157step3 raw20157step2; decide +kernel
      have hl : raw20157step3Labels = raw20157step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node857 node857Labels := by rfl

def raw20158 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20158Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20158step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20158step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20158step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20158step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw20158step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20158step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw20158step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20158 raw20158Labels = mixedMoment B node815 node815Labels := by
  calc
    mixedMoment B raw20158 raw20158Labels = mixedMoment B raw20158step0 raw20158step0Labels := by
      have hz : ∀ j, raw20158 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20158step0 = (fun i j => raw20158 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20158step0 raw20158; decide +kernel
      have hl : raw20158step0Labels = raw20158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20158 raw20158Labels permutation346 hz
    mixedMoment B raw20158step0 raw20158step0Labels = mixedMoment B raw20158step1 raw20158step1Labels := by
      have hz : ∀ j, raw20158step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20158step1 = (fun i j => raw20158step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20158step1 raw20158step0; decide +kernel
      have hl : raw20158step1Labels = raw20158step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20158step0 raw20158step0Labels permutation56 hz
    mixedMoment B raw20158step1 raw20158step1Labels = mixedMoment B raw20158step2 raw20158step2Labels := by
      have ha : raw20158step2 = (fun i j => raw20158step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20158step2 raw20158step1; decide +kernel
      have hl : raw20158step2Labels = raw20158step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20158step1 raw20158step1Labels permutation10 permutation4
    mixedMoment B raw20158step2 raw20158step2Labels = mixedMoment B raw20158step3 raw20158step3Labels := by
      have ha : raw20158step3 = -raw20158step2 := by apply Matrix.ext; change ∀ i j, raw20158step3 i j = -(raw20158step2 i j); unfold raw20158step3 raw20158step2; decide +kernel
      have hl : raw20158step3Labels = raw20158step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node815 node815Labels := by rfl

def raw20159 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20159Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20159step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw20159step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20159step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw20159step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20159 raw20159Labels = mixedMoment B node1723 node1723Labels := by
  calc
    mixedMoment B raw20159 raw20159Labels = mixedMoment B raw20159step0 raw20159step0Labels := by
      have hz : ∀ j, raw20159 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20159step0 = (fun i j => raw20159 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20159step0 raw20159; decide +kernel
      have hl : raw20159step0Labels = raw20159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20159 raw20159Labels permutation346 hz
    mixedMoment B raw20159step0 raw20159step0Labels = mixedMoment B raw20159step1 raw20159step1Labels := by
      have ha : raw20159step1 = (fun i j => raw20159step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20159step1 raw20159step0; decide +kernel
      have hl : raw20159step1Labels = raw20159step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20159step0 raw20159step0Labels permutation44 permutation4
    mixedMoment B raw20159step1 raw20159step1Labels = mixedMoment B raw20159step2 raw20159step2Labels := by
      have ha : raw20159step2 = -raw20159step1 := by apply Matrix.ext; change ∀ i j, raw20159step2 i j = -(raw20159step1 i j); unfold raw20159step2 raw20159step1; decide +kernel
      have hl : raw20159step2Labels = raw20159step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1723 node1723Labels := by rfl

def raw20160 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20160Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20160step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw20160step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20160step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw20160step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20160 raw20160Labels = mixedMoment B node1723 node1723Labels := by
  calc
    mixedMoment B raw20160 raw20160Labels = mixedMoment B raw20160step0 raw20160step0Labels := by
      have hz : ∀ j, raw20160 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20160step0 = (fun i j => raw20160 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20160step0 raw20160; decide +kernel
      have hl : raw20160step0Labels = raw20160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20160 raw20160Labels permutation265 hz
    mixedMoment B raw20160step0 raw20160step0Labels = mixedMoment B raw20160step1 raw20160step1Labels := by
      have ha : raw20160step1 = (fun i j => raw20160step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20160step1 raw20160step0; decide +kernel
      have hl : raw20160step1Labels = raw20160step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20160step0 raw20160step0Labels permutation44 permutation4
    mixedMoment B raw20160step1 raw20160step1Labels = mixedMoment B raw20160step2 raw20160step2Labels := by
      have ha : raw20160step2 = -raw20160step1 := by apply Matrix.ext; change ∀ i j, raw20160step2 i j = -(raw20160step1 i j); unfold raw20160step2 raw20160step1; decide +kernel
      have hl : raw20160step2Labels = raw20160step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1723 node1723Labels := by rfl

def raw20161 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20161Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20161step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20161step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20161step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20161step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw20161step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20161step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20161step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20161 raw20161Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw20161 raw20161Labels = mixedMoment B raw20161step0 raw20161step0Labels := by
      have hz : ∀ j, raw20161 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20161step0 = (fun i j => raw20161 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20161step0 raw20161; decide +kernel
      have hl : raw20161step0Labels = raw20161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20161 raw20161Labels permutation346 hz
    mixedMoment B raw20161step0 raw20161step0Labels = mixedMoment B raw20161step1 raw20161step1Labels := by
      have hz : ∀ j, raw20161step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20161step1 = (fun i j => raw20161step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20161step1 raw20161step0; decide +kernel
      have hl : raw20161step1Labels = raw20161step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20161step0 raw20161step0Labels permutation56 hz
    mixedMoment B raw20161step1 raw20161step1Labels = mixedMoment B raw20161step2 raw20161step2Labels := by
      have ha : raw20161step2 = (fun i j => raw20161step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20161step2 raw20161step1; decide +kernel
      have hl : raw20161step2Labels = raw20161step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20161step1 raw20161step1Labels permutation10 permutation4
    mixedMoment B raw20161step2 raw20161step2Labels = mixedMoment B raw20161step3 raw20161step3Labels := by
      have ha : raw20161step3 = -raw20161step2 := by apply Matrix.ext; change ∀ i j, raw20161step3 i j = -(raw20161step2 i j); unfold raw20161step3 raw20161step2; decide +kernel
      have hl : raw20161step3Labels = raw20161step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1725 node1725Labels := by rfl

def raw20162 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20162Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20162step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw20162step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw20162step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20162 raw20162Labels = mixedMoment B node1624 node1624Labels := by
  calc
    mixedMoment B raw20162 raw20162Labels = mixedMoment B raw20162step0 raw20162step0Labels := by
      have hz : ∀ j, raw20162 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20162step0 = (fun i j => raw20162 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20162step0 raw20162; decide +kernel
      have hl : raw20162step0Labels = raw20162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20162 raw20162Labels permutation346 hz
    mixedMoment B raw20162step0 raw20162step0Labels = mixedMoment B raw20162step1 raw20162step1Labels := by
      have ha : raw20162step1 = (fun i j => raw20162step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20162step1 raw20162step0; decide +kernel
      have hl : raw20162step1Labels = raw20162step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20162step0 raw20162step0Labels permutation35 permutation4
    mixedMoment B raw20162step1 raw20162step1Labels = mixedMoment B raw20162step2 raw20162step2Labels := by
      have ha : raw20162step2 = -raw20162step1 := by apply Matrix.ext; change ∀ i j, raw20162step2 i j = -(raw20162step1 i j); unfold raw20162step2 raw20162step1; decide +kernel
      have hl : raw20162step2Labels = raw20162step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1624 node1624Labels := by rfl

def raw20163 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20163Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20163step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw20163step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20163step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw20163step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20163 raw20163Labels = mixedMoment B node1624 node1624Labels := by
  calc
    mixedMoment B raw20163 raw20163Labels = mixedMoment B raw20163step0 raw20163step0Labels := by
      have hz : ∀ j, raw20163 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20163step0 = (fun i j => raw20163 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20163step0 raw20163; decide +kernel
      have hl : raw20163step0Labels = raw20163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20163 raw20163Labels permutation265 hz
    mixedMoment B raw20163step0 raw20163step0Labels = mixedMoment B raw20163step1 raw20163step1Labels := by
      have ha : raw20163step1 = (fun i j => raw20163step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20163step1 raw20163step0; decide +kernel
      have hl : raw20163step1Labels = raw20163step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20163step0 raw20163step0Labels permutation35 permutation4
    mixedMoment B raw20163step1 raw20163step1Labels = mixedMoment B raw20163step2 raw20163step2Labels := by
      have ha : raw20163step2 = -raw20163step1 := by apply Matrix.ext; change ∀ i j, raw20163step2 i j = -(raw20163step1 i j); unfold raw20163step2 raw20163step1; decide +kernel
      have hl : raw20163step2Labels = raw20163step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1624 node1624Labels := by rfl

def raw20164 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20164Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20164step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw20164step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20164step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw20164step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20164 raw20164Labels = mixedMoment B node1604 node1604Labels := by
  calc
    mixedMoment B raw20164 raw20164Labels = mixedMoment B raw20164step0 raw20164step0Labels := by
      have hz : ∀ j, raw20164 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20164step0 = (fun i j => raw20164 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20164step0 raw20164; decide +kernel
      have hl : raw20164step0Labels = raw20164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20164 raw20164Labels permutation346 hz
    mixedMoment B raw20164step0 raw20164step0Labels = mixedMoment B raw20164step1 raw20164step1Labels := by
      have ha : raw20164step1 = (fun i j => raw20164step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20164step1 raw20164step0; decide +kernel
      have hl : raw20164step1Labels = raw20164step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20164step0 raw20164step0Labels permutation34 permutation4
    mixedMoment B raw20164step1 raw20164step1Labels = mixedMoment B raw20164step2 raw20164step2Labels := by
      have ha : raw20164step2 = -raw20164step1 := by apply Matrix.ext; change ∀ i j, raw20164step2 i j = -(raw20164step1 i j); unfold raw20164step2 raw20164step1; decide +kernel
      have hl : raw20164step2Labels = raw20164step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1604 node1604Labels := by rfl

def raw20165 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20165Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20165step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw20165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20165step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw20165step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20165 raw20165Labels = mixedMoment B node1604 node1604Labels := by
  calc
    mixedMoment B raw20165 raw20165Labels = mixedMoment B raw20165step0 raw20165step0Labels := by
      have hz : ∀ j, raw20165 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20165step0 = (fun i j => raw20165 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20165step0 raw20165; decide +kernel
      have hl : raw20165step0Labels = raw20165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20165 raw20165Labels permutation265 hz
    mixedMoment B raw20165step0 raw20165step0Labels = mixedMoment B raw20165step1 raw20165step1Labels := by
      have ha : raw20165step1 = (fun i j => raw20165step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20165step1 raw20165step0; decide +kernel
      have hl : raw20165step1Labels = raw20165step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20165step0 raw20165step0Labels permutation34 permutation4
    mixedMoment B raw20165step1 raw20165step1Labels = mixedMoment B raw20165step2 raw20165step2Labels := by
      have ha : raw20165step2 = -raw20165step1 := by apply Matrix.ext; change ∀ i j, raw20165step2 i j = -(raw20165step1 i j); unfold raw20165step2 raw20165step1; decide +kernel
      have hl : raw20165step2Labels = raw20165step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1604 node1604Labels := by rfl

def raw20166 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20166Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20166step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20166step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20166step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw20166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20166step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -2, 0], ![2, 1, -3]]
def raw20166step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20166 raw20166Labels = mixedMoment B node1652 node1652Labels := by
  calc
    mixedMoment B raw20166 raw20166Labels = mixedMoment B raw20166step0 raw20166step0Labels := by
      have hz : ∀ j, raw20166 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20166step0 = (fun i j => raw20166 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20166step0 raw20166; decide +kernel
      have hl : raw20166step0Labels = raw20166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20166 raw20166Labels permutation346 hz
    mixedMoment B raw20166step0 raw20166step0Labels = mixedMoment B raw20166step1 raw20166step1Labels := by
      have hz : ∀ j, raw20166step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20166step1 = (fun i j => raw20166step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20166step1 raw20166step0; decide +kernel
      have hl : raw20166step1Labels = raw20166step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20166step0 raw20166step0Labels permutation56 hz
    mixedMoment B raw20166step1 raw20166step1Labels = mixedMoment B raw20166step2 raw20166step2Labels := by
      have ha : raw20166step2 = (fun i j => raw20166step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20166step2 raw20166step1; decide +kernel
      have hl : raw20166step2Labels = raw20166step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20166step1 raw20166step1Labels permutation10 permutation4
    mixedMoment B raw20166step2 raw20166step2Labels = mixedMoment B raw20166step3 raw20166step3Labels := by
      have ha : raw20166step3 = -raw20166step2 := by apply Matrix.ext; change ∀ i j, raw20166step3 i j = -(raw20166step2 i j); unfold raw20166step3 raw20166step2; decide +kernel
      have hl : raw20166step3Labels = raw20166step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1652 node1652Labels := by rfl

def raw20167 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw20167Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw20167step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -3, 3], ![-1, 1, 0], ![-2, 2, 0]]
def raw20167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20167step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw20167step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20167 raw20167Labels = mixedMoment B node1718 node1718Labels := by
  calc
    mixedMoment B raw20167 raw20167Labels = mixedMoment B raw20167step0 raw20167step0Labels := by
      have hz : ∀ j, raw20167 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20167step0 = (fun i j => raw20167 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20167step0 raw20167; decide +kernel
      have hl : raw20167step0Labels = raw20167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20167 raw20167Labels permutation346 hz
    mixedMoment B raw20167step0 raw20167step0Labels = mixedMoment B raw20167step1 raw20167step1Labels := by
      have ha : raw20167step1 = (fun i j => raw20167step0 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20167step1 raw20167step0; decide +kernel
      have hl : raw20167step1Labels = raw20167step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20167step0 raw20167step0Labels permutation48 permutation4
    mixedMoment B raw20167step1 raw20167step1Labels = mixedMoment B raw20167step2 raw20167step2Labels := by
      have ha : raw20167step2 = -raw20167step1 := by apply Matrix.ext; change ∀ i j, raw20167step2 i j = -(raw20167step1 i j); unfold raw20167step2 raw20167step1; decide +kernel
      have hl : raw20167step2Labels = raw20167step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1718 node1718Labels := by rfl

def raw20168 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw20168Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw20168step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -3, 3], ![-1, 1, 0], ![-2, 2, 0]]
def raw20168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw20168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20168 raw20168Labels = mixedMoment B node1718 node1718Labels := by
  calc
    mixedMoment B raw20168 raw20168Labels = mixedMoment B raw20168step0 raw20168step0Labels := by
      have hz : ∀ j, raw20168 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20168step0 = (fun i j => raw20168 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20168step0 raw20168; decide +kernel
      have hl : raw20168step0Labels = raw20168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20168 raw20168Labels permutation265 hz
    mixedMoment B raw20168step0 raw20168step0Labels = mixedMoment B raw20168step1 raw20168step1Labels := by
      have ha : raw20168step1 = (fun i j => raw20168step0 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20168step1 raw20168step0; decide +kernel
      have hl : raw20168step1Labels = raw20168step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20168step0 raw20168step0Labels permutation48 permutation4
    mixedMoment B raw20168step1 raw20168step1Labels = mixedMoment B raw20168step2 raw20168step2Labels := by
      have ha : raw20168step2 = -raw20168step1 := by apply Matrix.ext; change ∀ i j, raw20168step2 i j = -(raw20168step1 i j); unfold raw20168step2 raw20168step1; decide +kernel
      have hl : raw20168step2Labels = raw20168step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1718 node1718Labels := by rfl

def raw20169 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw20169Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw20169step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20169step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![3, -3, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw20169step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20169step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -3, 3], ![-3, 3, 0]]
def raw20169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20169step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 3, -3], ![3, -3, 0]]
def raw20169step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20169 raw20169Labels = mixedMoment B node1719 node1719Labels := by
  calc
    mixedMoment B raw20169 raw20169Labels = mixedMoment B raw20169step0 raw20169step0Labels := by
      have hz : ∀ j, raw20169 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20169step0 = (fun i j => raw20169 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20169step0 raw20169; decide +kernel
      have hl : raw20169step0Labels = raw20169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20169 raw20169Labels permutation346 hz
    mixedMoment B raw20169step0 raw20169step0Labels = mixedMoment B raw20169step1 raw20169step1Labels := by
      have hz : ∀ j, raw20169step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20169step1 = (fun i j => raw20169step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20169step1 raw20169step0; decide +kernel
      have hl : raw20169step1Labels = raw20169step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20169step0 raw20169step0Labels permutation56 hz
    mixedMoment B raw20169step1 raw20169step1Labels = mixedMoment B raw20169step2 raw20169step2Labels := by
      have ha : raw20169step2 = (fun i j => raw20169step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20169step2 raw20169step1; decide +kernel
      have hl : raw20169step2Labels = raw20169step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20169step1 raw20169step1Labels permutation11 permutation4
    mixedMoment B raw20169step2 raw20169step2Labels = mixedMoment B raw20169step3 raw20169step3Labels := by
      have ha : raw20169step3 = -raw20169step2 := by apply Matrix.ext; change ∀ i j, raw20169step3 i j = -(raw20169step2 i j); unfold raw20169step3 raw20169step2; decide +kernel
      have hl : raw20169step3Labels = raw20169step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1719 node1719Labels := by rfl

def raw20170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20170Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20170step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20170step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw20170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20170step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20170step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20170 raw20170Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw20170 raw20170Labels = mixedMoment B raw20170step0 raw20170step0Labels := by
      have hz : ∀ j, raw20170 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20170step0 = (fun i j => raw20170 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20170step0 raw20170; decide +kernel
      have hl : raw20170step0Labels = raw20170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20170 raw20170Labels permutation346 hz
    mixedMoment B raw20170step0 raw20170step0Labels = mixedMoment B raw20170step1 raw20170step1Labels := by
      have hz : ∀ j, raw20170step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20170step1 = (fun i j => raw20170step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20170step1 raw20170step0; decide +kernel
      have hl : raw20170step1Labels = raw20170step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20170step0 raw20170step0Labels permutation56 hz
    mixedMoment B raw20170step1 raw20170step1Labels = mixedMoment B raw20170step2 raw20170step2Labels := by
      have ha : raw20170step2 = (fun i j => raw20170step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20170step2 raw20170step1; decide +kernel
      have hl : raw20170step2Labels = raw20170step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20170step1 raw20170step1Labels permutation31 permutation2
    mixedMoment B raw20170step2 raw20170step2Labels = mixedMoment B raw20170step3 raw20170step3Labels := by
      have ha : raw20170step3 = -raw20170step2 := by apply Matrix.ext; change ∀ i j, raw20170step3 i j = -(raw20170step2 i j); unfold raw20170step3 raw20170step2; decide +kernel
      have hl : raw20170step3Labels = raw20170step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2062 node2062Labels := by rfl

def raw20171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20171Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20171step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20171 raw20171Labels = mixedMoment B node1315 node1315Labels := by
  calc
    mixedMoment B raw20171 raw20171Labels = mixedMoment B raw20171step0 raw20171step0Labels := by
      have hz : ∀ j, raw20171 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20171step0 = (fun i j => raw20171 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20171step0 raw20171; decide +kernel
      have hl : raw20171step0Labels = raw20171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20171 raw20171Labels permutation346 hz
    mixedMoment B raw20171step0 raw20171step0Labels = mixedMoment B raw20171step1 raw20171step1Labels := by
      have ha : raw20171step1 = (fun i j => raw20171step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20171step1 raw20171step0; decide +kernel
      have hl : raw20171step1Labels = raw20171step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20171step0 raw20171step0Labels permutation38 permutation2
    _ = mixedMoment B node1315 node1315Labels := by rfl

def raw20172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20172Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20172step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20172 raw20172Labels = mixedMoment B node1315 node1315Labels := by
  calc
    mixedMoment B raw20172 raw20172Labels = mixedMoment B raw20172step0 raw20172step0Labels := by
      have hz : ∀ j, raw20172 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20172step0 = (fun i j => raw20172 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20172step0 raw20172; decide +kernel
      have hl : raw20172step0Labels = raw20172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20172 raw20172Labels permutation265 hz
    mixedMoment B raw20172step0 raw20172step0Labels = mixedMoment B raw20172step1 raw20172step1Labels := by
      have ha : raw20172step1 = (fun i j => raw20172step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20172step1 raw20172step0; decide +kernel
      have hl : raw20172step1Labels = raw20172step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20172step0 raw20172step0Labels permutation38 permutation2
    _ = mixedMoment B node1315 node1315Labels := by rfl

def raw20173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20173Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20173step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20173step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20173 raw20173Labels = mixedMoment B node1369 node1369Labels := by
  calc
    mixedMoment B raw20173 raw20173Labels = mixedMoment B raw20173step0 raw20173step0Labels := by
      have hz : ∀ j, raw20173 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20173step0 = (fun i j => raw20173 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20173step0 raw20173; decide +kernel
      have hl : raw20173step0Labels = raw20173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20173 raw20173Labels permutation346 hz
    mixedMoment B raw20173step0 raw20173step0Labels = mixedMoment B raw20173step1 raw20173step1Labels := by
      have hz : ∀ j, raw20173step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20173step1 = (fun i j => raw20173step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20173step1 raw20173step0; decide +kernel
      have hl : raw20173step1Labels = raw20173step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20173step0 raw20173step0Labels permutation56 hz
    _ = mixedMoment B node1369 node1369Labels := by rfl

def raw20174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, -2, 0], ![3, 0, -3]]
def raw20174Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -2, 0], ![3, 0, -3]]
def raw20174step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20174step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -2, 0], ![3, 0, -3]]
def raw20174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20174 raw20174Labels = mixedMoment B node1323 node1323Labels := by
  calc
    mixedMoment B raw20174 raw20174Labels = mixedMoment B raw20174step0 raw20174step0Labels := by
      have hz : ∀ j, raw20174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20174step0 = (fun i j => raw20174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20174step0 raw20174; decide +kernel
      have hl : raw20174step0Labels = raw20174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20174 raw20174Labels permutation346 hz
    mixedMoment B raw20174step0 raw20174step0Labels = mixedMoment B raw20174step1 raw20174step1Labels := by
      have hz : ∀ j, raw20174step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20174step1 = (fun i j => raw20174step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20174step1 raw20174step0; decide +kernel
      have hl : raw20174step1Labels = raw20174step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20174step0 raw20174step0Labels permutation56 hz
    _ = mixedMoment B node1323 node1323Labels := by rfl

def raw20175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![4, -1, -3]]
def raw20175Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![4, -1, -3]]
def raw20175step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20175step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![4, -1, -3]]
def raw20175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20175step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, -1, 2], ![-4, 3, 1]]
def raw20175step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20175step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![4, -3, -1]]
def raw20175step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20175 raw20175Labels = mixedMoment B node936 node936Labels := by
  calc
    mixedMoment B raw20175 raw20175Labels = mixedMoment B raw20175step0 raw20175step0Labels := by
      have hz : ∀ j, raw20175 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20175step0 = (fun i j => raw20175 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20175step0 raw20175; decide +kernel
      have hl : raw20175step0Labels = raw20175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20175 raw20175Labels permutation346 hz
    mixedMoment B raw20175step0 raw20175step0Labels = mixedMoment B raw20175step1 raw20175step1Labels := by
      have hz : ∀ j, raw20175step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20175step1 = (fun i j => raw20175step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20175step1 raw20175step0; decide +kernel
      have hl : raw20175step1Labels = raw20175step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20175step0 raw20175step0Labels permutation56 hz
    mixedMoment B raw20175step1 raw20175step1Labels = mixedMoment B raw20175step2 raw20175step2Labels := by
      have ha : raw20175step2 = (fun i j => raw20175step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20175step2 raw20175step1; decide +kernel
      have hl : raw20175step2Labels = raw20175step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20175step1 raw20175step1Labels permutation31 permutation2
    mixedMoment B raw20175step2 raw20175step2Labels = mixedMoment B raw20175step3 raw20175step3Labels := by
      have ha : raw20175step3 = -raw20175step2 := by apply Matrix.ext; change ∀ i j, raw20175step3 i j = -(raw20175step2 i j); unfold raw20175step3 raw20175step2; decide +kernel
      have hl : raw20175step3Labels = raw20175step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node936 node936Labels := by rfl

def raw20176 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![-2, 2], ![0, 0], ![3, -3]]
def raw20176Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20176step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![-2, 2], ![3, -3]]
def raw20176step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20176step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![3, -3]]
def raw20176step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20176step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![3, -3]]
def raw20176step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20176step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw20176step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20176step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw20176step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20176 raw20176Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw20176 raw20176Labels = mixedMoment B raw20176step0 raw20176step0Labels := by
      have hz : ∀ j, raw20176 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20176step0 = (fun i j => raw20176 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20176step0 raw20176; decide +kernel
      have hl : raw20176step0Labels = raw20176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20176 raw20176Labels permutation520 hz
    mixedMoment B raw20176step0 raw20176step0Labels = mixedMoment B raw20176step1 raw20176step1Labels := by
      have hz : ∀ j, raw20176step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20176step1 = (fun i j => raw20176step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20176step1 raw20176step0; decide +kernel
      have hl : raw20176step1Labels = raw20176step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20176step0 raw20176step0Labels permutation80 hz
    mixedMoment B raw20176step1 raw20176step1Labels = mixedMoment B raw20176step2 raw20176step2Labels := by
      have hz : ∀ j, raw20176step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20176step2 = (fun i j => raw20176step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20176step2 raw20176step1; decide +kernel
      have hl : raw20176step2Labels = raw20176step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20176step1 raw20176step1Labels permutation14 hz
    mixedMoment B raw20176step2 raw20176step2Labels = mixedMoment B raw20176step3 raw20176step3Labels := by
      have ha : raw20176step3 = (fun i j => raw20176step2 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20176step3 raw20176step2; decide +kernel
      have hl : raw20176step3Labels = raw20176step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20176step2 raw20176step2Labels permutation6 permutation0
    mixedMoment B raw20176step3 raw20176step3Labels = mixedMoment B raw20176step4 raw20176step4Labels := by
      have ha : raw20176step4 = -raw20176step3 := by apply Matrix.ext; change ∀ i j, raw20176step4 i j = -(raw20176step3 i j); unfold raw20176step4 raw20176step3; decide +kernel
      have hl : raw20176step4Labels = raw20176step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw20177 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20177Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20177step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw20177step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20177 raw20177Labels = mixedMoment B node2005 node2005Labels := by
  calc
    mixedMoment B raw20177 raw20177Labels = mixedMoment B raw20177step0 raw20177step0Labels := by
      have hz : ∀ j, raw20177 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20177step0 = (fun i j => raw20177 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20177step0 raw20177; decide +kernel
      have hl : raw20177step0Labels = raw20177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20177 raw20177Labels permutation346 hz
    mixedMoment B raw20177step0 raw20177step0Labels = mixedMoment B raw20177step1 raw20177step1Labels := by
      have ha : raw20177step1 = (fun i j => raw20177step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20177step1 raw20177step0; decide +kernel
      have hl : raw20177step1Labels = raw20177step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20177step0 raw20177step0Labels permutation139 permutation2
    _ = mixedMoment B node2005 node2005Labels := by rfl

def raw20178 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20178Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20178step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw20178step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20178 raw20178Labels = mixedMoment B node2005 node2005Labels := by
  calc
    mixedMoment B raw20178 raw20178Labels = mixedMoment B raw20178step0 raw20178step0Labels := by
      have hz : ∀ j, raw20178 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20178step0 = (fun i j => raw20178 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20178step0 raw20178; decide +kernel
      have hl : raw20178step0Labels = raw20178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20178 raw20178Labels permutation265 hz
    mixedMoment B raw20178step0 raw20178step0Labels = mixedMoment B raw20178step1 raw20178step1Labels := by
      have ha : raw20178step1 = (fun i j => raw20178step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20178step1 raw20178step0; decide +kernel
      have hl : raw20178step1Labels = raw20178step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20178step0 raw20178step0Labels permutation139 permutation2
    _ = mixedMoment B node2005 node2005Labels := by rfl

def raw20179 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw20179Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw20179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20179step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw20179step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20179step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw20179step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20179 raw20179Labels = mixedMoment B node1011 node1011Labels := by
  calc
    mixedMoment B raw20179 raw20179Labels = mixedMoment B raw20179step0 raw20179step0Labels := by
      have hz : ∀ j, raw20179 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20179step0 = (fun i j => raw20179 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20179step0 raw20179; decide +kernel
      have hl : raw20179step0Labels = raw20179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20179 raw20179Labels permutation346 hz
    mixedMoment B raw20179step0 raw20179step0Labels = mixedMoment B raw20179step1 raw20179step1Labels := by
      have hz : ∀ j, raw20179step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20179step1 = (fun i j => raw20179step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20179step1 raw20179step0; decide +kernel
      have hl : raw20179step1Labels = raw20179step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20179step0 raw20179step0Labels permutation56 hz
    mixedMoment B raw20179step1 raw20179step1Labels = mixedMoment B raw20179step2 raw20179step2Labels := by
      have ha : raw20179step2 = (fun i j => raw20179step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20179step2 raw20179step1; decide +kernel
      have hl : raw20179step2Labels = raw20179step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20179step1 raw20179step1Labels permutation31 permutation2
    _ = mixedMoment B node1011 node1011Labels := by rfl

def raw20180 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20180Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20180step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw20180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw20180step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20180 raw20180Labels = mixedMoment B node835 node835Labels := by
  calc
    mixedMoment B raw20180 raw20180Labels = mixedMoment B raw20180step0 raw20180step0Labels := by
      have hz : ∀ j, raw20180 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20180step0 = (fun i j => raw20180 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20180step0 raw20180; decide +kernel
      have hl : raw20180step0Labels = raw20180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20180 raw20180Labels permutation346 hz
    mixedMoment B raw20180step0 raw20180step0Labels = mixedMoment B raw20180step1 raw20180step1Labels := by
      have ha : raw20180step1 = (fun i j => raw20180step0 (permutation51 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20180step1 raw20180step0; decide +kernel
      have hl : raw20180step1Labels = raw20180step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20180step0 raw20180step0Labels permutation51 permutation4
    mixedMoment B raw20180step1 raw20180step1Labels = mixedMoment B raw20180step2 raw20180step2Labels := by
      have ha : raw20180step2 = -raw20180step1 := by apply Matrix.ext; change ∀ i j, raw20180step2 i j = -(raw20180step1 i j); unfold raw20180step2 raw20180step1; decide +kernel
      have hl : raw20180step2Labels = raw20180step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node835 node835Labels := by rfl

def raw20181 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20181Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20181step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw20181step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20181step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw20181step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20181 raw20181Labels = mixedMoment B node835 node835Labels := by
  calc
    mixedMoment B raw20181 raw20181Labels = mixedMoment B raw20181step0 raw20181step0Labels := by
      have hz : ∀ j, raw20181 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20181step0 = (fun i j => raw20181 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20181step0 raw20181; decide +kernel
      have hl : raw20181step0Labels = raw20181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20181 raw20181Labels permutation265 hz
    mixedMoment B raw20181step0 raw20181step0Labels = mixedMoment B raw20181step1 raw20181step1Labels := by
      have ha : raw20181step1 = (fun i j => raw20181step0 (permutation51 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20181step1 raw20181step0; decide +kernel
      have hl : raw20181step1Labels = raw20181step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20181step0 raw20181step0Labels permutation51 permutation4
    mixedMoment B raw20181step1 raw20181step1Labels = mixedMoment B raw20181step2 raw20181step2Labels := by
      have ha : raw20181step2 = -raw20181step1 := by apply Matrix.ext; change ∀ i j, raw20181step2 i j = -(raw20181step1 i j); unfold raw20181step2 raw20181step1; decide +kernel
      have hl : raw20181step2Labels = raw20181step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node835 node835Labels := by rfl

def raw20182 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20182Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![3, -3, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20182step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20182step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![3, -3, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20182step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20182step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -3, 3], ![-1, 0, 1], ![-3, 3, 0]]
def raw20182step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20182step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, 0, -1], ![3, -3, 0]]
def raw20182step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20182 raw20182Labels = mixedMoment B node837 node837Labels := by
  calc
    mixedMoment B raw20182 raw20182Labels = mixedMoment B raw20182step0 raw20182step0Labels := by
      have hz : ∀ j, raw20182 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20182step0 = (fun i j => raw20182 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20182step0 raw20182; decide +kernel
      have hl : raw20182step0Labels = raw20182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20182 raw20182Labels permutation346 hz
    mixedMoment B raw20182step0 raw20182step0Labels = mixedMoment B raw20182step1 raw20182step1Labels := by
      have hz : ∀ j, raw20182step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20182step1 = (fun i j => raw20182step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20182step1 raw20182step0; decide +kernel
      have hl : raw20182step1Labels = raw20182step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20182step0 raw20182step0Labels permutation56 hz
    mixedMoment B raw20182step1 raw20182step1Labels = mixedMoment B raw20182step2 raw20182step2Labels := by
      have ha : raw20182step2 = (fun i j => raw20182step1 (permutation13 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20182step2 raw20182step1; decide +kernel
      have hl : raw20182step2Labels = raw20182step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20182step1 raw20182step1Labels permutation13 permutation4
    mixedMoment B raw20182step2 raw20182step2Labels = mixedMoment B raw20182step3 raw20182step3Labels := by
      have ha : raw20182step3 = -raw20182step2 := by apply Matrix.ext; change ∀ i j, raw20182step3 i j = -(raw20182step2 i j); unfold raw20182step3 raw20182step2; decide +kernel
      have hl : raw20182step3Labels = raw20182step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node837 node837Labels := by rfl

def raw20183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![1, 0, -1], ![3, 0, -3]]
def raw20183Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -3, 3], ![1, 0, -1], ![3, 0, -3]]
def raw20183step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20183step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -3, 3], ![1, 0, -1], ![3, 0, -3]]
def raw20183step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20183 raw20183Labels = mixedMoment B node1352 node1352Labels := by
  calc
    mixedMoment B raw20183 raw20183Labels = mixedMoment B raw20183step0 raw20183step0Labels := by
      have hz : ∀ j, raw20183 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20183step0 = (fun i j => raw20183 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20183step0 raw20183; decide +kernel
      have hl : raw20183step0Labels = raw20183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20183 raw20183Labels permutation346 hz
    mixedMoment B raw20183step0 raw20183step0Labels = mixedMoment B raw20183step1 raw20183step1Labels := by
      have hz : ∀ j, raw20183step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20183step1 = (fun i j => raw20183step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20183step1 raw20183step0; decide +kernel
      have hl : raw20183step1Labels = raw20183step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20183step0 raw20183step0Labels permutation56 hz
    _ = mixedMoment B node1352 node1352Labels := by rfl

def raw20184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -3, 3], ![1, 0, -1], ![3, 0, -3]]
def raw20184Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -3, 3], ![1, 0, -1], ![3, 0, -3]]
def raw20184step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -3, 3], ![-1, 1, 0], ![-3, 2, 1]]
def raw20184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20184step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![3, -2, -1]]
def raw20184step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20184 raw20184Labels = mixedMoment B node1932 node1932Labels := by
  calc
    mixedMoment B raw20184 raw20184Labels = mixedMoment B raw20184step0 raw20184step0Labels := by
      have hz : ∀ j, raw20184 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20184step0 = (fun i j => raw20184 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20184step0 raw20184; decide +kernel
      have hl : raw20184step0Labels = raw20184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20184 raw20184Labels permutation346 hz
    mixedMoment B raw20184step0 raw20184step0Labels = mixedMoment B raw20184step1 raw20184step1Labels := by
      have ha : raw20184step1 = (fun i j => raw20184step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20184step1 raw20184step0; decide +kernel
      have hl : raw20184step1Labels = raw20184step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20184step0 raw20184step0Labels permutation151 permutation2
    mixedMoment B raw20184step1 raw20184step1Labels = mixedMoment B raw20184step2 raw20184step2Labels := by
      have ha : raw20184step2 = -raw20184step1 := by apply Matrix.ext; change ∀ i j, raw20184step2 i j = -(raw20184step1 i j); unfold raw20184step2 raw20184step1; decide +kernel
      have hl : raw20184step2Labels = raw20184step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1932 node1932Labels := by rfl

def raw20185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3], ![1, 0, -1], ![3, 0, -3]]
def raw20185Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -3, 3], ![1, 0, -1], ![3, 0, -3]]
def raw20185step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -3, 3], ![-1, 1, 0], ![-3, 2, 1]]
def raw20185step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![3, -2, -1]]
def raw20185step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20185 raw20185Labels = mixedMoment B node1932 node1932Labels := by
  calc
    mixedMoment B raw20185 raw20185Labels = mixedMoment B raw20185step0 raw20185step0Labels := by
      have hz : ∀ j, raw20185 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20185step0 = (fun i j => raw20185 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20185step0 raw20185; decide +kernel
      have hl : raw20185step0Labels = raw20185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20185 raw20185Labels permutation265 hz
    mixedMoment B raw20185step0 raw20185step0Labels = mixedMoment B raw20185step1 raw20185step1Labels := by
      have ha : raw20185step1 = (fun i j => raw20185step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20185step1 raw20185step0; decide +kernel
      have hl : raw20185step1Labels = raw20185step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20185step0 raw20185step0Labels permutation151 permutation2
    mixedMoment B raw20185step1 raw20185step1Labels = mixedMoment B raw20185step2 raw20185step2Labels := by
      have ha : raw20185step2 = -raw20185step1 := by apply Matrix.ext; change ∀ i j, raw20185step2 i j = -(raw20185step1 i j); unfold raw20185step2 raw20185step1; decide +kernel
      have hl : raw20185step2Labels = raw20185step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1932 node1932Labels := by rfl

def raw20186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3], ![1, 0, -1], ![3, 0, -3]]
def raw20186Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -2, 3], ![1, 0, -1], ![3, 0, -3]]
def raw20186step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20186step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![3, 0, -3]]
def raw20186step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20186step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw20186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20186step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw20186step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20186 raw20186Labels = mixedMoment B node1951 node1951Labels := by
  calc
    mixedMoment B raw20186 raw20186Labels = mixedMoment B raw20186step0 raw20186step0Labels := by
      have hz : ∀ j, raw20186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20186step0 = (fun i j => raw20186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20186step0 raw20186; decide +kernel
      have hl : raw20186step0Labels = raw20186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20186 raw20186Labels permutation346 hz
    mixedMoment B raw20186step0 raw20186step0Labels = mixedMoment B raw20186step1 raw20186step1Labels := by
      have hz : ∀ j, raw20186step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20186step1 = (fun i j => raw20186step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20186step1 raw20186step0; decide +kernel
      have hl : raw20186step1Labels = raw20186step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20186step0 raw20186step0Labels permutation56 hz
    mixedMoment B raw20186step1 raw20186step1Labels = mixedMoment B raw20186step2 raw20186step2Labels := by
      have ha : raw20186step2 = (fun i j => raw20186step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20186step2 raw20186step1; decide +kernel
      have hl : raw20186step2Labels = raw20186step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20186step1 raw20186step1Labels permutation31 permutation2
    mixedMoment B raw20186step2 raw20186step2Labels = mixedMoment B raw20186step3 raw20186step3Labels := by
      have ha : raw20186step3 = -raw20186step2 := by apply Matrix.ext; change ∀ i j, raw20186step3 i j = -(raw20186step2 i j); unfold raw20186step3 raw20186step2; decide +kernel
      have hl : raw20186step3Labels = raw20186step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1951 node1951Labels := by rfl

def raw20187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![0, 1, -1], ![3, 0, -3]]
def raw20187Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -3, 3], ![0, 1, -1], ![3, 0, -3]]
def raw20187step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20187step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -3, 3], ![0, 1, -1], ![3, 0, -3]]
def raw20187step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20187step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-3, 2, 1]]
def raw20187step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20187step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw20187step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20187 raw20187Labels = mixedMoment B node2222 node2222Labels := by
  calc
    mixedMoment B raw20187 raw20187Labels = mixedMoment B raw20187step0 raw20187step0Labels := by
      have hz : ∀ j, raw20187 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20187step0 = (fun i j => raw20187 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20187step0 raw20187; decide +kernel
      have hl : raw20187step0Labels = raw20187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20187 raw20187Labels permutation346 hz
    mixedMoment B raw20187step0 raw20187step0Labels = mixedMoment B raw20187step1 raw20187step1Labels := by
      have hz : ∀ j, raw20187step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20187step1 = (fun i j => raw20187step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20187step1 raw20187step0; decide +kernel
      have hl : raw20187step1Labels = raw20187step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20187step0 raw20187step0Labels permutation56 hz
    mixedMoment B raw20187step1 raw20187step1Labels = mixedMoment B raw20187step2 raw20187step2Labels := by
      have ha : raw20187step2 = (fun i j => raw20187step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20187step2 raw20187step1; decide +kernel
      have hl : raw20187step2Labels = raw20187step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20187step1 raw20187step1Labels permutation31 permutation2
    mixedMoment B raw20187step2 raw20187step2Labels = mixedMoment B raw20187step3 raw20187step3Labels := by
      have ha : raw20187step3 = -raw20187step2 := by apply Matrix.ext; change ∀ i j, raw20187step3 i j = -(raw20187step2 i j); unfold raw20187step3 raw20187step2; decide +kernel
      have hl : raw20187step3Labels = raw20187step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2222 node2222Labels := by rfl

def raw20188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![1, 0, -1], ![2, 1, -3]]
def raw20188Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -3, 3], ![1, 0, -1], ![2, 1, -3]]
def raw20188step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20188step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -3, 3], ![1, 0, -1], ![2, 1, -3]]
def raw20188step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20188step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw20188step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20188 raw20188Labels = mixedMoment B node2267 node2267Labels := by
  calc
    mixedMoment B raw20188 raw20188Labels = mixedMoment B raw20188step0 raw20188step0Labels := by
      have hz : ∀ j, raw20188 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20188step0 = (fun i j => raw20188 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20188step0 raw20188; decide +kernel
      have hl : raw20188step0Labels = raw20188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20188 raw20188Labels permutation346 hz
    mixedMoment B raw20188step0 raw20188step0Labels = mixedMoment B raw20188step1 raw20188step1Labels := by
      have hz : ∀ j, raw20188step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20188step1 = (fun i j => raw20188step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20188step1 raw20188step0; decide +kernel
      have hl : raw20188step1Labels = raw20188step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20188step0 raw20188step0Labels permutation56 hz
    mixedMoment B raw20188step1 raw20188step1Labels = mixedMoment B raw20188step2 raw20188step2Labels := by
      have ha : raw20188step2 = (fun i j => raw20188step1 (permutation17 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20188step2 raw20188step1; decide +kernel
      have hl : raw20188step2Labels = raw20188step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20188step1 raw20188step1Labels permutation17 permutation4
    _ = mixedMoment B node2267 node2267Labels := by rfl

def raw20189 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![-3, 3], ![1, -1], ![3, -3]]
def raw20189Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20189step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-3, 3], ![1, -1], ![3, -3]]
def raw20189step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20189step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![1, -1], ![3, -3]]
def raw20189step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20189step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw20189step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20189 raw20189Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw20189 raw20189Labels = mixedMoment B raw20189step0 raw20189step0Labels := by
      have hz : ∀ j, raw20189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20189step0 = (fun i j => raw20189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20189step0 raw20189; decide +kernel
      have hl : raw20189step0Labels = raw20189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20189 raw20189Labels permutation346 hz
    mixedMoment B raw20189step0 raw20189step0Labels = mixedMoment B raw20189step1 raw20189step1Labels := by
      have hz : ∀ j, raw20189step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20189step1 = (fun i j => raw20189step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20189step1 raw20189step0; decide +kernel
      have hl : raw20189step1Labels = raw20189step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20189step0 raw20189step0Labels permutation56 hz
    mixedMoment B raw20189step1 raw20189step1Labels = mixedMoment B raw20189step2 raw20189step2Labels := by
      have ha : raw20189step2 = (fun i j => raw20189step1 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20189step2 raw20189step1; decide +kernel
      have hl : raw20189step2Labels = raw20189step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20189step1 raw20189step1Labels permutation14 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw20190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20190Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20190step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20190step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20190 raw20190Labels = mixedMoment B node581 node581Labels := by
  calc
    mixedMoment B raw20190 raw20190Labels = mixedMoment B raw20190step0 raw20190step0Labels := by
      have hz : ∀ j, raw20190 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20190step0 = (fun i j => raw20190 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20190step0 raw20190; decide +kernel
      have hl : raw20190step0Labels = raw20190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20190 raw20190Labels permutation265 hz
    mixedMoment B raw20190step0 raw20190step0Labels = mixedMoment B raw20190step1 raw20190step1Labels := by
      have ha : raw20190step1 = (fun i j => raw20190step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20190step1 raw20190step0; decide +kernel
      have hl : raw20190step1Labels = raw20190step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20190step0 raw20190step0Labels permutation40 permutation2
    _ = mixedMoment B node581 node581Labels := by rfl

def raw20191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20191Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20191step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20191step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20191 raw20191Labels = mixedMoment B node905 node905Labels := by
  calc
    mixedMoment B raw20191 raw20191Labels = mixedMoment B raw20191step0 raw20191step0Labels := by
      have ha : raw20191step0 = (fun i j => raw20191 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20191step0 raw20191; decide +kernel
      have hl : raw20191step0Labels = raw20191Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20191 raw20191Labels permutation160 permutation2
    _ = mixedMoment B node905 node905Labels := by rfl

def raw20192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20192Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20192step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20192 raw20192Labels = mixedMoment B node1022 node1022Labels := by
  calc
    mixedMoment B raw20192 raw20192Labels = mixedMoment B raw20192step0 raw20192step0Labels := by
      have hz : ∀ j, raw20192 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20192step0 = (fun i j => raw20192 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20192step0 raw20192; decide +kernel
      have hl : raw20192step0Labels = raw20192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20192 raw20192Labels permutation265 hz
    _ = mixedMoment B node1022 node1022Labels := by rfl

def raw20193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20193Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20193step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20193step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20193 raw20193Labels = mixedMoment B node945 node945Labels := by
  calc
    mixedMoment B raw20193 raw20193Labels = mixedMoment B raw20193step0 raw20193step0Labels := by
      have hz : ∀ j, raw20193 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20193step0 = (fun i j => raw20193 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20193step0 raw20193; decide +kernel
      have hl : raw20193step0Labels = raw20193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20193 raw20193Labels permutation265 hz
    mixedMoment B raw20193step0 raw20193step0Labels = mixedMoment B raw20193step1 raw20193step1Labels := by
      have ha : raw20193step1 = (fun i j => raw20193step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20193step1 raw20193step0; decide +kernel
      have hl : raw20193step1Labels = raw20193step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20193step0 raw20193step0Labels permutation40 permutation2
    _ = mixedMoment B node945 node945Labels := by rfl

def raw20194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw20194Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw20194step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20194step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw20194step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20194step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20194 raw20194Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw20194 raw20194Labels = mixedMoment B raw20194step0 raw20194step0Labels := by
      have hz : ∀ j, raw20194 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20194step0 = (fun i j => raw20194 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20194step0 raw20194; decide +kernel
      have hl : raw20194step0Labels = raw20194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20194 raw20194Labels permutation520 hz
    mixedMoment B raw20194step0 raw20194step0Labels = mixedMoment B raw20194step1 raw20194step1Labels := by
      have hz : ∀ j, raw20194step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20194step1 = (fun i j => raw20194step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20194step1 raw20194step0; decide +kernel
      have hl : raw20194step1Labels = raw20194step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20194step0 raw20194step0Labels permutation56 hz
    mixedMoment B raw20194step1 raw20194step1Labels = mixedMoment B raw20194step2 raw20194step2Labels := by
      have ha : raw20194step2 = (fun i j => raw20194step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20194step2 raw20194step1; decide +kernel
      have hl : raw20194step2Labels = raw20194step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20194step1 raw20194step1Labels permutation10 permutation2
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw20195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw20195Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw20195step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20195step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20195 raw20195Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw20195 raw20195Labels = mixedMoment B raw20195step0 raw20195step0Labels := by
      have hz : ∀ j, raw20195 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20195step0 = (fun i j => raw20195 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20195step0 raw20195; decide +kernel
      have hl : raw20195step0Labels = raw20195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20195 raw20195Labels permutation265 hz
    mixedMoment B raw20195step0 raw20195step0Labels = mixedMoment B raw20195step1 raw20195step1Labels := by
      have ha : raw20195step1 = (fun i j => raw20195step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20195step1 raw20195step0; decide +kernel
      have hl : raw20195step1Labels = raw20195step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20195step0 raw20195step0Labels permutation40 permutation2
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw20196 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![0, 0], ![1, -1]]
def raw20196Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20196step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]
def raw20196step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20196step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw20196step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20196 raw20196Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw20196 raw20196Labels = mixedMoment B raw20196step0 raw20196step0Labels := by
      have hz : ∀ j, raw20196 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20196step0 = (fun i j => raw20196 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20196step0 raw20196; decide +kernel
      have hl : raw20196step0Labels = raw20196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20196 raw20196Labels permutation520 hz
    mixedMoment B raw20196step0 raw20196step0Labels = mixedMoment B raw20196step1 raw20196step1Labels := by
      have hz : ∀ j, raw20196step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20196step1 = (fun i j => raw20196step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20196step1 raw20196step0; decide +kernel
      have hl : raw20196step1Labels = raw20196step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20196step0 raw20196step0Labels permutation56 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw20197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20197Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20197step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw20197step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20197step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20197 raw20197Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw20197 raw20197Labels = mixedMoment B raw20197step0 raw20197step0Labels := by
      have hz : ∀ j, raw20197 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20197step0 = (fun i j => raw20197 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20197step0 raw20197; decide +kernel
      have hl : raw20197step0Labels = raw20197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20197 raw20197Labels permutation265 hz
    mixedMoment B raw20197step0 raw20197step0Labels = mixedMoment B raw20197step1 raw20197step1Labels := by
      have ha : raw20197step1 = (fun i j => raw20197step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20197step1 raw20197step0; decide +kernel
      have hl : raw20197step1Labels = raw20197step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20197step0 raw20197step0Labels permutation151 permutation2
    mixedMoment B raw20197step1 raw20197step1Labels = mixedMoment B raw20197step2 raw20197step2Labels := by
      have ha : raw20197step2 = -raw20197step1 := by apply Matrix.ext; change ∀ i j, raw20197step2 i j = -(raw20197step1 i j); unfold raw20197step2 raw20197step1; decide +kernel
      have hl : raw20197step2Labels = raw20197step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw20198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20198Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20198step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20198 raw20198Labels = mixedMoment B node1327 node1327Labels := by
  calc
    mixedMoment B raw20198 raw20198Labels = mixedMoment B raw20198step0 raw20198step0Labels := by
      have ha : raw20198step0 = (fun i j => raw20198 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20198step0 raw20198; decide +kernel
      have hl : raw20198step0Labels = raw20198Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20198 raw20198Labels permutation182 permutation2
    _ = mixedMoment B node1327 node1327Labels := by rfl

def raw20199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20199Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20199step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20199 raw20199Labels = mixedMoment B node1337 node1337Labels := by
  calc
    mixedMoment B raw20199 raw20199Labels = mixedMoment B raw20199step0 raw20199step0Labels := by
      have hz : ∀ j, raw20199 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20199step0 = (fun i j => raw20199 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20199step0 raw20199; decide +kernel
      have hl : raw20199step0Labels = raw20199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20199 raw20199Labels permutation265 hz
    _ = mixedMoment B node1337 node1337Labels := by rfl

def raw20200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20200step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20200 raw20200Labels = mixedMoment B node1333 node1333Labels := by
  calc
    mixedMoment B raw20200 raw20200Labels = mixedMoment B raw20200step0 raw20200step0Labels := by
      have hz : ∀ j, raw20200 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20200step0 = (fun i j => raw20200 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20200step0 raw20200; decide +kernel
      have hl : raw20200step0Labels = raw20200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20200 raw20200Labels permutation265 hz
    _ = mixedMoment B node1333 node1333Labels := by rfl

def raw20201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 3, 1]]
def raw20201step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw20201step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20201 raw20201Labels = mixedMoment B node1118 node1118Labels := by
  calc
    mixedMoment B raw20201 raw20201Labels = mixedMoment B raw20201step0 raw20201step0Labels := by
      have hz : ∀ j, raw20201 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20201step0 = (fun i j => raw20201 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20201step0 raw20201; decide +kernel
      have hl : raw20201step0Labels = raw20201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20201 raw20201Labels permutation265 hz
    mixedMoment B raw20201step0 raw20201step0Labels = mixedMoment B raw20201step1 raw20201step1Labels := by
      have ha : raw20201step1 = (fun i j => raw20201step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20201step1 raw20201step0; decide +kernel
      have hl : raw20201step1Labels = raw20201step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20201step0 raw20201step0Labels permutation151 permutation2
    mixedMoment B raw20201step1 raw20201step1Labels = mixedMoment B raw20201step2 raw20201step2Labels := by
      have ha : raw20201step2 = -raw20201step1 := by apply Matrix.ext; change ∀ i j, raw20201step2 i j = -(raw20201step1 i j); unfold raw20201step2 raw20201step1; decide +kernel
      have hl : raw20201step2Labels = raw20201step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1118 node1118Labels := by rfl

def raw20202 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20202Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20202step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20202step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20202step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20202 raw20202Labels = mixedMoment B node3279 node3279Labels := by
  calc
    mixedMoment B raw20202 raw20202Labels = mixedMoment B raw20202step0 raw20202step0Labels := by
      have ha : raw20202step0 = (fun i j => raw20202 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20202step0 raw20202; decide +kernel
      have hl : raw20202step0Labels = raw20202Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20202 raw20202Labels permutation182 permutation2
    mixedMoment B raw20202step0 raw20202step0Labels = mixedMoment B raw20202step1 raw20202step1Labels := by
      have ha : raw20202step1 = -raw20202step0 := by apply Matrix.ext; change ∀ i j, raw20202step1 i j = -(raw20202step0 i j); unfold raw20202step1 raw20202step0; decide +kernel
      have hl : raw20202step1Labels = raw20202step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3279 node3279Labels := by rfl

def raw20203 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20203step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20203step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20203step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20203step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20203step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20203 raw20203Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw20203 raw20203Labels = mixedMoment B raw20203step0 raw20203step0Labels := by
      have hz : ∀ j, raw20203 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20203step0 = (fun i j => raw20203 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20203step0 raw20203; decide +kernel
      have hl : raw20203step0Labels = raw20203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20203 raw20203Labels permutation434 hz
    mixedMoment B raw20203step0 raw20203step0Labels = mixedMoment B raw20203step1 raw20203step1Labels := by
      have hz : ∀ j, raw20203step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20203step1 = (fun i j => raw20203step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20203step1 raw20203step0; decide +kernel
      have hl : raw20203step1Labels = raw20203step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20203step0 raw20203step0Labels permutation56 hz
    mixedMoment B raw20203step1 raw20203step1Labels = mixedMoment B raw20203step2 raw20203step2Labels := by
      have ha : raw20203step2 = -raw20203step1 := by apply Matrix.ext; change ∀ i j, raw20203step2 i j = -(raw20203step1 i j); unfold raw20203step2 raw20203step1; decide +kernel
      have hl : raw20203step2Labels = raw20203step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3300 node3300Labels := by rfl

def raw20204 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw20204Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw20204step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw20204step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20204 raw20204Labels = mixedMoment B node3283 node3283Labels := by
  calc
    mixedMoment B raw20204 raw20204Labels = mixedMoment B raw20204step0 raw20204step0Labels := by
      have hz : ∀ j, raw20204 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20204step0 = (fun i j => raw20204 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20204step0 raw20204; decide +kernel
      have hl : raw20204step0Labels = raw20204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20204 raw20204Labels permutation265 hz
    mixedMoment B raw20204step0 raw20204step0Labels = mixedMoment B raw20204step1 raw20204step1Labels := by
      have ha : raw20204step1 = -raw20204step0 := by apply Matrix.ext; change ∀ i j, raw20204step1 i j = -(raw20204step0 i j); unfold raw20204step1 raw20204step0; decide +kernel
      have hl : raw20204step1Labels = raw20204step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3283 node3283Labels := by rfl

def raw20205 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw20205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw20205step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw20205step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20205 raw20205Labels = mixedMoment B node1942 node1942Labels := by
  calc
    mixedMoment B raw20205 raw20205Labels = mixedMoment B raw20205step0 raw20205step0Labels := by
      have hz : ∀ j, raw20205 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20205step0 = (fun i j => raw20205 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20205step0 raw20205; decide +kernel
      have hl : raw20205step0Labels = raw20205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20205 raw20205Labels permutation265 hz
    mixedMoment B raw20205step0 raw20205step0Labels = mixedMoment B raw20205step1 raw20205step1Labels := by
      have ha : raw20205step1 = (fun i j => raw20205step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20205step1 raw20205step0; decide +kernel
      have hl : raw20205step1Labels = raw20205step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20205step0 raw20205step0Labels permutation149 permutation2
    _ = mixedMoment B node1942 node1942Labels := by rfl

def raw20206 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw20206step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20206step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw20206step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20206 raw20206Labels = mixedMoment B node802 node802Labels := by
  calc
    mixedMoment B raw20206 raw20206Labels = mixedMoment B raw20206step0 raw20206step0Labels := by
      have ha : raw20206step0 = (fun i j => raw20206 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20206step0 raw20206; decide +kernel
      have hl : raw20206step0Labels = raw20206Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20206 raw20206Labels permutation224 permutation4
    mixedMoment B raw20206step0 raw20206step0Labels = mixedMoment B raw20206step1 raw20206step1Labels := by
      have ha : raw20206step1 = -raw20206step0 := by apply Matrix.ext; change ∀ i j, raw20206step1 i j = -(raw20206step0 i j); unfold raw20206step1 raw20206step0; decide +kernel
      have hl : raw20206step1Labels = raw20206step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node802 node802Labels := by rfl

def raw20207 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20207step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20207step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw20207step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20207step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw20207step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20207 raw20207Labels = mixedMoment B node808 node808Labels := by
  calc
    mixedMoment B raw20207 raw20207Labels = mixedMoment B raw20207step0 raw20207step0Labels := by
      have hz : ∀ j, raw20207 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20207step0 = (fun i j => raw20207 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20207step0 raw20207; decide +kernel
      have hl : raw20207step0Labels = raw20207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20207 raw20207Labels permutation265 hz
    mixedMoment B raw20207step0 raw20207step0Labels = mixedMoment B raw20207step1 raw20207step1Labels := by
      have ha : raw20207step1 = (fun i j => raw20207step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20207step1 raw20207step0; decide +kernel
      have hl : raw20207step1Labels = raw20207step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20207step0 raw20207step0Labels permutation47 permutation4
    mixedMoment B raw20207step1 raw20207step1Labels = mixedMoment B raw20207step2 raw20207step2Labels := by
      have ha : raw20207step2 = -raw20207step1 := by apply Matrix.ext; change ∀ i j, raw20207step2 i j = -(raw20207step1 i j); unfold raw20207step2 raw20207step1; decide +kernel
      have hl : raw20207step2Labels = raw20207step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node808 node808Labels := by rfl

def raw20208 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20208step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20208step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20208step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20208 raw20208Labels = mixedMoment B node847 node847Labels := by
  calc
    mixedMoment B raw20208 raw20208Labels = mixedMoment B raw20208step0 raw20208step0Labels := by
      have hz : ∀ j, raw20208 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20208step0 = (fun i j => raw20208 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20208step0 raw20208; decide +kernel
      have hl : raw20208step0Labels = raw20208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20208 raw20208Labels permutation265 hz
    mixedMoment B raw20208step0 raw20208step0Labels = mixedMoment B raw20208step1 raw20208step1Labels := by
      have ha : raw20208step1 = (fun i j => raw20208step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20208step1 raw20208step0; decide +kernel
      have hl : raw20208step1Labels = raw20208step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20208step0 raw20208step0Labels permutation32 permutation4
    mixedMoment B raw20208step1 raw20208step1Labels = mixedMoment B raw20208step2 raw20208step2Labels := by
      have ha : raw20208step2 = -raw20208step1 := by apply Matrix.ext; change ∀ i j, raw20208step2 i j = -(raw20208step1 i j); unfold raw20208step2 raw20208step1; decide +kernel
      have hl : raw20208step2Labels = raw20208step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node847 node847Labels := by rfl

def raw20209 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20209step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw20209step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20209step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw20209step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20209 raw20209Labels = mixedMoment B node804 node804Labels := by
  calc
    mixedMoment B raw20209 raw20209Labels = mixedMoment B raw20209step0 raw20209step0Labels := by
      have hz : ∀ j, raw20209 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20209step0 = (fun i j => raw20209 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20209step0 raw20209; decide +kernel
      have hl : raw20209step0Labels = raw20209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20209 raw20209Labels permutation265 hz
    mixedMoment B raw20209step0 raw20209step0Labels = mixedMoment B raw20209step1 raw20209step1Labels := by
      have ha : raw20209step1 = (fun i j => raw20209step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20209step1 raw20209step0; decide +kernel
      have hl : raw20209step1Labels = raw20209step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20209step0 raw20209step0Labels permutation44 permutation4
    mixedMoment B raw20209step1 raw20209step1Labels = mixedMoment B raw20209step2 raw20209step2Labels := by
      have ha : raw20209step2 = -raw20209step1 := by apply Matrix.ext; change ∀ i j, raw20209step2 i j = -(raw20209step1 i j); unfold raw20209step2 raw20209step1; decide +kernel
      have hl : raw20209step2Labels = raw20209step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node804 node804Labels := by rfl

def raw20210 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20210Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20210step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20210step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20210step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20210 raw20210Labels = mixedMoment B node1613 node1613Labels := by
  calc
    mixedMoment B raw20210 raw20210Labels = mixedMoment B raw20210step0 raw20210step0Labels := by
      have ha : raw20210step0 = (fun i j => raw20210 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20210step0 raw20210; decide +kernel
      have hl : raw20210step0Labels = raw20210Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20210 raw20210Labels permutation152 permutation4
    mixedMoment B raw20210step0 raw20210step0Labels = mixedMoment B raw20210step1 raw20210step1Labels := by
      have ha : raw20210step1 = -raw20210step0 := by apply Matrix.ext; change ∀ i j, raw20210step1 i j = -(raw20210step0 i j); unfold raw20210step1 raw20210step0; decide +kernel
      have hl : raw20210step1Labels = raw20210step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1613 node1613Labels := by rfl

def raw20211 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20211Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20211step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20211step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20211step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20211step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20211step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20211step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20211step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20211 raw20211Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw20211 raw20211Labels = mixedMoment B raw20211step0 raw20211step0Labels := by
      have hz : ∀ j, raw20211 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20211step0 = (fun i j => raw20211 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20211step0 raw20211; decide +kernel
      have hl : raw20211step0Labels = raw20211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20211 raw20211Labels permutation434 hz
    mixedMoment B raw20211step0 raw20211step0Labels = mixedMoment B raw20211step1 raw20211step1Labels := by
      have hz : ∀ j, raw20211step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20211step1 = (fun i j => raw20211step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20211step1 raw20211step0; decide +kernel
      have hl : raw20211step1Labels = raw20211step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20211step0 raw20211step0Labels permutation56 hz
    mixedMoment B raw20211step1 raw20211step1Labels = mixedMoment B raw20211step2 raw20211step2Labels := by
      have ha : raw20211step2 = (fun i j => raw20211step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20211step2 raw20211step1; decide +kernel
      have hl : raw20211step2Labels = raw20211step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20211step1 raw20211step1Labels permutation8 permutation4
    mixedMoment B raw20211step2 raw20211step2Labels = mixedMoment B raw20211step3 raw20211step3Labels := by
      have ha : raw20211step3 = -raw20211step2 := by apply Matrix.ext; change ∀ i j, raw20211step3 i j = -(raw20211step2 i j); unfold raw20211step3 raw20211step2; decide +kernel
      have hl : raw20211step3Labels = raw20211step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1750 node1750Labels := by rfl

def raw20212 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw20212step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw20212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20212 raw20212Labels = mixedMoment B node1596 node1596Labels := by
  calc
    mixedMoment B raw20212 raw20212Labels = mixedMoment B raw20212step0 raw20212step0Labels := by
      have ha : raw20212step0 = (fun i j => raw20212 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20212step0 raw20212; decide +kernel
      have hl : raw20212step0Labels = raw20212Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20212 raw20212Labels permutation164 permutation4
    mixedMoment B raw20212step0 raw20212step0Labels = mixedMoment B raw20212step1 raw20212step1Labels := by
      have ha : raw20212step1 = -raw20212step0 := by apply Matrix.ext; change ∀ i j, raw20212step1 i j = -(raw20212step0 i j); unfold raw20212step1 raw20212step0; decide +kernel
      have hl : raw20212step1Labels = raw20212step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1596 node1596Labels := by rfl

def raw20213 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20213step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20213step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw20213step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20213step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20213step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20213 raw20213Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw20213 raw20213Labels = mixedMoment B raw20213step0 raw20213step0Labels := by
      have hz : ∀ j, raw20213 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20213step0 = (fun i j => raw20213 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20213step0 raw20213; decide +kernel
      have hl : raw20213step0Labels = raw20213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20213 raw20213Labels permutation434 hz
    mixedMoment B raw20213step0 raw20213step0Labels = mixedMoment B raw20213step1 raw20213step1Labels := by
      have hz : ∀ j, raw20213step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20213step1 = (fun i j => raw20213step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20213step1 raw20213step0; decide +kernel
      have hl : raw20213step1Labels = raw20213step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20213step0 raw20213step0Labels permutation56 hz
    mixedMoment B raw20213step1 raw20213step1Labels = mixedMoment B raw20213step2 raw20213step2Labels := by
      have ha : raw20213step2 = (fun i j => raw20213step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20213step2 raw20213step1; decide +kernel
      have hl : raw20213step2Labels = raw20213step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20213step1 raw20213step1Labels permutation10 permutation4
    mixedMoment B raw20213step2 raw20213step2Labels = mixedMoment B raw20213step3 raw20213step3Labels := by
      have ha : raw20213step3 = -raw20213step2 := by apply Matrix.ext; change ∀ i j, raw20213step3 i j = -(raw20213step2 i j); unfold raw20213step3 raw20213step2; decide +kernel
      have hl : raw20213step3Labels = raw20213step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1725 node1725Labels := by rfl

def raw20214 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20214Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20214step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw20214step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20214step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw20214step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20214 raw20214Labels = mixedMoment B node1643 node1643Labels := by
  calc
    mixedMoment B raw20214 raw20214Labels = mixedMoment B raw20214step0 raw20214step0Labels := by
      have hz : ∀ j, raw20214 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20214step0 = (fun i j => raw20214 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20214step0 raw20214; decide +kernel
      have hl : raw20214step0Labels = raw20214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20214 raw20214Labels permutation265 hz
    mixedMoment B raw20214step0 raw20214step0Labels = mixedMoment B raw20214step1 raw20214step1Labels := by
      have ha : raw20214step1 = (fun i j => raw20214step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20214step1 raw20214step0; decide +kernel
      have hl : raw20214step1Labels = raw20214step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20214step0 raw20214step0Labels permutation44 permutation4
    mixedMoment B raw20214step1 raw20214step1Labels = mixedMoment B raw20214step2 raw20214step2Labels := by
      have ha : raw20214step2 = -raw20214step1 := by apply Matrix.ext; change ∀ i j, raw20214step2 i j = -(raw20214step1 i j); unfold raw20214step2 raw20214step1; decide +kernel
      have hl : raw20214step2Labels = raw20214step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1643 node1643Labels := by rfl

def raw20215 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw20215Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw20215step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20215step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw20215step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20215 raw20215Labels = mixedMoment B node1717 node1717Labels := by
  calc
    mixedMoment B raw20215 raw20215Labels = mixedMoment B raw20215step0 raw20215step0Labels := by
      have ha : raw20215step0 = (fun i j => raw20215 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20215step0 raw20215; decide +kernel
      have hl : raw20215step0Labels = raw20215Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20215 raw20215Labels permutation240 permutation4
    mixedMoment B raw20215step0 raw20215step0Labels = mixedMoment B raw20215step1 raw20215step1Labels := by
      have ha : raw20215step1 = -raw20215step0 := by apply Matrix.ext; change ∀ i j, raw20215step1 i j = -(raw20215step0 i j); unfold raw20215step1 raw20215step0; decide +kernel
      have hl : raw20215step1Labels = raw20215step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1717 node1717Labels := by rfl

def raw20216 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw20216Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw20216step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -3, 3], ![-1, 1, 0], ![-2, 2, 0]]
def raw20216step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20216step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw20216step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20216 raw20216Labels = mixedMoment B node1718 node1718Labels := by
  calc
    mixedMoment B raw20216 raw20216Labels = mixedMoment B raw20216step0 raw20216step0Labels := by
      have hz : ∀ j, raw20216 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20216step0 = (fun i j => raw20216 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20216step0 raw20216; decide +kernel
      have hl : raw20216step0Labels = raw20216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20216 raw20216Labels permutation265 hz
    mixedMoment B raw20216step0 raw20216step0Labels = mixedMoment B raw20216step1 raw20216step1Labels := by
      have ha : raw20216step1 = (fun i j => raw20216step0 (permutation49 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20216step1 raw20216step0; decide +kernel
      have hl : raw20216step1Labels = raw20216step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20216step0 raw20216step0Labels permutation49 permutation4
    mixedMoment B raw20216step1 raw20216step1Labels = mixedMoment B raw20216step2 raw20216step2Labels := by
      have ha : raw20216step2 = -raw20216step1 := by apply Matrix.ext; change ∀ i j, raw20216step2 i j = -(raw20216step1 i j); unfold raw20216step2 raw20216step1; decide +kernel
      have hl : raw20216step2Labels = raw20216step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1718 node1718Labels := by rfl

def raw20217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20217Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20217step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20217step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20217 raw20217Labels = mixedMoment B node585 node585Labels := by
  calc
    mixedMoment B raw20217 raw20217Labels = mixedMoment B raw20217step0 raw20217step0Labels := by
      have hz : ∀ j, raw20217 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20217step0 = (fun i j => raw20217 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20217step0 raw20217; decide +kernel
      have hl : raw20217step0Labels = raw20217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20217 raw20217Labels permutation265 hz
    mixedMoment B raw20217step0 raw20217step0Labels = mixedMoment B raw20217step1 raw20217step1Labels := by
      have ha : raw20217step1 = (fun i j => raw20217step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20217step1 raw20217step0; decide +kernel
      have hl : raw20217step1Labels = raw20217step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20217step0 raw20217step0Labels permutation38 permutation2
    _ = mixedMoment B node585 node585Labels := by rfl

def raw20218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20218 raw20218Labels = mixedMoment B node909 node909Labels := by
  calc
    mixedMoment B raw20218 raw20218Labels = mixedMoment B raw20218step0 raw20218step0Labels := by
      have ha : raw20218step0 = (fun i j => raw20218 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20218step0 raw20218; decide +kernel
      have hl : raw20218step0Labels = raw20218Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20218 raw20218Labels permutation158 permutation2
    _ = mixedMoment B node909 node909Labels := by rfl

def raw20219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20219Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20219step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20219step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20219 raw20219Labels = mixedMoment B node949 node949Labels := by
  calc
    mixedMoment B raw20219 raw20219Labels = mixedMoment B raw20219step0 raw20219step0Labels := by
      have hz : ∀ j, raw20219 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20219step0 = (fun i j => raw20219 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20219step0 raw20219; decide +kernel
      have hl : raw20219step0Labels = raw20219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20219 raw20219Labels permutation265 hz
    mixedMoment B raw20219step0 raw20219step0Labels = mixedMoment B raw20219step1 raw20219step1Labels := by
      have ha : raw20219step1 = (fun i j => raw20219step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20219step1 raw20219step0; decide +kernel
      have hl : raw20219step1Labels = raw20219step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20219step0 raw20219step0Labels permutation38 permutation2
    _ = mixedMoment B node949 node949Labels := by rfl

def raw20220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw20220Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw20220step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw20220step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20220 raw20220Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw20220 raw20220Labels = mixedMoment B raw20220step0 raw20220step0Labels := by
      have hz : ∀ j, raw20220 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20220step0 = (fun i j => raw20220 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20220step0 raw20220; decide +kernel
      have hl : raw20220step0Labels = raw20220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20220 raw20220Labels permutation265 hz
    mixedMoment B raw20220step0 raw20220step0Labels = mixedMoment B raw20220step1 raw20220step1Labels := by
      have ha : raw20220step1 = (fun i j => raw20220step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20220step1 raw20220step0; decide +kernel
      have hl : raw20220step1Labels = raw20220step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20220step0 raw20220step0Labels permutation38 permutation2
    _ = mixedMoment B node1044 node1044Labels := by rfl

def raw20221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20221Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20221step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20221 raw20221Labels = mixedMoment B node1326 node1326Labels := by
  calc
    mixedMoment B raw20221 raw20221Labels = mixedMoment B raw20221step0 raw20221step0Labels := by
      have ha : raw20221step0 = (fun i j => raw20221 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20221step0 raw20221; decide +kernel
      have hl : raw20221step0Labels = raw20221Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20221 raw20221Labels permutation182 permutation2
    _ = mixedMoment B node1326 node1326Labels := by rfl

def raw20222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20222Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20222step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20222 raw20222Labels = mixedMoment B node1336 node1336Labels := by
  calc
    mixedMoment B raw20222 raw20222Labels = mixedMoment B raw20222step0 raw20222step0Labels := by
      have hz : ∀ j, raw20222 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20222step0 = (fun i j => raw20222 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20222step0 raw20222; decide +kernel
      have hl : raw20222step0Labels = raw20222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20222 raw20222Labels permutation265 hz
    _ = mixedMoment B node1336 node1336Labels := by rfl

def raw20223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20223Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20223step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20223 raw20223Labels = mixedMoment B node1332 node1332Labels := by
  calc
    mixedMoment B raw20223 raw20223Labels = mixedMoment B raw20223step0 raw20223step0Labels := by
      have hz : ∀ j, raw20223 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20223step0 = (fun i j => raw20223 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20223step0 raw20223; decide +kernel
      have hl : raw20223step0Labels = raw20223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20223 raw20223Labels permutation265 hz
    _ = mixedMoment B node1332 node1332Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
