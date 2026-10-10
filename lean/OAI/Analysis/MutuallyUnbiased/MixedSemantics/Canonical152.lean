import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw19456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![4, 0, -4]]
def raw19456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![4, 0, -4]]
def raw19456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19456step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, -1, 2], ![4, 0, -4]]
def raw19456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19456step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw19456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19456step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw19456step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19456 raw19456Labels = mixedMoment B node813 node813Labels := by
  calc
    mixedMoment B raw19456 raw19456Labels = mixedMoment B raw19456step0 raw19456step0Labels := by
      have hz : ∀ j, raw19456 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19456step0 = (fun i j => raw19456 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19456step0 raw19456; decide +kernel
      have hl : raw19456step0Labels = raw19456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19456 raw19456Labels permutation346 hz
    mixedMoment B raw19456step0 raw19456step0Labels = mixedMoment B raw19456step1 raw19456step1Labels := by
      have hz : ∀ j, raw19456step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19456step1 = (fun i j => raw19456step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19456step1 raw19456step0; decide +kernel
      have hl : raw19456step1Labels = raw19456step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19456step0 raw19456step0Labels permutation56 hz
    mixedMoment B raw19456step1 raw19456step1Labels = mixedMoment B raw19456step2 raw19456step2Labels := by
      have ha : raw19456step2 = (fun i j => raw19456step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19456step2 raw19456step1; decide +kernel
      have hl : raw19456step2Labels = raw19456step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19456step1 raw19456step1Labels permutation29 permutation2
    mixedMoment B raw19456step2 raw19456step2Labels = mixedMoment B raw19456step3 raw19456step3Labels := by
      have ha : raw19456step3 = -raw19456step2 := by apply Matrix.ext; change ∀ i j, raw19456step3 i j = -(raw19456step2 i j); unfold raw19456step3 raw19456step2; decide +kernel
      have hl : raw19456step3Labels = raw19456step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node813 node813Labels := by rfl

def raw19457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![3, 1, -4]]
def raw19457Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![3, 1, -4]]
def raw19457step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19457step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -2, 2], ![3, 1, -4]]
def raw19457step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19457step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw19457step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19457step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw19457step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19457 raw19457Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw19457 raw19457Labels = mixedMoment B raw19457step0 raw19457step0Labels := by
      have hz : ∀ j, raw19457 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19457step0 = (fun i j => raw19457 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19457step0 raw19457; decide +kernel
      have hl : raw19457step0Labels = raw19457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19457 raw19457Labels permutation346 hz
    mixedMoment B raw19457step0 raw19457step0Labels = mixedMoment B raw19457step1 raw19457step1Labels := by
      have hz : ∀ j, raw19457step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19457step1 = (fun i j => raw19457step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19457step1 raw19457step0; decide +kernel
      have hl : raw19457step1Labels = raw19457step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19457step0 raw19457step0Labels permutation56 hz
    mixedMoment B raw19457step1 raw19457step1Labels = mixedMoment B raw19457step2 raw19457step2Labels := by
      have ha : raw19457step2 = (fun i j => raw19457step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19457step2 raw19457step1; decide +kernel
      have hl : raw19457step2Labels = raw19457step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19457step1 raw19457step1Labels permutation29 permutation2
    mixedMoment B raw19457step2 raw19457step2Labels = mixedMoment B raw19457step3 raw19457step3Labels := by
      have ha : raw19457step3 = -raw19457step2 := by apply Matrix.ext; change ∀ i j, raw19457step3 i j = -(raw19457step2 i j); unfold raw19457step3 raw19457step2; decide +kernel
      have hl : raw19457step3Labels = raw19457step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1716 node1716Labels := by rfl

def raw19458 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![-1, 1], ![-2, 2], ![4, -4]]
def raw19458Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19458step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![-2, 2], ![4, -4]]
def raw19458step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19458step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![4, -4]]
def raw19458step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19458step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw19458step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19458step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw19458step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19458 raw19458Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw19458 raw19458Labels = mixedMoment B raw19458step0 raw19458step0Labels := by
      have hz : ∀ j, raw19458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19458step0 = (fun i j => raw19458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19458step0 raw19458; decide +kernel
      have hl : raw19458step0Labels = raw19458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19458 raw19458Labels permutation346 hz
    mixedMoment B raw19458step0 raw19458step0Labels = mixedMoment B raw19458step1 raw19458step1Labels := by
      have hz : ∀ j, raw19458step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19458step1 = (fun i j => raw19458step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19458step1 raw19458step0; decide +kernel
      have hl : raw19458step1Labels = raw19458step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19458step0 raw19458step0Labels permutation56 hz
    mixedMoment B raw19458step1 raw19458step1Labels = mixedMoment B raw19458step2 raw19458step2Labels := by
      have ha : raw19458step2 = (fun i j => raw19458step1 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19458step2 raw19458step1; decide +kernel
      have hl : raw19458step2Labels = raw19458step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19458step1 raw19458step1Labels permutation26 permutation0
    mixedMoment B raw19458step2 raw19458step2Labels = mixedMoment B raw19458step3 raw19458step3Labels := by
      have ha : raw19458step3 = -raw19458step2 := by apply Matrix.ext; change ∀ i j, raw19458step3 i j = -(raw19458step2 i j); unfold raw19458step3 raw19458step2; decide +kernel
      have hl : raw19458step3Labels = raw19458step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw19459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19459step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-4, 3, 1]]
def raw19459step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19459step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw19459step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19459 raw19459Labels = mixedMoment B node779 node779Labels := by
  calc
    mixedMoment B raw19459 raw19459Labels = mixedMoment B raw19459step0 raw19459step0Labels := by
      have hz : ∀ j, raw19459 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19459step0 = (fun i j => raw19459 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19459step0 raw19459; decide +kernel
      have hl : raw19459step0Labels = raw19459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19459 raw19459Labels permutation265 hz
    mixedMoment B raw19459step0 raw19459step0Labels = mixedMoment B raw19459step1 raw19459step1Labels := by
      have ha : raw19459step1 = (fun i j => raw19459step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19459step1 raw19459step0; decide +kernel
      have hl : raw19459step1Labels = raw19459step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19459step0 raw19459step0Labels permutation137 permutation2
    mixedMoment B raw19459step1 raw19459step1Labels = mixedMoment B raw19459step2 raw19459step2Labels := by
      have ha : raw19459step2 = -raw19459step1 := by apply Matrix.ext; change ∀ i j, raw19459step2 i j = -(raw19459step1 i j); unfold raw19459step2 raw19459step1; decide +kernel
      have hl : raw19459step2Labels = raw19459step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node779 node779Labels := by rfl

def raw19460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw19460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19460step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw19460step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19460 raw19460Labels = mixedMoment B node776 node776Labels := by
  calc
    mixedMoment B raw19460 raw19460Labels = mixedMoment B raw19460step0 raw19460step0Labels := by
      have ha : raw19460step0 = (fun i j => raw19460 (permutation640 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19460step0 raw19460; decide +kernel
      have hl : raw19460step0Labels = raw19460Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19460 raw19460Labels permutation640 permutation2
    mixedMoment B raw19460step0 raw19460step0Labels = mixedMoment B raw19460step1 raw19460step1Labels := by
      have ha : raw19460step1 = -raw19460step0 := by apply Matrix.ext; change ∀ i j, raw19460step1 i j = -(raw19460step0 i j); unfold raw19460step1 raw19460step0; decide +kernel
      have hl : raw19460step1Labels = raw19460step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node776 node776Labels := by rfl

def raw19461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19461Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw19461step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19461step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw19461step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19461 raw19461Labels = mixedMoment B node787 node787Labels := by
  calc
    mixedMoment B raw19461 raw19461Labels = mixedMoment B raw19461step0 raw19461step0Labels := by
      have hz : ∀ j, raw19461 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19461step0 = (fun i j => raw19461 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19461step0 raw19461; decide +kernel
      have hl : raw19461step0Labels = raw19461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19461 raw19461Labels permutation265 hz
    mixedMoment B raw19461step0 raw19461step0Labels = mixedMoment B raw19461step1 raw19461step1Labels := by
      have ha : raw19461step1 = (fun i j => raw19461step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19461step1 raw19461step0; decide +kernel
      have hl : raw19461step1Labels = raw19461step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19461step0 raw19461step0Labels permutation145 permutation2
    mixedMoment B raw19461step1 raw19461step1Labels = mixedMoment B raw19461step2 raw19461step2Labels := by
      have ha : raw19461step2 = -raw19461step1 := by apply Matrix.ext; change ∀ i j, raw19461step2 i j = -(raw19461step1 i j); unfold raw19461step2 raw19461step1; decide +kernel
      have hl : raw19461step2Labels = raw19461step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node787 node787Labels := by rfl

def raw19462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw19462step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19462step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw19462step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19462 raw19462Labels = mixedMoment B node787 node787Labels := by
  calc
    mixedMoment B raw19462 raw19462Labels = mixedMoment B raw19462step0 raw19462step0Labels := by
      have hz : ∀ j, raw19462 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19462step0 = (fun i j => raw19462 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19462step0 raw19462; decide +kernel
      have hl : raw19462step0Labels = raw19462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19462 raw19462Labels permutation265 hz
    mixedMoment B raw19462step0 raw19462step0Labels = mixedMoment B raw19462step1 raw19462step1Labels := by
      have ha : raw19462step1 = (fun i j => raw19462step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19462step1 raw19462step0; decide +kernel
      have hl : raw19462step1Labels = raw19462step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19462step0 raw19462step0Labels permutation139 permutation2
    mixedMoment B raw19462step1 raw19462step1Labels = mixedMoment B raw19462step2 raw19462step2Labels := by
      have ha : raw19462step2 = -raw19462step1 := by apply Matrix.ext; change ∀ i j, raw19462step2 i j = -(raw19462step1 i j); unfold raw19462step2 raw19462step1; decide +kernel
      have hl : raw19462step2Labels = raw19462step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node787 node787Labels := by rfl

def raw19463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![4, 0, -4]]
def raw19463Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![4, 0, -4]]
def raw19463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw19463step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19463step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw19463step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19463 raw19463Labels = mixedMoment B node787 node787Labels := by
  calc
    mixedMoment B raw19463 raw19463Labels = mixedMoment B raw19463step0 raw19463step0Labels := by
      have hz : ∀ j, raw19463 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19463step0 = (fun i j => raw19463 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19463step0 raw19463; decide +kernel
      have hl : raw19463step0Labels = raw19463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19463 raw19463Labels permutation265 hz
    mixedMoment B raw19463step0 raw19463step0Labels = mixedMoment B raw19463step1 raw19463step1Labels := by
      have ha : raw19463step1 = (fun i j => raw19463step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19463step1 raw19463step0; decide +kernel
      have hl : raw19463step1Labels = raw19463step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19463step0 raw19463step0Labels permutation137 permutation2
    mixedMoment B raw19463step1 raw19463step1Labels = mixedMoment B raw19463step2 raw19463step2Labels := by
      have ha : raw19463step2 = -raw19463step1 := by apply Matrix.ext; change ∀ i j, raw19463step2 i j = -(raw19463step1 i j); unfold raw19463step2 raw19463step1; decide +kernel
      have hl : raw19463step2Labels = raw19463step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node787 node787Labels := by rfl

def raw19464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![3, 1, -4]]
def raw19464Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![3, 1, -4]]
def raw19464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19464step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw19464step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19464step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw19464step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19464 raw19464Labels = mixedMoment B node1700 node1700Labels := by
  calc
    mixedMoment B raw19464 raw19464Labels = mixedMoment B raw19464step0 raw19464step0Labels := by
      have hz : ∀ j, raw19464 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19464step0 = (fun i j => raw19464 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19464step0 raw19464; decide +kernel
      have hl : raw19464step0Labels = raw19464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19464 raw19464Labels permutation265 hz
    mixedMoment B raw19464step0 raw19464step0Labels = mixedMoment B raw19464step1 raw19464step1Labels := by
      have ha : raw19464step1 = (fun i j => raw19464step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19464step1 raw19464step0; decide +kernel
      have hl : raw19464step1Labels = raw19464step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19464step0 raw19464step0Labels permutation137 permutation2
    mixedMoment B raw19464step1 raw19464step1Labels = mixedMoment B raw19464step2 raw19464step2Labels := by
      have ha : raw19464step2 = -raw19464step1 := by apply Matrix.ext; change ∀ i j, raw19464step2 i j = -(raw19464step1 i j); unfold raw19464step2 raw19464step1; decide +kernel
      have hl : raw19464step2Labels = raw19464step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1700 node1700Labels := by rfl

def raw19465 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![-1, 1], ![-1, 1], ![4, -4]]
def raw19465Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19465step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![4, -4]]
def raw19465step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19465step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw19465step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19465step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw19465step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19465 raw19465Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw19465 raw19465Labels = mixedMoment B raw19465step0 raw19465step0Labels := by
      have hz : ∀ j, raw19465 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19465step0 = (fun i j => raw19465 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19465step0 raw19465; decide +kernel
      have hl : raw19465step0Labels = raw19465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19465 raw19465Labels permutation265 hz
    mixedMoment B raw19465step0 raw19465step0Labels = mixedMoment B raw19465step1 raw19465step1Labels := by
      have ha : raw19465step1 = (fun i j => raw19465step0 (permutation128 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19465step1 raw19465step0; decide +kernel
      have hl : raw19465step1Labels = raw19465step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19465step0 raw19465step0Labels permutation128 permutation0
    mixedMoment B raw19465step1 raw19465step1Labels = mixedMoment B raw19465step2 raw19465step2Labels := by
      have ha : raw19465step2 = -raw19465step1 := by apply Matrix.ext; change ∀ i j, raw19465step2 i j = -(raw19465step1 i j); unfold raw19465step2 raw19465step1; decide +kernel
      have hl : raw19465step2Labels = raw19465step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4068 node4068Labels := by rfl

def raw19466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw19466Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw19466step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19466step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19466step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19466step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw19466step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19466step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw19466step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19466 raw19466Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw19466 raw19466Labels = mixedMoment B raw19466step0 raw19466step0Labels := by
      have hz : ∀ j, raw19466 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19466step0 = (fun i j => raw19466 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19466step0 raw19466; decide +kernel
      have hl : raw19466step0Labels = raw19466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19466 raw19466Labels permutation434 hz
    mixedMoment B raw19466step0 raw19466step0Labels = mixedMoment B raw19466step1 raw19466step1Labels := by
      have hz : ∀ j, raw19466step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19466step1 = (fun i j => raw19466step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19466step1 raw19466step0; decide +kernel
      have hl : raw19466step1Labels = raw19466step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19466step0 raw19466step0Labels permutation80 hz
    mixedMoment B raw19466step1 raw19466step1Labels = mixedMoment B raw19466step2 raw19466step2Labels := by
      have ha : raw19466step2 = (fun i j => raw19466step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19466step2 raw19466step1; decide +kernel
      have hl : raw19466step2Labels = raw19466step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19466step1 raw19466step1Labels permutation31 permutation2
    mixedMoment B raw19466step2 raw19466step2Labels = mixedMoment B raw19466step3 raw19466step3Labels := by
      have ha : raw19466step3 = -raw19466step2 := by apply Matrix.ext; change ∀ i j, raw19466step3 i j = -(raw19466step2 i j); unfold raw19466step3 raw19466step2; decide +kernel
      have hl : raw19466step3Labels = raw19466step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1242 node1242Labels := by rfl

def raw19467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw19467Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw19467step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19467step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19467step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19467 raw19467Labels = mixedMoment B node1221 node1221Labels := by
  calc
    mixedMoment B raw19467 raw19467Labels = mixedMoment B raw19467step0 raw19467step0Labels := by
      have hz : ∀ j, raw19467 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19467step0 = (fun i j => raw19467 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19467step0 raw19467; decide +kernel
      have hl : raw19467step0Labels = raw19467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19467 raw19467Labels permutation434 hz
    mixedMoment B raw19467step0 raw19467step0Labels = mixedMoment B raw19467step1 raw19467step1Labels := by
      have hz : ∀ j, raw19467step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19467step1 = (fun i j => raw19467step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19467step1 raw19467step0; decide +kernel
      have hl : raw19467step1Labels = raw19467step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19467step0 raw19467step0Labels permutation80 hz
    _ = mixedMoment B node1221 node1221Labels := by rfl

def raw19468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![4, -2, -2]]
def raw19468Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![4, -2, -2]]
def raw19468step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19468step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19468 raw19468Labels = mixedMoment B node1115 node1115Labels := by
  calc
    mixedMoment B raw19468 raw19468Labels = mixedMoment B raw19468step0 raw19468step0Labels := by
      have hz : ∀ j, raw19468 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19468step0 = (fun i j => raw19468 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19468step0 raw19468; decide +kernel
      have hl : raw19468step0Labels = raw19468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19468 raw19468Labels permutation434 hz
    mixedMoment B raw19468step0 raw19468step0Labels = mixedMoment B raw19468step1 raw19468step1Labels := by
      have ha : raw19468step1 = (fun i j => raw19468step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19468step1 raw19468step0; decide +kernel
      have hl : raw19468step1Labels = raw19468step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19468step0 raw19468step0Labels permutation34 permutation2
    _ = mixedMoment B node1115 node1115Labels := by rfl

def raw19469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![4, -2, -2]]
def raw19469Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![4, -2, -2]]
def raw19469step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19469step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw19469step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19469 raw19469Labels = mixedMoment B node1115 node1115Labels := by
  calc
    mixedMoment B raw19469 raw19469Labels = mixedMoment B raw19469step0 raw19469step0Labels := by
      have hz : ∀ j, raw19469 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19469step0 = (fun i j => raw19469 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19469step0 raw19469; decide +kernel
      have hl : raw19469step0Labels = raw19469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19469 raw19469Labels permutation346 hz
    mixedMoment B raw19469step0 raw19469step0Labels = mixedMoment B raw19469step1 raw19469step1Labels := by
      have ha : raw19469step1 = (fun i j => raw19469step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19469step1 raw19469step0; decide +kernel
      have hl : raw19469step1Labels = raw19469step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19469step0 raw19469step0Labels permutation34 permutation2
    _ = mixedMoment B node1115 node1115Labels := by rfl

def raw19470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19470Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw19470step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19470step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19470step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19470 raw19470Labels = mixedMoment B node1140 node1140Labels := by
  calc
    mixedMoment B raw19470 raw19470Labels = mixedMoment B raw19470step0 raw19470step0Labels := by
      have hz : ∀ j, raw19470 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19470step0 = (fun i j => raw19470 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19470step0 raw19470; decide +kernel
      have hl : raw19470step0Labels = raw19470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19470 raw19470Labels permutation434 hz
    mixedMoment B raw19470step0 raw19470step0Labels = mixedMoment B raw19470step1 raw19470step1Labels := by
      have hz : ∀ j, raw19470step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19470step1 = (fun i j => raw19470step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19470step1 raw19470step0; decide +kernel
      have hl : raw19470step1Labels = raw19470step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19470step0 raw19470step0Labels permutation80 hz
    _ = mixedMoment B node1140 node1140Labels := by rfl

def raw19471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![5, -3, -2]]
def raw19471Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![5, -3, -2]]
def raw19471step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19471step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![5, -3, -2]]
def raw19471step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19471step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -3, -2], ![0, 1, -1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19471step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19471step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19471step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19471 raw19471Labels = mixedMoment B node633 node633Labels := by
  calc
    mixedMoment B raw19471 raw19471Labels = mixedMoment B raw19471step0 raw19471step0Labels := by
      have hz : ∀ j, raw19471 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19471step0 = (fun i j => raw19471 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19471step0 raw19471; decide +kernel
      have hl : raw19471step0Labels = raw19471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19471 raw19471Labels permutation434 hz
    mixedMoment B raw19471step0 raw19471step0Labels = mixedMoment B raw19471step1 raw19471step1Labels := by
      have hz : ∀ j, raw19471step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19471step1 = (fun i j => raw19471step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19471step1 raw19471step0; decide +kernel
      have hl : raw19471step1Labels = raw19471step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19471step0 raw19471step0Labels permutation80 hz
    mixedMoment B raw19471step1 raw19471step1Labels = mixedMoment B raw19471step2 raw19471step2Labels := by
      have ha : raw19471step2 = (fun i j => raw19471step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19471step2 raw19471step1; decide +kernel
      have hl : raw19471step2Labels = raw19471step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19471step1 raw19471step1Labels permutation31 permutation2
    mixedMoment B raw19471step2 raw19471step2Labels = mixedMoment B raw19471step3 raw19471step3Labels := by
      have ha : raw19471step3 = -raw19471step2 := by apply Matrix.ext; change ∀ i j, raw19471step3 i j = -(raw19471step2 i j); unfold raw19471step3 raw19471step2; decide +kernel
      have hl : raw19471step3Labels = raw19471step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node633 node633Labels := by rfl

def raw19472 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]
def raw19472Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19472step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![2, -2]]
def raw19472step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19472step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw19472step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19472 raw19472Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw19472 raw19472Labels = mixedMoment B raw19472step0 raw19472step0Labels := by
      have hz : ∀ j, raw19472 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19472step0 = (fun i j => raw19472 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19472step0 raw19472; decide +kernel
      have hl : raw19472step0Labels = raw19472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19472 raw19472Labels permutation434 hz
    mixedMoment B raw19472step0 raw19472step0Labels = mixedMoment B raw19472step1 raw19472step1Labels := by
      have hz : ∀ j, raw19472step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19472step1 = (fun i j => raw19472step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19472step1 raw19472step0; decide +kernel
      have hl : raw19472step1Labels = raw19472step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19472step0 raw19472step0Labels permutation80 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw19473 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19473Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19473step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19473step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19473step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19473step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw19473step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19473 raw19473Labels = mixedMoment B node3298 node3298Labels := by
  calc
    mixedMoment B raw19473 raw19473Labels = mixedMoment B raw19473step0 raw19473step0Labels := by
      have hz : ∀ j, raw19473 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19473step0 = (fun i j => raw19473 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19473step0 raw19473; decide +kernel
      have hl : raw19473step0Labels = raw19473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19473 raw19473Labels permutation434 hz
    mixedMoment B raw19473step0 raw19473step0Labels = mixedMoment B raw19473step1 raw19473step1Labels := by
      have hz : ∀ j, raw19473step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19473step1 = (fun i j => raw19473step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19473step1 raw19473step0; decide +kernel
      have hl : raw19473step1Labels = raw19473step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19473step0 raw19473step0Labels permutation80 hz
    mixedMoment B raw19473step1 raw19473step1Labels = mixedMoment B raw19473step2 raw19473step2Labels := by
      have ha : raw19473step2 = (fun i j => raw19473step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19473step2 raw19473step1; decide +kernel
      have hl : raw19473step2Labels = raw19473step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19473step1 raw19473step1Labels permutation29 permutation2
    _ = mixedMoment B node3298 node3298Labels := by rfl

def raw19474 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19474Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19474step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19474step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19474step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-2, 2, 0], ![-2, -2, 4]]
def raw19474step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19474step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -2, 0], ![2, 2, -4]]
def raw19474step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19474 raw19474Labels = mixedMoment B node1629 node1629Labels := by
  calc
    mixedMoment B raw19474 raw19474Labels = mixedMoment B raw19474step0 raw19474step0Labels := by
      have hz : ∀ j, raw19474 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19474step0 = (fun i j => raw19474 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19474step0 raw19474; decide +kernel
      have hl : raw19474step0Labels = raw19474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19474 raw19474Labels permutation434 hz
    mixedMoment B raw19474step0 raw19474step0Labels = mixedMoment B raw19474step1 raw19474step1Labels := by
      have hz : ∀ j, raw19474step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19474step1 = (fun i j => raw19474step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19474step1 raw19474step0; decide +kernel
      have hl : raw19474step1Labels = raw19474step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19474step0 raw19474step0Labels permutation80 hz
    mixedMoment B raw19474step1 raw19474step1Labels = mixedMoment B raw19474step2 raw19474step2Labels := by
      have ha : raw19474step2 = (fun i j => raw19474step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19474step2 raw19474step1; decide +kernel
      have hl : raw19474step2Labels = raw19474step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19474step1 raw19474step1Labels permutation10 permutation2
    mixedMoment B raw19474step2 raw19474step2Labels = mixedMoment B raw19474step3 raw19474step3Labels := by
      have ha : raw19474step3 = -raw19474step2 := by apply Matrix.ext; change ∀ i j, raw19474step3 i j = -(raw19474step2 i j); unfold raw19474step3 raw19474step2; decide +kernel
      have hl : raw19474step3Labels = raw19474step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1629 node1629Labels := by rfl

def raw19475 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19475Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19475step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19475step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19475step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19475step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw19475step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19475 raw19475Labels = mixedMoment B node1615 node1615Labels := by
  calc
    mixedMoment B raw19475 raw19475Labels = mixedMoment B raw19475step0 raw19475step0Labels := by
      have hz : ∀ j, raw19475 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19475step0 = (fun i j => raw19475 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19475step0 raw19475; decide +kernel
      have hl : raw19475step0Labels = raw19475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19475 raw19475Labels permutation434 hz
    mixedMoment B raw19475step0 raw19475step0Labels = mixedMoment B raw19475step1 raw19475step1Labels := by
      have ha : raw19475step1 = (fun i j => raw19475step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19475step1 raw19475step0; decide +kernel
      have hl : raw19475step1Labels = raw19475step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19475step0 raw19475step0Labels permutation44 permutation2
    mixedMoment B raw19475step1 raw19475step1Labels = mixedMoment B raw19475step2 raw19475step2Labels := by
      have ha : raw19475step2 = -raw19475step1 := by apply Matrix.ext; change ∀ i j, raw19475step2 i j = -(raw19475step1 i j); unfold raw19475step2 raw19475step1; decide +kernel
      have hl : raw19475step2Labels = raw19475step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1615 node1615Labels := by rfl

def raw19476 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19476Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19476step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19476step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw19476step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19476 raw19476Labels = mixedMoment B node1615 node1615Labels := by
  calc
    mixedMoment B raw19476 raw19476Labels = mixedMoment B raw19476step0 raw19476step0Labels := by
      have hz : ∀ j, raw19476 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19476step0 = (fun i j => raw19476 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19476step0 raw19476; decide +kernel
      have hl : raw19476step0Labels = raw19476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19476 raw19476Labels permutation346 hz
    mixedMoment B raw19476step0 raw19476step0Labels = mixedMoment B raw19476step1 raw19476step1Labels := by
      have ha : raw19476step1 = (fun i j => raw19476step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19476step1 raw19476step0; decide +kernel
      have hl : raw19476step1Labels = raw19476step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19476step0 raw19476step0Labels permutation44 permutation2
    mixedMoment B raw19476step1 raw19476step1Labels = mixedMoment B raw19476step2 raw19476step2Labels := by
      have ha : raw19476step2 = -raw19476step1 := by apply Matrix.ext; change ∀ i j, raw19476step2 i j = -(raw19476step1 i j); unfold raw19476step2 raw19476step1; decide +kernel
      have hl : raw19476step2Labels = raw19476step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1615 node1615Labels := by rfl

def raw19477 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19477Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19477step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19477step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19477step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19477step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19477step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19477step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw19477step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19477 raw19477Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw19477 raw19477Labels = mixedMoment B raw19477step0 raw19477step0Labels := by
      have hz : ∀ j, raw19477 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19477step0 = (fun i j => raw19477 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19477step0 raw19477; decide +kernel
      have hl : raw19477step0Labels = raw19477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19477 raw19477Labels permutation520 hz
    mixedMoment B raw19477step0 raw19477step0Labels = mixedMoment B raw19477step1 raw19477step1Labels := by
      have hz : ∀ j, raw19477step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19477step1 = (fun i j => raw19477step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19477step1 raw19477step0; decide +kernel
      have hl : raw19477step1Labels = raw19477step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19477step0 raw19477step0Labels permutation104 hz
    mixedMoment B raw19477step1 raw19477step1Labels = mixedMoment B raw19477step2 raw19477step2Labels := by
      have hz : ∀ j, raw19477step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19477step2 = (fun i j => raw19477step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19477step2 raw19477step1; decide +kernel
      have hl : raw19477step2Labels = raw19477step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19477step1 raw19477step1Labels permutation20 hz
    mixedMoment B raw19477step2 raw19477step2Labels = mixedMoment B raw19477step3 raw19477step3Labels := by
      have ha : raw19477step3 = -raw19477step2 := by apply Matrix.ext; change ∀ i j, raw19477step3 i j = -(raw19477step2 i j); unfold raw19477step3 raw19477step2; decide +kernel
      have hl : raw19477step3Labels = raw19477step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1752 node1752Labels := by rfl

def raw19478 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19478Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19478step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19478step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw19478step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19478 raw19478Labels = mixedMoment B node1620 node1620Labels := by
  calc
    mixedMoment B raw19478 raw19478Labels = mixedMoment B raw19478step0 raw19478step0Labels := by
      have hz : ∀ j, raw19478 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19478step0 = (fun i j => raw19478 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19478step0 raw19478; decide +kernel
      have hl : raw19478step0Labels = raw19478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19478 raw19478Labels permutation434 hz
    mixedMoment B raw19478step0 raw19478step0Labels = mixedMoment B raw19478step1 raw19478step1Labels := by
      have hz : ∀ j, raw19478step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19478step1 = (fun i j => raw19478step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19478step1 raw19478step0; decide +kernel
      have hl : raw19478step1Labels = raw19478step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19478step0 raw19478step0Labels permutation80 hz
    mixedMoment B raw19478step1 raw19478step1Labels = mixedMoment B raw19478step2 raw19478step2Labels := by
      have ha : raw19478step2 = (fun i j => raw19478step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19478step2 raw19478step1; decide +kernel
      have hl : raw19478step2Labels = raw19478step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19478step1 raw19478step1Labels permutation29 permutation2
    _ = mixedMoment B node1620 node1620Labels := by rfl

def raw19479 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19479Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19479step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19479step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19479step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19479step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw19479step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19479 raw19479Labels = mixedMoment B node3298 node3298Labels := by
  calc
    mixedMoment B raw19479 raw19479Labels = mixedMoment B raw19479step0 raw19479step0Labels := by
      have hz : ∀ j, raw19479 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19479step0 = (fun i j => raw19479 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19479step0 raw19479; decide +kernel
      have hl : raw19479step0Labels = raw19479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19479 raw19479Labels permutation434 hz
    mixedMoment B raw19479step0 raw19479step0Labels = mixedMoment B raw19479step1 raw19479step1Labels := by
      have hz : ∀ j, raw19479step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19479step1 = (fun i j => raw19479step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19479step1 raw19479step0; decide +kernel
      have hl : raw19479step1Labels = raw19479step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19479step0 raw19479step0Labels permutation56 hz
    mixedMoment B raw19479step1 raw19479step1Labels = mixedMoment B raw19479step2 raw19479step2Labels := by
      have ha : raw19479step2 = (fun i j => raw19479step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19479step2 raw19479step1; decide +kernel
      have hl : raw19479step2Labels = raw19479step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19479step1 raw19479step1Labels permutation29 permutation2
    _ = mixedMoment B node3298 node3298Labels := by rfl

def raw19480 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19480Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19480step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19480step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19480step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw19480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19480 raw19480Labels = mixedMoment B node3298 node3298Labels := by
  calc
    mixedMoment B raw19480 raw19480Labels = mixedMoment B raw19480step0 raw19480step0Labels := by
      have hz : ∀ j, raw19480 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19480step0 = (fun i j => raw19480 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19480step0 raw19480; decide +kernel
      have hl : raw19480step0Labels = raw19480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19480 raw19480Labels permutation346 hz
    mixedMoment B raw19480step0 raw19480step0Labels = mixedMoment B raw19480step1 raw19480step1Labels := by
      have hz : ∀ j, raw19480step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19480step1 = (fun i j => raw19480step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19480step1 raw19480step0; decide +kernel
      have hl : raw19480step1Labels = raw19480step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19480step0 raw19480step0Labels permutation56 hz
    mixedMoment B raw19480step1 raw19480step1Labels = mixedMoment B raw19480step2 raw19480step2Labels := by
      have ha : raw19480step2 = (fun i j => raw19480step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19480step2 raw19480step1; decide +kernel
      have hl : raw19480step2Labels = raw19480step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19480step1 raw19480step1Labels permutation29 permutation2
    _ = mixedMoment B node3298 node3298Labels := by rfl

def raw19481 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19481Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19481step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19481step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19481step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19481step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, -2, 4]]
def raw19481step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19481step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, 2, -4], ![-2, -2, 4]]
def raw19481step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19481step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, -2, 4], ![2, 2, -4]]
def raw19481step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19481 raw19481Labels = mixedMoment B node3313 node3313Labels := by
  calc
    mixedMoment B raw19481 raw19481Labels = mixedMoment B raw19481step0 raw19481step0Labels := by
      have hz : ∀ j, raw19481 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19481step0 = (fun i j => raw19481 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19481step0 raw19481; decide +kernel
      have hl : raw19481step0Labels = raw19481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19481 raw19481Labels permutation520 hz
    mixedMoment B raw19481step0 raw19481step0Labels = mixedMoment B raw19481step1 raw19481step1Labels := by
      have hz : ∀ j, raw19481step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19481step1 = (fun i j => raw19481step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19481step1 raw19481step0; decide +kernel
      have hl : raw19481step1Labels = raw19481step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19481step0 raw19481step0Labels permutation104 hz
    mixedMoment B raw19481step1 raw19481step1Labels = mixedMoment B raw19481step2 raw19481step2Labels := by
      have hz : ∀ j, raw19481step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19481step2 = (fun i j => raw19481step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19481step2 raw19481step1; decide +kernel
      have hl : raw19481step2Labels = raw19481step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19481step1 raw19481step1Labels permutation20 hz
    mixedMoment B raw19481step2 raw19481step2Labels = mixedMoment B raw19481step3 raw19481step3Labels := by
      have hz : ∀ j, raw19481step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19481step3 = (fun i j => raw19481step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19481step3 raw19481step2; decide +kernel
      have hl : raw19481step3Labels = raw19481step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19481step2 raw19481step2Labels permutation4 hz
    mixedMoment B raw19481step3 raw19481step3Labels = mixedMoment B raw19481step4 raw19481step4Labels := by
      have ha : raw19481step4 = (fun i j => raw19481step3 (permutation1 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19481step4 raw19481step3; decide +kernel
      have hl : raw19481step4Labels = raw19481step3Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19481step3 raw19481step3Labels permutation1 permutation2
    _ = mixedMoment B node3313 node3313Labels := by rfl

def raw19482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw19482Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw19482step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19482step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -2, 2], ![4, -1, -3]]
def raw19482step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19482step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-4, 2, 2]]
def raw19482step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19482step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![4, -2, -2]]
def raw19482step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19482 raw19482Labels = mixedMoment B node994 node994Labels := by
  calc
    mixedMoment B raw19482 raw19482Labels = mixedMoment B raw19482step0 raw19482step0Labels := by
      have hz : ∀ j, raw19482 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19482step0 = (fun i j => raw19482 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19482step0 raw19482; decide +kernel
      have hl : raw19482step0Labels = raw19482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19482 raw19482Labels permutation434 hz
    mixedMoment B raw19482step0 raw19482step0Labels = mixedMoment B raw19482step1 raw19482step1Labels := by
      have hz : ∀ j, raw19482step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19482step1 = (fun i j => raw19482step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19482step1 raw19482step0; decide +kernel
      have hl : raw19482step1Labels = raw19482step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19482step0 raw19482step0Labels permutation80 hz
    mixedMoment B raw19482step1 raw19482step1Labels = mixedMoment B raw19482step2 raw19482step2Labels := by
      have ha : raw19482step2 = (fun i j => raw19482step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19482step2 raw19482step1; decide +kernel
      have hl : raw19482step2Labels = raw19482step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19482step1 raw19482step1Labels permutation29 permutation2
    mixedMoment B raw19482step2 raw19482step2Labels = mixedMoment B raw19482step3 raw19482step3Labels := by
      have ha : raw19482step3 = -raw19482step2 := by apply Matrix.ext; change ∀ i j, raw19482step3 i j = -(raw19482step2 i j); unfold raw19482step3 raw19482step2; decide +kernel
      have hl : raw19482step3Labels = raw19482step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node994 node994Labels := by rfl

def raw19483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw19483Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw19483step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![4, -1, -3]]
def raw19483step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19483step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 2, -1], ![-3, 1, 2]]
def raw19483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19483step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw19483step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19483 raw19483Labels = mixedMoment B node1055 node1055Labels := by
  calc
    mixedMoment B raw19483 raw19483Labels = mixedMoment B raw19483step0 raw19483step0Labels := by
      have hz : ∀ j, raw19483 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19483step0 = (fun i j => raw19483 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19483step0 raw19483; decide +kernel
      have hl : raw19483step0Labels = raw19483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19483 raw19483Labels permutation434 hz
    mixedMoment B raw19483step0 raw19483step0Labels = mixedMoment B raw19483step1 raw19483step1Labels := by
      have hz : ∀ j, raw19483step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19483step1 = (fun i j => raw19483step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19483step1 raw19483step0; decide +kernel
      have hl : raw19483step1Labels = raw19483step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19483step0 raw19483step0Labels permutation80 hz
    mixedMoment B raw19483step1 raw19483step1Labels = mixedMoment B raw19483step2 raw19483step2Labels := by
      have ha : raw19483step2 = (fun i j => raw19483step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19483step2 raw19483step1; decide +kernel
      have hl : raw19483step2Labels = raw19483step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19483step1 raw19483step1Labels permutation31 permutation2
    mixedMoment B raw19483step2 raw19483step2Labels = mixedMoment B raw19483step3 raw19483step3Labels := by
      have ha : raw19483step3 = -raw19483step2 := by apply Matrix.ext; change ∀ i j, raw19483step3 i j = -(raw19483step2 i j); unfold raw19483step3 raw19483step2; decide +kernel
      have hl : raw19483step3Labels = raw19483step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1055 node1055Labels := by rfl

def raw19484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![4, -1, -3]]
def raw19484Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw19484step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw19484step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19484step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw19484step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19484 raw19484Labels = mixedMoment B node989 node989Labels := by
  calc
    mixedMoment B raw19484 raw19484Labels = mixedMoment B raw19484step0 raw19484step0Labels := by
      have hz : ∀ j, raw19484 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19484step0 = (fun i j => raw19484 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19484step0 raw19484; decide +kernel
      have hl : raw19484step0Labels = raw19484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19484 raw19484Labels permutation434 hz
    mixedMoment B raw19484step0 raw19484step0Labels = mixedMoment B raw19484step1 raw19484step1Labels := by
      have ha : raw19484step1 = (fun i j => raw19484step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19484step1 raw19484step0; decide +kernel
      have hl : raw19484step1Labels = raw19484step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19484step0 raw19484step0Labels permutation139 permutation2
    mixedMoment B raw19484step1 raw19484step1Labels = mixedMoment B raw19484step2 raw19484step2Labels := by
      have ha : raw19484step2 = -raw19484step1 := by apply Matrix.ext; change ∀ i j, raw19484step2 i j = -(raw19484step1 i j); unfold raw19484step2 raw19484step1; decide +kernel
      have hl : raw19484step2Labels = raw19484step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node989 node989Labels := by rfl

def raw19485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw19485Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![4, -1, -3]]
def raw19485step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw19485step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19485step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw19485step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19485 raw19485Labels = mixedMoment B node989 node989Labels := by
  calc
    mixedMoment B raw19485 raw19485Labels = mixedMoment B raw19485step0 raw19485step0Labels := by
      have hz : ∀ j, raw19485 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19485step0 = (fun i j => raw19485 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19485step0 raw19485; decide +kernel
      have hl : raw19485step0Labels = raw19485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19485 raw19485Labels permutation346 hz
    mixedMoment B raw19485step0 raw19485step0Labels = mixedMoment B raw19485step1 raw19485step1Labels := by
      have ha : raw19485step1 = (fun i j => raw19485step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19485step1 raw19485step0; decide +kernel
      have hl : raw19485step1Labels = raw19485step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19485step0 raw19485step0Labels permutation139 permutation2
    mixedMoment B raw19485step1 raw19485step1Labels = mixedMoment B raw19485step2 raw19485step2Labels := by
      have ha : raw19485step2 = -raw19485step1 := by apply Matrix.ext; change ∀ i j, raw19485step2 i j = -(raw19485step1 i j); unfold raw19485step2 raw19485step1; decide +kernel
      have hl : raw19485step2Labels = raw19485step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node989 node989Labels := by rfl

def raw19486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw19486Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![4, -1, -3]]
def raw19486step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19486step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, -1, 2], ![4, -1, -3]]
def raw19486step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19486step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw19486step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19486step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw19486step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19486 raw19486Labels = mixedMoment B node1009 node1009Labels := by
  calc
    mixedMoment B raw19486 raw19486Labels = mixedMoment B raw19486step0 raw19486step0Labels := by
      have hz : ∀ j, raw19486 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19486step0 = (fun i j => raw19486 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19486step0 raw19486; decide +kernel
      have hl : raw19486step0Labels = raw19486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19486 raw19486Labels permutation434 hz
    mixedMoment B raw19486step0 raw19486step0Labels = mixedMoment B raw19486step1 raw19486step1Labels := by
      have hz : ∀ j, raw19486step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19486step1 = (fun i j => raw19486step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19486step1 raw19486step0; decide +kernel
      have hl : raw19486step1Labels = raw19486step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19486step0 raw19486step0Labels permutation80 hz
    mixedMoment B raw19486step1 raw19486step1Labels = mixedMoment B raw19486step2 raw19486step2Labels := by
      have ha : raw19486step2 = (fun i j => raw19486step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19486step2 raw19486step1; decide +kernel
      have hl : raw19486step2Labels = raw19486step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19486step1 raw19486step1Labels permutation29 permutation2
    mixedMoment B raw19486step2 raw19486step2Labels = mixedMoment B raw19486step3 raw19486step3Labels := by
      have ha : raw19486step3 = -raw19486step2 := by apply Matrix.ext; change ∀ i j, raw19486step3 i j = -(raw19486step2 i j); unfold raw19486step3 raw19486step2; decide +kernel
      have hl : raw19486step3Labels = raw19486step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1009 node1009Labels := by rfl

def raw19487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw19487Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw19487step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19487step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![3, 0, -3]]
def raw19487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19487step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw19487step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19487step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw19487step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19487 raw19487Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw19487 raw19487Labels = mixedMoment B raw19487step0 raw19487step0Labels := by
      have hz : ∀ j, raw19487 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19487step0 = (fun i j => raw19487 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19487step0 raw19487; decide +kernel
      have hl : raw19487step0Labels = raw19487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19487 raw19487Labels permutation434 hz
    mixedMoment B raw19487step0 raw19487step0Labels = mixedMoment B raw19487step1 raw19487step1Labels := by
      have hz : ∀ j, raw19487step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19487step1 = (fun i j => raw19487step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19487step1 raw19487step0; decide +kernel
      have hl : raw19487step1Labels = raw19487step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19487step0 raw19487step0Labels permutation80 hz
    mixedMoment B raw19487step1 raw19487step1Labels = mixedMoment B raw19487step2 raw19487step2Labels := by
      have ha : raw19487step2 = (fun i j => raw19487step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19487step2 raw19487step1; decide +kernel
      have hl : raw19487step2Labels = raw19487step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19487step1 raw19487step1Labels permutation29 permutation2
    mixedMoment B raw19487step2 raw19487step2Labels = mixedMoment B raw19487step3 raw19487step3Labels := by
      have ha : raw19487step3 = -raw19487step2 := by apply Matrix.ext; change ∀ i j, raw19487step3 i j = -(raw19487step2 i j); unfold raw19487step3 raw19487step2; decide +kernel
      have hl : raw19487step3Labels = raw19487step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2218 node2218Labels := by rfl

def raw19488 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![0, 0], ![-2, 2], ![3, -3]]
def raw19488Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19488step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![-2, 2], ![3, -3]]
def raw19488step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19488step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![3, -3]]
def raw19488step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19488step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw19488step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19488step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw19488step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19488 raw19488Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw19488 raw19488Labels = mixedMoment B raw19488step0 raw19488step0Labels := by
      have hz : ∀ j, raw19488 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19488step0 = (fun i j => raw19488 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19488step0 raw19488; decide +kernel
      have hl : raw19488step0Labels = raw19488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19488 raw19488Labels permutation434 hz
    mixedMoment B raw19488step0 raw19488step0Labels = mixedMoment B raw19488step1 raw19488step1Labels := by
      have hz : ∀ j, raw19488step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19488step1 = (fun i j => raw19488step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19488step1 raw19488step0; decide +kernel
      have hl : raw19488step1Labels = raw19488step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19488step0 raw19488step0Labels permutation80 hz
    mixedMoment B raw19488step1 raw19488step1Labels = mixedMoment B raw19488step2 raw19488step2Labels := by
      have ha : raw19488step2 = (fun i j => raw19488step1 (permutation28 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19488step2 raw19488step1; decide +kernel
      have hl : raw19488step2Labels = raw19488step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19488step1 raw19488step1Labels permutation28 permutation0
    mixedMoment B raw19488step2 raw19488step2Labels = mixedMoment B raw19488step3 raw19488step3Labels := by
      have ha : raw19488step3 = -raw19488step2 := by apply Matrix.ext; change ∀ i j, raw19488step3 i j = -(raw19488step2 i j); unfold raw19488step3 raw19488step2; decide +kernel
      have hl : raw19488step3Labels = raw19488step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw19489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw19489Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw19489step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19489step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -2, 2], ![3, 0, -3]]
def raw19489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19489step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw19489step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19489 raw19489Labels = mixedMoment B node1190 node1190Labels := by
  calc
    mixedMoment B raw19489 raw19489Labels = mixedMoment B raw19489step0 raw19489step0Labels := by
      have hz : ∀ j, raw19489 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19489step0 = (fun i j => raw19489 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19489step0 raw19489; decide +kernel
      have hl : raw19489step0Labels = raw19489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19489 raw19489Labels permutation434 hz
    mixedMoment B raw19489step0 raw19489step0Labels = mixedMoment B raw19489step1 raw19489step1Labels := by
      have hz : ∀ j, raw19489step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19489step1 = (fun i j => raw19489step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19489step1 raw19489step0; decide +kernel
      have hl : raw19489step1Labels = raw19489step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19489step0 raw19489step0Labels permutation80 hz
    mixedMoment B raw19489step1 raw19489step1Labels = mixedMoment B raw19489step2 raw19489step2Labels := by
      have ha : raw19489step2 = (fun i j => raw19489step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19489step2 raw19489step1; decide +kernel
      have hl : raw19489step2Labels = raw19489step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19489step1 raw19489step1Labels permutation10 permutation2
    _ = mixedMoment B node1190 node1190Labels := by rfl

def raw19490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw19490Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw19490step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw19490step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19490 raw19490Labels = mixedMoment B node1179 node1179Labels := by
  calc
    mixedMoment B raw19490 raw19490Labels = mixedMoment B raw19490step0 raw19490step0Labels := by
      have hz : ∀ j, raw19490 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19490step0 = (fun i j => raw19490 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19490step0 raw19490; decide +kernel
      have hl : raw19490step0Labels = raw19490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19490 raw19490Labels permutation434 hz
    mixedMoment B raw19490step0 raw19490step0Labels = mixedMoment B raw19490step1 raw19490step1Labels := by
      have ha : raw19490step1 = (fun i j => raw19490step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19490step1 raw19490step0; decide +kernel
      have hl : raw19490step1Labels = raw19490step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19490step0 raw19490step0Labels permutation44 permutation2
    _ = mixedMoment B node1179 node1179Labels := by rfl

def raw19491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw19491Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![3, 0, -3]]
def raw19491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw19491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19491 raw19491Labels = mixedMoment B node1179 node1179Labels := by
  calc
    mixedMoment B raw19491 raw19491Labels = mixedMoment B raw19491step0 raw19491step0Labels := by
      have hz : ∀ j, raw19491 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19491step0 = (fun i j => raw19491 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19491step0 raw19491; decide +kernel
      have hl : raw19491step0Labels = raw19491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19491 raw19491Labels permutation346 hz
    mixedMoment B raw19491step0 raw19491step0Labels = mixedMoment B raw19491step1 raw19491step1Labels := by
      have ha : raw19491step1 = (fun i j => raw19491step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19491step1 raw19491step0; decide +kernel
      have hl : raw19491step1Labels = raw19491step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19491step0 raw19491step0Labels permutation44 permutation2
    _ = mixedMoment B node1179 node1179Labels := by rfl

def raw19492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw19492Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw19492step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19492step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![3, 0, -3]]
def raw19492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19492 raw19492Labels = mixedMoment B node1258 node1258Labels := by
  calc
    mixedMoment B raw19492 raw19492Labels = mixedMoment B raw19492step0 raw19492step0Labels := by
      have hz : ∀ j, raw19492 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19492step0 = (fun i j => raw19492 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19492step0 raw19492; decide +kernel
      have hl : raw19492step0Labels = raw19492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19492 raw19492Labels permutation434 hz
    mixedMoment B raw19492step0 raw19492step0Labels = mixedMoment B raw19492step1 raw19492step1Labels := by
      have hz : ∀ j, raw19492step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19492step1 = (fun i j => raw19492step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19492step1 raw19492step0; decide +kernel
      have hl : raw19492step1Labels = raw19492step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19492step0 raw19492step0Labels permutation80 hz
    _ = mixedMoment B node1258 node1258Labels := by rfl

def raw19493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw19493Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw19493step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw19493step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19493step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19493step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19493 raw19493Labels = mixedMoment B node975 node975Labels := by
  calc
    mixedMoment B raw19493 raw19493Labels = mixedMoment B raw19493step0 raw19493step0Labels := by
      have hz : ∀ j, raw19493 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19493step0 = (fun i j => raw19493 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19493step0 raw19493; decide +kernel
      have hl : raw19493step0Labels = raw19493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19493 raw19493Labels permutation346 hz
    mixedMoment B raw19493step0 raw19493step0Labels = mixedMoment B raw19493step1 raw19493step1Labels := by
      have ha : raw19493step1 = (fun i j => raw19493step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19493step1 raw19493step0; decide +kernel
      have hl : raw19493step1Labels = raw19493step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19493step0 raw19493step0Labels permutation137 permutation2
    mixedMoment B raw19493step1 raw19493step1Labels = mixedMoment B raw19493step2 raw19493step2Labels := by
      have ha : raw19493step2 = -raw19493step1 := by apply Matrix.ext; change ∀ i j, raw19493step2 i j = -(raw19493step1 i j); unfold raw19493step2 raw19493step1; decide +kernel
      have hl : raw19493step2Labels = raw19493step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node975 node975Labels := by rfl

def raw19494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw19494Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw19494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw19494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19494step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw19494step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19494 raw19494Labels = mixedMoment B node1019 node1019Labels := by
  calc
    mixedMoment B raw19494 raw19494Labels = mixedMoment B raw19494step0 raw19494step0Labels := by
      have hz : ∀ j, raw19494 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19494step0 = (fun i j => raw19494 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19494step0 raw19494; decide +kernel
      have hl : raw19494step0Labels = raw19494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19494 raw19494Labels permutation346 hz
    mixedMoment B raw19494step0 raw19494step0Labels = mixedMoment B raw19494step1 raw19494step1Labels := by
      have ha : raw19494step1 = (fun i j => raw19494step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19494step1 raw19494step0; decide +kernel
      have hl : raw19494step1Labels = raw19494step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19494step0 raw19494step0Labels permutation145 permutation2
    mixedMoment B raw19494step1 raw19494step1Labels = mixedMoment B raw19494step2 raw19494step2Labels := by
      have ha : raw19494step2 = -raw19494step1 := by apply Matrix.ext; change ∀ i j, raw19494step2 i j = -(raw19494step1 i j); unfold raw19494step2 raw19494step1; decide +kernel
      have hl : raw19494step2Labels = raw19494step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1019 node1019Labels := by rfl

def raw19495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, -1, -3]]
def raw19495Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw19495step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19495step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw19495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19495 raw19495Labels = mixedMoment B node971 node971Labels := by
  calc
    mixedMoment B raw19495 raw19495Labels = mixedMoment B raw19495step0 raw19495step0Labels := by
      have ha : raw19495step0 = (fun i j => raw19495 (permutation616 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19495step0 raw19495; decide +kernel
      have hl : raw19495step0Labels = raw19495Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19495 raw19495Labels permutation616 permutation2
    mixedMoment B raw19495step0 raw19495step0Labels = mixedMoment B raw19495step1 raw19495step1Labels := by
      have ha : raw19495step1 = -raw19495step0 := by apply Matrix.ext; change ∀ i j, raw19495step1 i j = -(raw19495step0 i j); unfold raw19495step1 raw19495step0; decide +kernel
      have hl : raw19495step1Labels = raw19495step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node971 node971Labels := by rfl

def raw19496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw19496Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![4, -1, -3]]
def raw19496step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw19496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw19496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19496 raw19496Labels = mixedMoment B node982 node982Labels := by
  calc
    mixedMoment B raw19496 raw19496Labels = mixedMoment B raw19496step0 raw19496step0Labels := by
      have hz : ∀ j, raw19496 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19496step0 = (fun i j => raw19496 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19496step0 raw19496; decide +kernel
      have hl : raw19496step0Labels = raw19496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19496 raw19496Labels permutation346 hz
    mixedMoment B raw19496step0 raw19496step0Labels = mixedMoment B raw19496step1 raw19496step1Labels := by
      have ha : raw19496step1 = (fun i j => raw19496step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19496step1 raw19496step0; decide +kernel
      have hl : raw19496step1Labels = raw19496step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19496step0 raw19496step0Labels permutation139 permutation2
    mixedMoment B raw19496step1 raw19496step1Labels = mixedMoment B raw19496step2 raw19496step2Labels := by
      have ha : raw19496step2 = -raw19496step1 := by apply Matrix.ext; change ∀ i j, raw19496step2 i j = -(raw19496step1 i j); unfold raw19496step2 raw19496step1; decide +kernel
      have hl : raw19496step2Labels = raw19496step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node982 node982Labels := by rfl

def raw19497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw19497Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![4, -1, -3]]
def raw19497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw19497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19497step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw19497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19497 raw19497Labels = mixedMoment B node982 node982Labels := by
  calc
    mixedMoment B raw19497 raw19497Labels = mixedMoment B raw19497step0 raw19497step0Labels := by
      have hz : ∀ j, raw19497 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19497step0 = (fun i j => raw19497 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19497step0 raw19497; decide +kernel
      have hl : raw19497step0Labels = raw19497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19497 raw19497Labels permutation346 hz
    mixedMoment B raw19497step0 raw19497step0Labels = mixedMoment B raw19497step1 raw19497step1Labels := by
      have ha : raw19497step1 = (fun i j => raw19497step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19497step1 raw19497step0; decide +kernel
      have hl : raw19497step1Labels = raw19497step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19497step0 raw19497step0Labels permutation137 permutation2
    mixedMoment B raw19497step1 raw19497step1Labels = mixedMoment B raw19497step2 raw19497step2Labels := by
      have ha : raw19497step2 = -raw19497step1 := by apply Matrix.ext; change ∀ i j, raw19497step2 i j = -(raw19497step1 i j); unfold raw19497step2 raw19497step1; decide +kernel
      have hl : raw19497step2Labels = raw19497step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node982 node982Labels := by rfl

def raw19498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw19498Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw19498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw19498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19498step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw19498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19498 raw19498Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw19498 raw19498Labels = mixedMoment B raw19498step0 raw19498step0Labels := by
      have hz : ∀ j, raw19498 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19498step0 = (fun i j => raw19498 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19498step0 raw19498; decide +kernel
      have hl : raw19498step0Labels = raw19498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19498 raw19498Labels permutation346 hz
    mixedMoment B raw19498step0 raw19498step0Labels = mixedMoment B raw19498step1 raw19498step1Labels := by
      have ha : raw19498step1 = (fun i j => raw19498step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19498step1 raw19498step0; decide +kernel
      have hl : raw19498step1Labels = raw19498step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19498step0 raw19498step0Labels permutation137 permutation2
    mixedMoment B raw19498step1 raw19498step1Labels = mixedMoment B raw19498step2 raw19498step2Labels := by
      have ha : raw19498step2 = -raw19498step1 := by apply Matrix.ext; change ∀ i j, raw19498step2 i j = -(raw19498step1 i j); unfold raw19498step2 raw19498step1; decide +kernel
      have hl : raw19498step2Labels = raw19498step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2193 node2193Labels := by rfl

def raw19499 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![-1, 1], ![-1, 1], ![3, -3]]
def raw19499Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19499step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw19499step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19499step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw19499step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19499step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw19499step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19499 raw19499Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw19499 raw19499Labels = mixedMoment B raw19499step0 raw19499step0Labels := by
      have hz : ∀ j, raw19499 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19499step0 = (fun i j => raw19499 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19499step0 raw19499; decide +kernel
      have hl : raw19499step0Labels = raw19499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19499 raw19499Labels permutation346 hz
    mixedMoment B raw19499step0 raw19499step0Labels = mixedMoment B raw19499step1 raw19499step1Labels := by
      have ha : raw19499step1 = (fun i j => raw19499step0 (permutation137 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19499step1 raw19499step0; decide +kernel
      have hl : raw19499step1Labels = raw19499step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19499step0 raw19499step0Labels permutation137 permutation0
    mixedMoment B raw19499step1 raw19499step1Labels = mixedMoment B raw19499step2 raw19499step2Labels := by
      have ha : raw19499step2 = -raw19499step1 := by apply Matrix.ext; change ∀ i j, raw19499step2 i j = -(raw19499step1 i j); unfold raw19499step2 raw19499step1; decide +kernel
      have hl : raw19499step2Labels = raw19499step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw19500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw19500Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw19500step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw19500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19500 raw19500Labels = mixedMoment B node1202 node1202Labels := by
  calc
    mixedMoment B raw19500 raw19500Labels = mixedMoment B raw19500step0 raw19500step0Labels := by
      have hz : ∀ j, raw19500 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19500step0 = (fun i j => raw19500 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19500step0 raw19500; decide +kernel
      have hl : raw19500step0Labels = raw19500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19500 raw19500Labels permutation346 hz
    mixedMoment B raw19500step0 raw19500step0Labels = mixedMoment B raw19500step1 raw19500step1Labels := by
      have ha : raw19500step1 = (fun i j => raw19500step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19500step1 raw19500step0; decide +kernel
      have hl : raw19500step1Labels = raw19500step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19500step0 raw19500step0Labels permutation40 permutation2
    _ = mixedMoment B node1202 node1202Labels := by rfl

def raw19501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw19501Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw19501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19501 raw19501Labels = mixedMoment B node1194 node1194Labels := by
  calc
    mixedMoment B raw19501 raw19501Labels = mixedMoment B raw19501step0 raw19501step0Labels := by
      have ha : raw19501step0 = (fun i j => raw19501 (permutation212 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19501step0 raw19501; decide +kernel
      have hl : raw19501step0Labels = raw19501Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19501 raw19501Labels permutation212 permutation2
    _ = mixedMoment B node1194 node1194Labels := by rfl

def raw19502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw19502Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![3, 0, -3]]
def raw19502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw19502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19502 raw19502Labels = mixedMoment B node1211 node1211Labels := by
  calc
    mixedMoment B raw19502 raw19502Labels = mixedMoment B raw19502step0 raw19502step0Labels := by
      have hz : ∀ j, raw19502 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19502step0 = (fun i j => raw19502 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19502step0 raw19502; decide +kernel
      have hl : raw19502step0Labels = raw19502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19502 raw19502Labels permutation346 hz
    mixedMoment B raw19502step0 raw19502step0Labels = mixedMoment B raw19502step1 raw19502step1Labels := by
      have ha : raw19502step1 = (fun i j => raw19502step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19502step1 raw19502step0; decide +kernel
      have hl : raw19502step1Labels = raw19502step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19502step0 raw19502step0Labels permutation44 permutation2
    _ = mixedMoment B node1211 node1211Labels := by rfl

def raw19503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw19503Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw19503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw19503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19503 raw19503Labels = mixedMoment B node1211 node1211Labels := by
  calc
    mixedMoment B raw19503 raw19503Labels = mixedMoment B raw19503step0 raw19503step0Labels := by
      have hz : ∀ j, raw19503 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19503step0 = (fun i j => raw19503 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19503step0 raw19503; decide +kernel
      have hl : raw19503step0Labels = raw19503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19503 raw19503Labels permutation346 hz
    mixedMoment B raw19503step0 raw19503step0Labels = mixedMoment B raw19503step1 raw19503step1Labels := by
      have ha : raw19503step1 = (fun i j => raw19503step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19503step1 raw19503step0; decide +kernel
      have hl : raw19503step1Labels = raw19503step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19503step0 raw19503step0Labels permutation38 permutation2
    _ = mixedMoment B node1211 node1211Labels := by rfl

def raw19504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19504Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19504step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19504step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19504step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19504step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![4, -2, -2]]
def raw19504step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19504step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19504step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19504step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19504step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19504 raw19504Labels = mixedMoment B node4187 node4187Labels := by
  calc
    mixedMoment B raw19504 raw19504Labels = mixedMoment B raw19504step0 raw19504step0Labels := by
      have hz : ∀ j, raw19504 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19504step0 = (fun i j => raw19504 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19504step0 raw19504; decide +kernel
      have hl : raw19504step0Labels = raw19504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19504 raw19504Labels permutation520 hz
    mixedMoment B raw19504step0 raw19504step0Labels = mixedMoment B raw19504step1 raw19504step1Labels := by
      have hz : ∀ j, raw19504step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19504step1 = (fun i j => raw19504step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19504step1 raw19504step0; decide +kernel
      have hl : raw19504step1Labels = raw19504step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19504step0 raw19504step0Labels permutation104 hz
    mixedMoment B raw19504step1 raw19504step1Labels = mixedMoment B raw19504step2 raw19504step2Labels := by
      have hz : ∀ j, raw19504step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19504step2 = (fun i j => raw19504step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19504step2 raw19504step1; decide +kernel
      have hl : raw19504step2Labels = raw19504step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19504step1 raw19504step1Labels permutation20 hz
    mixedMoment B raw19504step2 raw19504step2Labels = mixedMoment B raw19504step3 raw19504step3Labels := by
      have ha : raw19504step3 = (fun i j => raw19504step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19504step3 raw19504step2; decide +kernel
      have hl : raw19504step3Labels = raw19504step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19504step2 raw19504step2Labels permutation2 permutation3
    mixedMoment B raw19504step3 raw19504step3Labels = mixedMoment B raw19504step4 raw19504step4Labels := by
      have ha : raw19504step4 = raw19504step3 := by apply Matrix.ext; unfold raw19504step4 raw19504step3; decide +kernel
      have hl : raw19504step3Labels = labelEmbedding6 ∘ raw19504step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19504step3 raw19504step3Labels raw19504step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4187 node4187Labels := by rfl

def raw19505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19505Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19505step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19505step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19505step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19505step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19505step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19505step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19505 raw19505Labels = mixedMoment B node4555 node4555Labels := by
  calc
    mixedMoment B raw19505 raw19505Labels = mixedMoment B raw19505step0 raw19505step0Labels := by
      have hz : ∀ j, raw19505 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19505step0 = (fun i j => raw19505 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19505step0 raw19505; decide +kernel
      have hl : raw19505step0Labels = raw19505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19505 raw19505Labels permutation520 hz
    mixedMoment B raw19505step0 raw19505step0Labels = mixedMoment B raw19505step1 raw19505step1Labels := by
      have hz : ∀ j, raw19505step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19505step1 = (fun i j => raw19505step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19505step1 raw19505step0; decide +kernel
      have hl : raw19505step1Labels = raw19505step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19505step0 raw19505step0Labels permutation104 hz
    mixedMoment B raw19505step1 raw19505step1Labels = mixedMoment B raw19505step2 raw19505step2Labels := by
      have ha : raw19505step2 = (fun i j => raw19505step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19505step2 raw19505step1; decide +kernel
      have hl : raw19505step2Labels = raw19505step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19505step1 raw19505step1Labels permutation10 permutation3
    mixedMoment B raw19505step2 raw19505step2Labels = mixedMoment B raw19505step3 raw19505step3Labels := by
      have ha : raw19505step3 = raw19505step2 := by apply Matrix.ext; unfold raw19505step3 raw19505step2; decide +kernel
      have hl : raw19505step2Labels = labelEmbedding6 ∘ raw19505step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19505step2 raw19505step2Labels raw19505step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4555 node4555Labels := by rfl

def raw19506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19506Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19506step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19506step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19506step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19506step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19506step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19506step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19506step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19506 raw19506Labels = mixedMoment B node4555 node4555Labels := by
  calc
    mixedMoment B raw19506 raw19506Labels = mixedMoment B raw19506step0 raw19506step0Labels := by
      have hz : ∀ j, raw19506 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19506step0 = (fun i j => raw19506 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19506step0 raw19506; decide +kernel
      have hl : raw19506step0Labels = raw19506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19506 raw19506Labels permutation520 hz
    mixedMoment B raw19506step0 raw19506step0Labels = mixedMoment B raw19506step1 raw19506step1Labels := by
      have hz : ∀ j, raw19506step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19506step1 = (fun i j => raw19506step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19506step1 raw19506step0; decide +kernel
      have hl : raw19506step1Labels = raw19506step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19506step0 raw19506step0Labels permutation80 hz
    mixedMoment B raw19506step1 raw19506step1Labels = mixedMoment B raw19506step2 raw19506step2Labels := by
      have ha : raw19506step2 = (fun i j => raw19506step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19506step2 raw19506step1; decide +kernel
      have hl : raw19506step2Labels = raw19506step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19506step1 raw19506step1Labels permutation10 permutation3
    mixedMoment B raw19506step2 raw19506step2Labels = mixedMoment B raw19506step3 raw19506step3Labels := by
      have ha : raw19506step3 = raw19506step2 := by apply Matrix.ext; unfold raw19506step3 raw19506step2; decide +kernel
      have hl : raw19506step2Labels = labelEmbedding6 ∘ raw19506step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19506step2 raw19506step2Labels raw19506step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4555 node4555Labels := by rfl

def raw19507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19507Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19507step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19507step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19507step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19507step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19507step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19507step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19507step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19507 raw19507Labels = mixedMoment B node4555 node4555Labels := by
  calc
    mixedMoment B raw19507 raw19507Labels = mixedMoment B raw19507step0 raw19507step0Labels := by
      have hz : ∀ j, raw19507 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19507step0 = (fun i j => raw19507 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19507step0 raw19507; decide +kernel
      have hl : raw19507step0Labels = raw19507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19507 raw19507Labels permutation434 hz
    mixedMoment B raw19507step0 raw19507step0Labels = mixedMoment B raw19507step1 raw19507step1Labels := by
      have hz : ∀ j, raw19507step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19507step1 = (fun i j => raw19507step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19507step1 raw19507step0; decide +kernel
      have hl : raw19507step1Labels = raw19507step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19507step0 raw19507step0Labels permutation80 hz
    mixedMoment B raw19507step1 raw19507step1Labels = mixedMoment B raw19507step2 raw19507step2Labels := by
      have ha : raw19507step2 = (fun i j => raw19507step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19507step2 raw19507step1; decide +kernel
      have hl : raw19507step2Labels = raw19507step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19507step1 raw19507step1Labels permutation10 permutation3
    mixedMoment B raw19507step2 raw19507step2Labels = mixedMoment B raw19507step3 raw19507step3Labels := by
      have ha : raw19507step3 = raw19507step2 := by apply Matrix.ext; unfold raw19507step3 raw19507step2; decide +kernel
      have hl : raw19507step2Labels = labelEmbedding6 ∘ raw19507step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19507step2 raw19507step2Labels raw19507step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4555 node4555Labels := by rfl

def raw19508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19508Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19508step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19508step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19508step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19508step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![4, -2, -2]]
def raw19508step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19508step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19508step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19508step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19508step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19508 raw19508Labels = mixedMoment B node4187 node4187Labels := by
  calc
    mixedMoment B raw19508 raw19508Labels = mixedMoment B raw19508step0 raw19508step0Labels := by
      have hz : ∀ j, raw19508 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19508step0 = (fun i j => raw19508 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19508step0 raw19508; decide +kernel
      have hl : raw19508step0Labels = raw19508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19508 raw19508Labels permutation520 hz
    mixedMoment B raw19508step0 raw19508step0Labels = mixedMoment B raw19508step1 raw19508step1Labels := by
      have hz : ∀ j, raw19508step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19508step1 = (fun i j => raw19508step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19508step1 raw19508step0; decide +kernel
      have hl : raw19508step1Labels = raw19508step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19508step0 raw19508step0Labels permutation104 hz
    mixedMoment B raw19508step1 raw19508step1Labels = mixedMoment B raw19508step2 raw19508step2Labels := by
      have hz : ∀ j, raw19508step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19508step2 = (fun i j => raw19508step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19508step2 raw19508step1; decide +kernel
      have hl : raw19508step2Labels = raw19508step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19508step1 raw19508step1Labels permutation14 hz
    mixedMoment B raw19508step2 raw19508step2Labels = mixedMoment B raw19508step3 raw19508step3Labels := by
      have ha : raw19508step3 = (fun i j => raw19508step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19508step3 raw19508step2; decide +kernel
      have hl : raw19508step3Labels = raw19508step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19508step2 raw19508step2Labels permutation2 permutation3
    mixedMoment B raw19508step3 raw19508step3Labels = mixedMoment B raw19508step4 raw19508step4Labels := by
      have ha : raw19508step4 = raw19508step3 := by apply Matrix.ext; unfold raw19508step4 raw19508step3; decide +kernel
      have hl : raw19508step3Labels = labelEmbedding6 ∘ raw19508step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19508step3 raw19508step3Labels raw19508step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4187 node4187Labels := by rfl

def raw19509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19509Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19509step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19509step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19509step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19509step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19509step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19509step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19509step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19509 raw19509Labels = mixedMoment B node4555 node4555Labels := by
  calc
    mixedMoment B raw19509 raw19509Labels = mixedMoment B raw19509step0 raw19509step0Labels := by
      have hz : ∀ j, raw19509 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19509step0 = (fun i j => raw19509 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19509step0 raw19509; decide +kernel
      have hl : raw19509step0Labels = raw19509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19509 raw19509Labels permutation520 hz
    mixedMoment B raw19509step0 raw19509step0Labels = mixedMoment B raw19509step1 raw19509step1Labels := by
      have hz : ∀ j, raw19509step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19509step1 = (fun i j => raw19509step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19509step1 raw19509step0; decide +kernel
      have hl : raw19509step1Labels = raw19509step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19509step0 raw19509step0Labels permutation104 hz
    mixedMoment B raw19509step1 raw19509step1Labels = mixedMoment B raw19509step2 raw19509step2Labels := by
      have ha : raw19509step2 = (fun i j => raw19509step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19509step2 raw19509step1; decide +kernel
      have hl : raw19509step2Labels = raw19509step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19509step1 raw19509step1Labels permutation8 permutation3
    mixedMoment B raw19509step2 raw19509step2Labels = mixedMoment B raw19509step3 raw19509step3Labels := by
      have ha : raw19509step3 = raw19509step2 := by apply Matrix.ext; unfold raw19509step3 raw19509step2; decide +kernel
      have hl : raw19509step2Labels = labelEmbedding6 ∘ raw19509step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19509step2 raw19509step2Labels raw19509step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4555 node4555Labels := by rfl

def raw19510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19510Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19510step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19510step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19510step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19510step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19510step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19510step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19510step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19510 raw19510Labels = mixedMoment B node4555 node4555Labels := by
  calc
    mixedMoment B raw19510 raw19510Labels = mixedMoment B raw19510step0 raw19510step0Labels := by
      have hz : ∀ j, raw19510 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19510step0 = (fun i j => raw19510 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19510step0 raw19510; decide +kernel
      have hl : raw19510step0Labels = raw19510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19510 raw19510Labels permutation520 hz
    mixedMoment B raw19510step0 raw19510step0Labels = mixedMoment B raw19510step1 raw19510step1Labels := by
      have hz : ∀ j, raw19510step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19510step1 = (fun i j => raw19510step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19510step1 raw19510step0; decide +kernel
      have hl : raw19510step1Labels = raw19510step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19510step0 raw19510step0Labels permutation56 hz
    mixedMoment B raw19510step1 raw19510step1Labels = mixedMoment B raw19510step2 raw19510step2Labels := by
      have ha : raw19510step2 = (fun i j => raw19510step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19510step2 raw19510step1; decide +kernel
      have hl : raw19510step2Labels = raw19510step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19510step1 raw19510step1Labels permutation10 permutation3
    mixedMoment B raw19510step2 raw19510step2Labels = mixedMoment B raw19510step3 raw19510step3Labels := by
      have ha : raw19510step3 = raw19510step2 := by apply Matrix.ext; unfold raw19510step3 raw19510step2; decide +kernel
      have hl : raw19510step2Labels = labelEmbedding6 ∘ raw19510step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19510step2 raw19510step2Labels raw19510step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4555 node4555Labels := by rfl

def raw19511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19511Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19511step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19511step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19511step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19511step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19511step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19511step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19511step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19511 raw19511Labels = mixedMoment B node4555 node4555Labels := by
  calc
    mixedMoment B raw19511 raw19511Labels = mixedMoment B raw19511step0 raw19511step0Labels := by
      have hz : ∀ j, raw19511 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19511step0 = (fun i j => raw19511 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19511step0 raw19511; decide +kernel
      have hl : raw19511step0Labels = raw19511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19511 raw19511Labels permutation434 hz
    mixedMoment B raw19511step0 raw19511step0Labels = mixedMoment B raw19511step1 raw19511step1Labels := by
      have hz : ∀ j, raw19511step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19511step1 = (fun i j => raw19511step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19511step1 raw19511step0; decide +kernel
      have hl : raw19511step1Labels = raw19511step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19511step0 raw19511step0Labels permutation56 hz
    mixedMoment B raw19511step1 raw19511step1Labels = mixedMoment B raw19511step2 raw19511step2Labels := by
      have ha : raw19511step2 = (fun i j => raw19511step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19511step2 raw19511step1; decide +kernel
      have hl : raw19511step2Labels = raw19511step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19511step1 raw19511step1Labels permutation10 permutation3
    mixedMoment B raw19511step2 raw19511step2Labels = mixedMoment B raw19511step3 raw19511step3Labels := by
      have ha : raw19511step3 = raw19511step2 := by apply Matrix.ext; unfold raw19511step3 raw19511step2; decide +kernel
      have hl : raw19511step2Labels = labelEmbedding6 ∘ raw19511step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19511step2 raw19511step2Labels raw19511step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4555 node4555Labels := by rfl

def raw19512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19512Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19512step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19512step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19512step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19512step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![4, -2, -2]]
def raw19512step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19512step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19512step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19512step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19512step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19512 raw19512Labels = mixedMoment B node4187 node4187Labels := by
  calc
    mixedMoment B raw19512 raw19512Labels = mixedMoment B raw19512step0 raw19512step0Labels := by
      have hz : ∀ j, raw19512 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19512step0 = (fun i j => raw19512 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19512step0 raw19512; decide +kernel
      have hl : raw19512step0Labels = raw19512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19512 raw19512Labels permutation520 hz
    mixedMoment B raw19512step0 raw19512step0Labels = mixedMoment B raw19512step1 raw19512step1Labels := by
      have hz : ∀ j, raw19512step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19512step1 = (fun i j => raw19512step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19512step1 raw19512step0; decide +kernel
      have hl : raw19512step1Labels = raw19512step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19512step0 raw19512step0Labels permutation80 hz
    mixedMoment B raw19512step1 raw19512step1Labels = mixedMoment B raw19512step2 raw19512step2Labels := by
      have hz : ∀ j, raw19512step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19512step2 = (fun i j => raw19512step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19512step2 raw19512step1; decide +kernel
      have hl : raw19512step2Labels = raw19512step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19512step1 raw19512step1Labels permutation14 hz
    mixedMoment B raw19512step2 raw19512step2Labels = mixedMoment B raw19512step3 raw19512step3Labels := by
      have ha : raw19512step3 = (fun i j => raw19512step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19512step3 raw19512step2; decide +kernel
      have hl : raw19512step3Labels = raw19512step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19512step2 raw19512step2Labels permutation2 permutation3
    mixedMoment B raw19512step3 raw19512step3Labels = mixedMoment B raw19512step4 raw19512step4Labels := by
      have ha : raw19512step4 = raw19512step3 := by apply Matrix.ext; unfold raw19512step4 raw19512step3; decide +kernel
      have hl : raw19512step3Labels = labelEmbedding6 ∘ raw19512step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19512step3 raw19512step3Labels raw19512step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4187 node4187Labels := by rfl

def raw19513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19513Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19513step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19513step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19513step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19513step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19513step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19513step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19513 raw19513Labels = mixedMoment B node4555 node4555Labels := by
  calc
    mixedMoment B raw19513 raw19513Labels = mixedMoment B raw19513step0 raw19513step0Labels := by
      have hz : ∀ j, raw19513 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19513step0 = (fun i j => raw19513 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19513step0 raw19513; decide +kernel
      have hl : raw19513step0Labels = raw19513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19513 raw19513Labels permutation520 hz
    mixedMoment B raw19513step0 raw19513step0Labels = mixedMoment B raw19513step1 raw19513step1Labels := by
      have hz : ∀ j, raw19513step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19513step1 = (fun i j => raw19513step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19513step1 raw19513step0; decide +kernel
      have hl : raw19513step1Labels = raw19513step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19513step0 raw19513step0Labels permutation80 hz
    mixedMoment B raw19513step1 raw19513step1Labels = mixedMoment B raw19513step2 raw19513step2Labels := by
      have ha : raw19513step2 = (fun i j => raw19513step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19513step2 raw19513step1; decide +kernel
      have hl : raw19513step2Labels = raw19513step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19513step1 raw19513step1Labels permutation8 permutation3
    mixedMoment B raw19513step2 raw19513step2Labels = mixedMoment B raw19513step3 raw19513step3Labels := by
      have ha : raw19513step3 = raw19513step2 := by apply Matrix.ext; unfold raw19513step3 raw19513step2; decide +kernel
      have hl : raw19513step2Labels = labelEmbedding6 ∘ raw19513step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19513step2 raw19513step2Labels raw19513step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4555 node4555Labels := by rfl

def raw19514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19514Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19514step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19514step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19514step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19514step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19514step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19514step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19514 raw19514Labels = mixedMoment B node4555 node4555Labels := by
  calc
    mixedMoment B raw19514 raw19514Labels = mixedMoment B raw19514step0 raw19514step0Labels := by
      have hz : ∀ j, raw19514 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19514step0 = (fun i j => raw19514 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19514step0 raw19514; decide +kernel
      have hl : raw19514step0Labels = raw19514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19514 raw19514Labels permutation520 hz
    mixedMoment B raw19514step0 raw19514step0Labels = mixedMoment B raw19514step1 raw19514step1Labels := by
      have hz : ∀ j, raw19514step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19514step1 = (fun i j => raw19514step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19514step1 raw19514step0; decide +kernel
      have hl : raw19514step1Labels = raw19514step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19514step0 raw19514step0Labels permutation56 hz
    mixedMoment B raw19514step1 raw19514step1Labels = mixedMoment B raw19514step2 raw19514step2Labels := by
      have ha : raw19514step2 = (fun i j => raw19514step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19514step2 raw19514step1; decide +kernel
      have hl : raw19514step2Labels = raw19514step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19514step1 raw19514step1Labels permutation8 permutation3
    mixedMoment B raw19514step2 raw19514step2Labels = mixedMoment B raw19514step3 raw19514step3Labels := by
      have ha : raw19514step3 = raw19514step2 := by apply Matrix.ext; unfold raw19514step3 raw19514step2; decide +kernel
      have hl : raw19514step2Labels = labelEmbedding6 ∘ raw19514step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19514step2 raw19514step2Labels raw19514step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4555 node4555Labels := by rfl

def raw19515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19515Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19515step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19515step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19515step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19515step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19515step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19515step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19515 raw19515Labels = mixedMoment B node4555 node4555Labels := by
  calc
    mixedMoment B raw19515 raw19515Labels = mixedMoment B raw19515step0 raw19515step0Labels := by
      have hz : ∀ j, raw19515 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19515step0 = (fun i j => raw19515 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19515step0 raw19515; decide +kernel
      have hl : raw19515step0Labels = raw19515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19515 raw19515Labels permutation346 hz
    mixedMoment B raw19515step0 raw19515step0Labels = mixedMoment B raw19515step1 raw19515step1Labels := by
      have hz : ∀ j, raw19515step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19515step1 = (fun i j => raw19515step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19515step1 raw19515step0; decide +kernel
      have hl : raw19515step1Labels = raw19515step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19515step0 raw19515step0Labels permutation56 hz
    mixedMoment B raw19515step1 raw19515step1Labels = mixedMoment B raw19515step2 raw19515step2Labels := by
      have ha : raw19515step2 = (fun i j => raw19515step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19515step2 raw19515step1; decide +kernel
      have hl : raw19515step2Labels = raw19515step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19515step1 raw19515step1Labels permutation10 permutation3
    mixedMoment B raw19515step2 raw19515step2Labels = mixedMoment B raw19515step3 raw19515step3Labels := by
      have ha : raw19515step3 = raw19515step2 := by apply Matrix.ext; unfold raw19515step3 raw19515step2; decide +kernel
      have hl : raw19515step2Labels = labelEmbedding6 ∘ raw19515step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19515step2 raw19515step2Labels raw19515step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4555 node4555Labels := by rfl

def raw19516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19516Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19516step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19516step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19516step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![4, -2, -2]]
def raw19516step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19516step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19516step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19516step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19516step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19516 raw19516Labels = mixedMoment B node4187 node4187Labels := by
  calc
    mixedMoment B raw19516 raw19516Labels = mixedMoment B raw19516step0 raw19516step0Labels := by
      have hz : ∀ j, raw19516 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19516step0 = (fun i j => raw19516 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19516step0 raw19516; decide +kernel
      have hl : raw19516step0Labels = raw19516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19516 raw19516Labels permutation434 hz
    mixedMoment B raw19516step0 raw19516step0Labels = mixedMoment B raw19516step1 raw19516step1Labels := by
      have hz : ∀ j, raw19516step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19516step1 = (fun i j => raw19516step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19516step1 raw19516step0; decide +kernel
      have hl : raw19516step1Labels = raw19516step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19516step0 raw19516step0Labels permutation80 hz
    mixedMoment B raw19516step1 raw19516step1Labels = mixedMoment B raw19516step2 raw19516step2Labels := by
      have hz : ∀ j, raw19516step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19516step2 = (fun i j => raw19516step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19516step2 raw19516step1; decide +kernel
      have hl : raw19516step2Labels = raw19516step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19516step1 raw19516step1Labels permutation14 hz
    mixedMoment B raw19516step2 raw19516step2Labels = mixedMoment B raw19516step3 raw19516step3Labels := by
      have ha : raw19516step3 = (fun i j => raw19516step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19516step3 raw19516step2; decide +kernel
      have hl : raw19516step3Labels = raw19516step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19516step2 raw19516step2Labels permutation2 permutation3
    mixedMoment B raw19516step3 raw19516step3Labels = mixedMoment B raw19516step4 raw19516step4Labels := by
      have ha : raw19516step4 = raw19516step3 := by apply Matrix.ext; unfold raw19516step4 raw19516step3; decide +kernel
      have hl : raw19516step3Labels = labelEmbedding6 ∘ raw19516step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19516step3 raw19516step3Labels raw19516step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4187 node4187Labels := by rfl

def raw19517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19517Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19517step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19517step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19517step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19517step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19517step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19517step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19517step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19517 raw19517Labels = mixedMoment B node4555 node4555Labels := by
  calc
    mixedMoment B raw19517 raw19517Labels = mixedMoment B raw19517step0 raw19517step0Labels := by
      have hz : ∀ j, raw19517 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19517step0 = (fun i j => raw19517 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19517step0 raw19517; decide +kernel
      have hl : raw19517step0Labels = raw19517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19517 raw19517Labels permutation434 hz
    mixedMoment B raw19517step0 raw19517step0Labels = mixedMoment B raw19517step1 raw19517step1Labels := by
      have hz : ∀ j, raw19517step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19517step1 = (fun i j => raw19517step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19517step1 raw19517step0; decide +kernel
      have hl : raw19517step1Labels = raw19517step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19517step0 raw19517step0Labels permutation80 hz
    mixedMoment B raw19517step1 raw19517step1Labels = mixedMoment B raw19517step2 raw19517step2Labels := by
      have ha : raw19517step2 = (fun i j => raw19517step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19517step2 raw19517step1; decide +kernel
      have hl : raw19517step2Labels = raw19517step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19517step1 raw19517step1Labels permutation8 permutation3
    mixedMoment B raw19517step2 raw19517step2Labels = mixedMoment B raw19517step3 raw19517step3Labels := by
      have ha : raw19517step3 = raw19517step2 := by apply Matrix.ext; unfold raw19517step3 raw19517step2; decide +kernel
      have hl : raw19517step2Labels = labelEmbedding6 ∘ raw19517step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19517step2 raw19517step2Labels raw19517step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4555 node4555Labels := by rfl

def raw19518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19518step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19518step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19518step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19518step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19518step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19518step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19518step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19518 raw19518Labels = mixedMoment B node4555 node4555Labels := by
  calc
    mixedMoment B raw19518 raw19518Labels = mixedMoment B raw19518step0 raw19518step0Labels := by
      have hz : ∀ j, raw19518 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19518step0 = (fun i j => raw19518 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19518step0 raw19518; decide +kernel
      have hl : raw19518step0Labels = raw19518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19518 raw19518Labels permutation434 hz
    mixedMoment B raw19518step0 raw19518step0Labels = mixedMoment B raw19518step1 raw19518step1Labels := by
      have hz : ∀ j, raw19518step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19518step1 = (fun i j => raw19518step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19518step1 raw19518step0; decide +kernel
      have hl : raw19518step1Labels = raw19518step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19518step0 raw19518step0Labels permutation56 hz
    mixedMoment B raw19518step1 raw19518step1Labels = mixedMoment B raw19518step2 raw19518step2Labels := by
      have ha : raw19518step2 = (fun i j => raw19518step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19518step2 raw19518step1; decide +kernel
      have hl : raw19518step2Labels = raw19518step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19518step1 raw19518step1Labels permutation8 permutation3
    mixedMoment B raw19518step2 raw19518step2Labels = mixedMoment B raw19518step3 raw19518step3Labels := by
      have ha : raw19518step3 = raw19518step2 := by apply Matrix.ext; unfold raw19518step3 raw19518step2; decide +kernel
      have hl : raw19518step2Labels = labelEmbedding6 ∘ raw19518step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19518step2 raw19518step2Labels raw19518step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4555 node4555Labels := by rfl

def raw19519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19519Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19519step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19519step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19519step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19519step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19519step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19519step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19519 raw19519Labels = mixedMoment B node4555 node4555Labels := by
  calc
    mixedMoment B raw19519 raw19519Labels = mixedMoment B raw19519step0 raw19519step0Labels := by
      have hz : ∀ j, raw19519 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19519step0 = (fun i j => raw19519 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19519step0 raw19519; decide +kernel
      have hl : raw19519step0Labels = raw19519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19519 raw19519Labels permutation346 hz
    mixedMoment B raw19519step0 raw19519step0Labels = mixedMoment B raw19519step1 raw19519step1Labels := by
      have hz : ∀ j, raw19519step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19519step1 = (fun i j => raw19519step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19519step1 raw19519step0; decide +kernel
      have hl : raw19519step1Labels = raw19519step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19519step0 raw19519step0Labels permutation56 hz
    mixedMoment B raw19519step1 raw19519step1Labels = mixedMoment B raw19519step2 raw19519step2Labels := by
      have ha : raw19519step2 = (fun i j => raw19519step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19519step2 raw19519step1; decide +kernel
      have hl : raw19519step2Labels = raw19519step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19519step1 raw19519step1Labels permutation8 permutation3
    mixedMoment B raw19519step2 raw19519step2Labels = mixedMoment B raw19519step3 raw19519step3Labels := by
      have ha : raw19519step3 = raw19519step2 := by apply Matrix.ext; unfold raw19519step3 raw19519step2; decide +kernel
      have hl : raw19519step2Labels = labelEmbedding6 ∘ raw19519step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19519step2 raw19519step2Labels raw19519step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4555 node4555Labels := by rfl

def raw19520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19520step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19520step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19520step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![5, -3, -2]]
def raw19520step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19520step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 3, 2], ![5, -3, -2]]
def raw19520step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19520step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def raw19520step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19520step5 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def raw19520step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19520 raw19520Labels = mixedMoment B node4194 node4194Labels := by
  calc
    mixedMoment B raw19520 raw19520Labels = mixedMoment B raw19520step0 raw19520step0Labels := by
      have hz : ∀ j, raw19520 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19520step0 = (fun i j => raw19520 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19520step0 raw19520; decide +kernel
      have hl : raw19520step0Labels = raw19520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19520 raw19520Labels permutation520 hz
    mixedMoment B raw19520step0 raw19520step0Labels = mixedMoment B raw19520step1 raw19520step1Labels := by
      have hz : ∀ j, raw19520step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19520step1 = (fun i j => raw19520step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19520step1 raw19520step0; decide +kernel
      have hl : raw19520step1Labels = raw19520step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19520step0 raw19520step0Labels permutation104 hz
    mixedMoment B raw19520step1 raw19520step1Labels = mixedMoment B raw19520step2 raw19520step2Labels := by
      have hz : ∀ j, raw19520step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19520step2 = (fun i j => raw19520step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19520step2 raw19520step1; decide +kernel
      have hl : raw19520step2Labels = raw19520step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19520step1 raw19520step1Labels permutation20 hz
    mixedMoment B raw19520step2 raw19520step2Labels = mixedMoment B raw19520step3 raw19520step3Labels := by
      have hz : ∀ j, raw19520step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19520step3 = (fun i j => raw19520step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19520step3 raw19520step2; decide +kernel
      have hl : raw19520step3Labels = raw19520step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19520step2 raw19520step2Labels permutation4 hz
    mixedMoment B raw19520step3 raw19520step3Labels = mixedMoment B raw19520step4 raw19520step4Labels := by
      have ha : raw19520step4 = (fun i j => raw19520step3 (permutation0 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19520step4 raw19520step3; decide +kernel
      have hl : raw19520step4Labels = raw19520step3Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19520step3 raw19520step3Labels permutation0 permutation3
    mixedMoment B raw19520step4 raw19520step4Labels = mixedMoment B raw19520step5 raw19520step5Labels := by
      have ha : raw19520step5 = raw19520step4 := by apply Matrix.ext; unfold raw19520step5 raw19520step4; decide +kernel
      have hl : raw19520step4Labels = labelEmbedding6 ∘ raw19520step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19520step4 raw19520step4Labels raw19520step5Labels labelEmbedding6 hl
    _ = mixedMoment B node4194 node4194Labels := by rfl

def raw19521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19521step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19521step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19521step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19521step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![5, -3, -2]]
def raw19521step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19521step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-4, 2, 2]]
def raw19521step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19521step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19521step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19521step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19521step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19521 raw19521Labels = mixedMoment B node4187 node4187Labels := by
  calc
    mixedMoment B raw19521 raw19521Labels = mixedMoment B raw19521step0 raw19521step0Labels := by
      have hz : ∀ j, raw19521 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19521step0 = (fun i j => raw19521 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19521step0 raw19521; decide +kernel
      have hl : raw19521step0Labels = raw19521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19521 raw19521Labels permutation520 hz
    mixedMoment B raw19521step0 raw19521step0Labels = mixedMoment B raw19521step1 raw19521step1Labels := by
      have hz : ∀ j, raw19521step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19521step1 = (fun i j => raw19521step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19521step1 raw19521step0; decide +kernel
      have hl : raw19521step1Labels = raw19521step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19521step0 raw19521step0Labels permutation104 hz
    mixedMoment B raw19521step1 raw19521step1Labels = mixedMoment B raw19521step2 raw19521step2Labels := by
      have hz : ∀ j, raw19521step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19521step2 = (fun i j => raw19521step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19521step2 raw19521step1; decide +kernel
      have hl : raw19521step2Labels = raw19521step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19521step1 raw19521step1Labels permutation20 hz
    mixedMoment B raw19521step2 raw19521step2Labels = mixedMoment B raw19521step3 raw19521step3Labels := by
      have ha : raw19521step3 = (fun i j => raw19521step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19521step3 raw19521step2; decide +kernel
      have hl : raw19521step3Labels = raw19521step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19521step2 raw19521step2Labels permutation7 permutation3
    mixedMoment B raw19521step3 raw19521step3Labels = mixedMoment B raw19521step4 raw19521step4Labels := by
      have ha : raw19521step4 = -raw19521step3 := by apply Matrix.ext; change ∀ i j, raw19521step4 i j = -(raw19521step3 i j); unfold raw19521step4 raw19521step3; decide +kernel
      have hl : raw19521step4Labels = raw19521step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19521step4 raw19521step4Labels = mixedMoment B raw19521step5 raw19521step5Labels := by
      have ha : raw19521step5 = raw19521step4 := by apply Matrix.ext; unfold raw19521step5 raw19521step4; decide +kernel
      have hl : raw19521step4Labels = labelEmbedding6 ∘ raw19521step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19521step4 raw19521step4Labels raw19521step5Labels labelEmbedding6 hl
    _ = mixedMoment B node4187 node4187Labels := by rfl

def raw19522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19522step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![5, -3, -2]]
def raw19522step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19522step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![5, -3, -2]]
def raw19522step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19522step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-4, 2, 2]]
def raw19522step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19522step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19522step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19522step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19522step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19522 raw19522Labels = mixedMoment B node4187 node4187Labels := by
  calc
    mixedMoment B raw19522 raw19522Labels = mixedMoment B raw19522step0 raw19522step0Labels := by
      have hz : ∀ j, raw19522 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19522step0 = (fun i j => raw19522 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19522step0 raw19522; decide +kernel
      have hl : raw19522step0Labels = raw19522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19522 raw19522Labels permutation520 hz
    mixedMoment B raw19522step0 raw19522step0Labels = mixedMoment B raw19522step1 raw19522step1Labels := by
      have hz : ∀ j, raw19522step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19522step1 = (fun i j => raw19522step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19522step1 raw19522step0; decide +kernel
      have hl : raw19522step1Labels = raw19522step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19522step0 raw19522step0Labels permutation104 hz
    mixedMoment B raw19522step1 raw19522step1Labels = mixedMoment B raw19522step2 raw19522step2Labels := by
      have hz : ∀ j, raw19522step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19522step2 = (fun i j => raw19522step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19522step2 raw19522step1; decide +kernel
      have hl : raw19522step2Labels = raw19522step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19522step1 raw19522step1Labels permutation14 hz
    mixedMoment B raw19522step2 raw19522step2Labels = mixedMoment B raw19522step3 raw19522step3Labels := by
      have ha : raw19522step3 = (fun i j => raw19522step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19522step3 raw19522step2; decide +kernel
      have hl : raw19522step3Labels = raw19522step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19522step2 raw19522step2Labels permutation7 permutation3
    mixedMoment B raw19522step3 raw19522step3Labels = mixedMoment B raw19522step4 raw19522step4Labels := by
      have ha : raw19522step4 = -raw19522step3 := by apply Matrix.ext; change ∀ i j, raw19522step4 i j = -(raw19522step3 i j); unfold raw19522step4 raw19522step3; decide +kernel
      have hl : raw19522step4Labels = raw19522step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19522step4 raw19522step4Labels = mixedMoment B raw19522step5 raw19522step5Labels := by
      have ha : raw19522step5 = raw19522step4 := by apply Matrix.ext; unfold raw19522step5 raw19522step4; decide +kernel
      have hl : raw19522step4Labels = labelEmbedding6 ∘ raw19522step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19522step4 raw19522step4Labels raw19522step5Labels labelEmbedding6 hl
    _ = mixedMoment B node4187 node4187Labels := by rfl

def raw19523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -3, -2]]
def raw19523step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![5, -3, -2]]
def raw19523step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19523step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![5, -3, -2]]
def raw19523step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19523step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-4, 2, 2]]
def raw19523step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19523step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19523step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19523step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19523step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19523 raw19523Labels = mixedMoment B node4187 node4187Labels := by
  calc
    mixedMoment B raw19523 raw19523Labels = mixedMoment B raw19523step0 raw19523step0Labels := by
      have hz : ∀ j, raw19523 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19523step0 = (fun i j => raw19523 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19523step0 raw19523; decide +kernel
      have hl : raw19523step0Labels = raw19523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19523 raw19523Labels permutation520 hz
    mixedMoment B raw19523step0 raw19523step0Labels = mixedMoment B raw19523step1 raw19523step1Labels := by
      have hz : ∀ j, raw19523step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19523step1 = (fun i j => raw19523step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19523step1 raw19523step0; decide +kernel
      have hl : raw19523step1Labels = raw19523step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19523step0 raw19523step0Labels permutation80 hz
    mixedMoment B raw19523step1 raw19523step1Labels = mixedMoment B raw19523step2 raw19523step2Labels := by
      have hz : ∀ j, raw19523step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19523step2 = (fun i j => raw19523step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19523step2 raw19523step1; decide +kernel
      have hl : raw19523step2Labels = raw19523step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19523step1 raw19523step1Labels permutation14 hz
    mixedMoment B raw19523step2 raw19523step2Labels = mixedMoment B raw19523step3 raw19523step3Labels := by
      have ha : raw19523step3 = (fun i j => raw19523step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19523step3 raw19523step2; decide +kernel
      have hl : raw19523step3Labels = raw19523step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19523step2 raw19523step2Labels permutation7 permutation3
    mixedMoment B raw19523step3 raw19523step3Labels = mixedMoment B raw19523step4 raw19523step4Labels := by
      have ha : raw19523step4 = -raw19523step3 := by apply Matrix.ext; change ∀ i j, raw19523step4 i j = -(raw19523step3 i j); unfold raw19523step4 raw19523step3; decide +kernel
      have hl : raw19523step4Labels = raw19523step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19523step4 raw19523step4Labels = mixedMoment B raw19523step5 raw19523step5Labels := by
      have ha : raw19523step5 = raw19523step4 := by apply Matrix.ext; unfold raw19523step5 raw19523step4; decide +kernel
      have hl : raw19523step4Labels = labelEmbedding6 ∘ raw19523step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19523step4 raw19523step4Labels raw19523step5Labels labelEmbedding6 hl
    _ = mixedMoment B node4187 node4187Labels := by rfl

def raw19524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -3, -2]]
def raw19524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -3, -2]]
def raw19524step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19524step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![5, -3, -2]]
def raw19524step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19524step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![5, -3, -2]]
def raw19524step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19524step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-4, 2, 2]]
def raw19524step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19524step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19524step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19524step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19524step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19524 raw19524Labels = mixedMoment B node4187 node4187Labels := by
  calc
    mixedMoment B raw19524 raw19524Labels = mixedMoment B raw19524step0 raw19524step0Labels := by
      have hz : ∀ j, raw19524 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19524step0 = (fun i j => raw19524 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19524step0 raw19524; decide +kernel
      have hl : raw19524step0Labels = raw19524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19524 raw19524Labels permutation434 hz
    mixedMoment B raw19524step0 raw19524step0Labels = mixedMoment B raw19524step1 raw19524step1Labels := by
      have hz : ∀ j, raw19524step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19524step1 = (fun i j => raw19524step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19524step1 raw19524step0; decide +kernel
      have hl : raw19524step1Labels = raw19524step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19524step0 raw19524step0Labels permutation80 hz
    mixedMoment B raw19524step1 raw19524step1Labels = mixedMoment B raw19524step2 raw19524step2Labels := by
      have hz : ∀ j, raw19524step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19524step2 = (fun i j => raw19524step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19524step2 raw19524step1; decide +kernel
      have hl : raw19524step2Labels = raw19524step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19524step1 raw19524step1Labels permutation14 hz
    mixedMoment B raw19524step2 raw19524step2Labels = mixedMoment B raw19524step3 raw19524step3Labels := by
      have ha : raw19524step3 = (fun i j => raw19524step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19524step3 raw19524step2; decide +kernel
      have hl : raw19524step3Labels = raw19524step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19524step2 raw19524step2Labels permutation7 permutation3
    mixedMoment B raw19524step3 raw19524step3Labels = mixedMoment B raw19524step4 raw19524step4Labels := by
      have ha : raw19524step4 = -raw19524step3 := by apply Matrix.ext; change ∀ i j, raw19524step4 i j = -(raw19524step3 i j); unfold raw19524step4 raw19524step3; decide +kernel
      have hl : raw19524step4Labels = raw19524step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19524step4 raw19524step4Labels = mixedMoment B raw19524step5 raw19524step5Labels := by
      have ha : raw19524step5 = raw19524step4 := by apply Matrix.ext; unfold raw19524step5 raw19524step4; decide +kernel
      have hl : raw19524step4Labels = labelEmbedding6 ∘ raw19524step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19524step4 raw19524step4Labels raw19524step5Labels labelEmbedding6 hl
    _ = mixedMoment B node4187 node4187Labels := by rfl

def raw19525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19525Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19525step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19525step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19525step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![4, -2, -2]]
def raw19525step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19525step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 0, 1], ![-3, 2, 1]]
def raw19525step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19525step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw19525step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19525 raw19525Labels = mixedMoment B node1307 node1307Labels := by
  calc
    mixedMoment B raw19525 raw19525Labels = mixedMoment B raw19525step0 raw19525step0Labels := by
      have hz : ∀ j, raw19525 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19525step0 = (fun i j => raw19525 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19525step0 raw19525; decide +kernel
      have hl : raw19525step0Labels = raw19525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19525 raw19525Labels permutation520 hz
    mixedMoment B raw19525step0 raw19525step0Labels = mixedMoment B raw19525step1 raw19525step1Labels := by
      have hz : ∀ j, raw19525step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19525step1 = (fun i j => raw19525step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19525step1 raw19525step0; decide +kernel
      have hl : raw19525step1Labels = raw19525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19525step0 raw19525step0Labels permutation104 hz
    mixedMoment B raw19525step1 raw19525step1Labels = mixedMoment B raw19525step2 raw19525step2Labels := by
      have hz : ∀ j, raw19525step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19525step2 = (fun i j => raw19525step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19525step2 raw19525step1; decide +kernel
      have hl : raw19525step2Labels = raw19525step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19525step1 raw19525step1Labels permutation20 hz
    mixedMoment B raw19525step2 raw19525step2Labels = mixedMoment B raw19525step3 raw19525step3Labels := by
      have ha : raw19525step3 = (fun i j => raw19525step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19525step3 raw19525step2; decide +kernel
      have hl : raw19525step3Labels = raw19525step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19525step2 raw19525step2Labels permutation7 permutation3
    mixedMoment B raw19525step3 raw19525step3Labels = mixedMoment B raw19525step4 raw19525step4Labels := by
      have ha : raw19525step4 = -raw19525step3 := by apply Matrix.ext; change ∀ i j, raw19525step4 i j = -(raw19525step3 i j); unfold raw19525step4 raw19525step3; decide +kernel
      have hl : raw19525step4Labels = raw19525step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1307 node1307Labels := by rfl

def raw19526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19526Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19526step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19526step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19526step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![4, -2, -2]]
def raw19526step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19526step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 0, 1], ![-3, 2, 1]]
def raw19526step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19526step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw19526step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19526 raw19526Labels = mixedMoment B node1307 node1307Labels := by
  calc
    mixedMoment B raw19526 raw19526Labels = mixedMoment B raw19526step0 raw19526step0Labels := by
      have hz : ∀ j, raw19526 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19526step0 = (fun i j => raw19526 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19526step0 raw19526; decide +kernel
      have hl : raw19526step0Labels = raw19526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19526 raw19526Labels permutation520 hz
    mixedMoment B raw19526step0 raw19526step0Labels = mixedMoment B raw19526step1 raw19526step1Labels := by
      have hz : ∀ j, raw19526step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19526step1 = (fun i j => raw19526step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19526step1 raw19526step0; decide +kernel
      have hl : raw19526step1Labels = raw19526step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19526step0 raw19526step0Labels permutation104 hz
    mixedMoment B raw19526step1 raw19526step1Labels = mixedMoment B raw19526step2 raw19526step2Labels := by
      have hz : ∀ j, raw19526step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19526step2 = (fun i j => raw19526step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19526step2 raw19526step1; decide +kernel
      have hl : raw19526step2Labels = raw19526step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19526step1 raw19526step1Labels permutation14 hz
    mixedMoment B raw19526step2 raw19526step2Labels = mixedMoment B raw19526step3 raw19526step3Labels := by
      have ha : raw19526step3 = (fun i j => raw19526step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19526step3 raw19526step2; decide +kernel
      have hl : raw19526step3Labels = raw19526step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19526step2 raw19526step2Labels permutation7 permutation3
    mixedMoment B raw19526step3 raw19526step3Labels = mixedMoment B raw19526step4 raw19526step4Labels := by
      have ha : raw19526step4 = -raw19526step3 := by apply Matrix.ext; change ∀ i j, raw19526step4 i j = -(raw19526step3 i j); unfold raw19526step4 raw19526step3; decide +kernel
      have hl : raw19526step4Labels = raw19526step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1307 node1307Labels := by rfl

def raw19527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19527Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19527step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19527step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19527step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![4, -2, -2]]
def raw19527step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19527step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 0, 1], ![-3, 2, 1]]
def raw19527step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19527step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw19527step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19527 raw19527Labels = mixedMoment B node1307 node1307Labels := by
  calc
    mixedMoment B raw19527 raw19527Labels = mixedMoment B raw19527step0 raw19527step0Labels := by
      have hz : ∀ j, raw19527 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19527step0 = (fun i j => raw19527 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19527step0 raw19527; decide +kernel
      have hl : raw19527step0Labels = raw19527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19527 raw19527Labels permutation520 hz
    mixedMoment B raw19527step0 raw19527step0Labels = mixedMoment B raw19527step1 raw19527step1Labels := by
      have hz : ∀ j, raw19527step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19527step1 = (fun i j => raw19527step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19527step1 raw19527step0; decide +kernel
      have hl : raw19527step1Labels = raw19527step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19527step0 raw19527step0Labels permutation80 hz
    mixedMoment B raw19527step1 raw19527step1Labels = mixedMoment B raw19527step2 raw19527step2Labels := by
      have hz : ∀ j, raw19527step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19527step2 = (fun i j => raw19527step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19527step2 raw19527step1; decide +kernel
      have hl : raw19527step2Labels = raw19527step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19527step1 raw19527step1Labels permutation14 hz
    mixedMoment B raw19527step2 raw19527step2Labels = mixedMoment B raw19527step3 raw19527step3Labels := by
      have ha : raw19527step3 = (fun i j => raw19527step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19527step3 raw19527step2; decide +kernel
      have hl : raw19527step3Labels = raw19527step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19527step2 raw19527step2Labels permutation7 permutation3
    mixedMoment B raw19527step3 raw19527step3Labels = mixedMoment B raw19527step4 raw19527step4Labels := by
      have ha : raw19527step4 = -raw19527step3 := by apply Matrix.ext; change ∀ i j, raw19527step4 i j = -(raw19527step3 i j); unfold raw19527step4 raw19527step3; decide +kernel
      have hl : raw19527step4Labels = raw19527step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1307 node1307Labels := by rfl

def raw19528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19528Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19528step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19528step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19528step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19528step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![4, -2, -2]]
def raw19528step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19528step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 0, 1], ![-3, 2, 1]]
def raw19528step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19528step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw19528step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19528 raw19528Labels = mixedMoment B node1307 node1307Labels := by
  calc
    mixedMoment B raw19528 raw19528Labels = mixedMoment B raw19528step0 raw19528step0Labels := by
      have hz : ∀ j, raw19528 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19528step0 = (fun i j => raw19528 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19528step0 raw19528; decide +kernel
      have hl : raw19528step0Labels = raw19528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19528 raw19528Labels permutation434 hz
    mixedMoment B raw19528step0 raw19528step0Labels = mixedMoment B raw19528step1 raw19528step1Labels := by
      have hz : ∀ j, raw19528step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19528step1 = (fun i j => raw19528step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19528step1 raw19528step0; decide +kernel
      have hl : raw19528step1Labels = raw19528step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19528step0 raw19528step0Labels permutation80 hz
    mixedMoment B raw19528step1 raw19528step1Labels = mixedMoment B raw19528step2 raw19528step2Labels := by
      have hz : ∀ j, raw19528step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19528step2 = (fun i j => raw19528step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19528step2 raw19528step1; decide +kernel
      have hl : raw19528step2Labels = raw19528step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19528step1 raw19528step1Labels permutation14 hz
    mixedMoment B raw19528step2 raw19528step2Labels = mixedMoment B raw19528step3 raw19528step3Labels := by
      have ha : raw19528step3 = (fun i j => raw19528step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19528step3 raw19528step2; decide +kernel
      have hl : raw19528step3Labels = raw19528step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19528step2 raw19528step2Labels permutation7 permutation3
    mixedMoment B raw19528step3 raw19528step3Labels = mixedMoment B raw19528step4 raw19528step4Labels := by
      have ha : raw19528step4 = -raw19528step3 := by apply Matrix.ext; change ∀ i j, raw19528step4 i j = -(raw19528step3 i j); unfold raw19528step4 raw19528step3; decide +kernel
      have hl : raw19528step4Labels = raw19528step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1307 node1307Labels := by rfl

def raw19529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw19529Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw19529step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw19529step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19529step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![3, -1, -2]]
def raw19529step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19529step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 1, 2], ![3, -1, -2]]
def raw19529step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19529step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 2, 1], ![3, -2, -1]]
def raw19529step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19529 raw19529Labels = mixedMoment B node3126 node3126Labels := by
  calc
    mixedMoment B raw19529 raw19529Labels = mixedMoment B raw19529step0 raw19529step0Labels := by
      have hz : ∀ j, raw19529 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19529step0 = (fun i j => raw19529 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19529step0 raw19529; decide +kernel
      have hl : raw19529step0Labels = raw19529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19529 raw19529Labels permutation520 hz
    mixedMoment B raw19529step0 raw19529step0Labels = mixedMoment B raw19529step1 raw19529step1Labels := by
      have hz : ∀ j, raw19529step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19529step1 = (fun i j => raw19529step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19529step1 raw19529step0; decide +kernel
      have hl : raw19529step1Labels = raw19529step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19529step0 raw19529step0Labels permutation104 hz
    mixedMoment B raw19529step1 raw19529step1Labels = mixedMoment B raw19529step2 raw19529step2Labels := by
      have hz : ∀ j, raw19529step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19529step2 = (fun i j => raw19529step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19529step2 raw19529step1; decide +kernel
      have hl : raw19529step2Labels = raw19529step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19529step1 raw19529step1Labels permutation20 hz
    mixedMoment B raw19529step2 raw19529step2Labels = mixedMoment B raw19529step3 raw19529step3Labels := by
      have hz : ∀ j, raw19529step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19529step3 = (fun i j => raw19529step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19529step3 raw19529step2; decide +kernel
      have hl : raw19529step3Labels = raw19529step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19529step2 raw19529step2Labels permutation4 hz
    mixedMoment B raw19529step3 raw19529step3Labels = mixedMoment B raw19529step4 raw19529step4Labels := by
      have ha : raw19529step4 = (fun i j => raw19529step3 (permutation0 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19529step4 raw19529step3; decide +kernel
      have hl : raw19529step4Labels = raw19529step3Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19529step3 raw19529step3Labels permutation0 permutation3
    _ = mixedMoment B node3126 node3126Labels := by rfl

def raw19530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19530Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19530step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19530step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19530step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![4, -2, -2]]
def raw19530step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19530step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19530step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19530 raw19530Labels = mixedMoment B node615 node615Labels := by
  calc
    mixedMoment B raw19530 raw19530Labels = mixedMoment B raw19530step0 raw19530step0Labels := by
      have hz : ∀ j, raw19530 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19530step0 = (fun i j => raw19530 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19530step0 raw19530; decide +kernel
      have hl : raw19530step0Labels = raw19530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19530 raw19530Labels permutation520 hz
    mixedMoment B raw19530step0 raw19530step0Labels = mixedMoment B raw19530step1 raw19530step1Labels := by
      have hz : ∀ j, raw19530step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19530step1 = (fun i j => raw19530step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19530step1 raw19530step0; decide +kernel
      have hl : raw19530step1Labels = raw19530step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19530step0 raw19530step0Labels permutation104 hz
    mixedMoment B raw19530step1 raw19530step1Labels = mixedMoment B raw19530step2 raw19530step2Labels := by
      have hz : ∀ j, raw19530step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19530step2 = (fun i j => raw19530step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19530step2 raw19530step1; decide +kernel
      have hl : raw19530step2Labels = raw19530step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19530step1 raw19530step1Labels permutation20 hz
    mixedMoment B raw19530step2 raw19530step2Labels = mixedMoment B raw19530step3 raw19530step3Labels := by
      have ha : raw19530step3 = (fun i j => raw19530step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19530step3 raw19530step2; decide +kernel
      have hl : raw19530step3Labels = raw19530step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19530step2 raw19530step2Labels permutation2 permutation3
    _ = mixedMoment B node615 node615Labels := by rfl

def raw19531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19531Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19531step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19531step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19531step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19531 raw19531Labels = mixedMoment B node1140 node1140Labels := by
  calc
    mixedMoment B raw19531 raw19531Labels = mixedMoment B raw19531step0 raw19531step0Labels := by
      have hz : ∀ j, raw19531 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19531step0 = (fun i j => raw19531 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19531step0 raw19531; decide +kernel
      have hl : raw19531step0Labels = raw19531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19531 raw19531Labels permutation520 hz
    mixedMoment B raw19531step0 raw19531step0Labels = mixedMoment B raw19531step1 raw19531step1Labels := by
      have hz : ∀ j, raw19531step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19531step1 = (fun i j => raw19531step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19531step1 raw19531step0; decide +kernel
      have hl : raw19531step1Labels = raw19531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19531step0 raw19531step0Labels permutation104 hz
    mixedMoment B raw19531step1 raw19531step1Labels = mixedMoment B raw19531step2 raw19531step2Labels := by
      have ha : raw19531step2 = (fun i j => raw19531step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19531step2 raw19531step1; decide +kernel
      have hl : raw19531step2Labels = raw19531step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19531step1 raw19531step1Labels permutation10 permutation3
    _ = mixedMoment B node1140 node1140Labels := by rfl

def raw19532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19532Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19532step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19532step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19532step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19532step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19532step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19532 raw19532Labels = mixedMoment B node1140 node1140Labels := by
  calc
    mixedMoment B raw19532 raw19532Labels = mixedMoment B raw19532step0 raw19532step0Labels := by
      have hz : ∀ j, raw19532 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19532step0 = (fun i j => raw19532 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19532step0 raw19532; decide +kernel
      have hl : raw19532step0Labels = raw19532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19532 raw19532Labels permutation520 hz
    mixedMoment B raw19532step0 raw19532step0Labels = mixedMoment B raw19532step1 raw19532step1Labels := by
      have hz : ∀ j, raw19532step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19532step1 = (fun i j => raw19532step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19532step1 raw19532step0; decide +kernel
      have hl : raw19532step1Labels = raw19532step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19532step0 raw19532step0Labels permutation80 hz
    mixedMoment B raw19532step1 raw19532step1Labels = mixedMoment B raw19532step2 raw19532step2Labels := by
      have ha : raw19532step2 = (fun i j => raw19532step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19532step2 raw19532step1; decide +kernel
      have hl : raw19532step2Labels = raw19532step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19532step1 raw19532step1Labels permutation10 permutation3
    _ = mixedMoment B node1140 node1140Labels := by rfl

def raw19533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19533Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19533step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19533step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19533step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19533step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19533step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19533 raw19533Labels = mixedMoment B node1140 node1140Labels := by
  calc
    mixedMoment B raw19533 raw19533Labels = mixedMoment B raw19533step0 raw19533step0Labels := by
      have hz : ∀ j, raw19533 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19533step0 = (fun i j => raw19533 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19533step0 raw19533; decide +kernel
      have hl : raw19533step0Labels = raw19533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19533 raw19533Labels permutation434 hz
    mixedMoment B raw19533step0 raw19533step0Labels = mixedMoment B raw19533step1 raw19533step1Labels := by
      have hz : ∀ j, raw19533step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19533step1 = (fun i j => raw19533step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19533step1 raw19533step0; decide +kernel
      have hl : raw19533step1Labels = raw19533step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19533step0 raw19533step0Labels permutation80 hz
    mixedMoment B raw19533step1 raw19533step1Labels = mixedMoment B raw19533step2 raw19533step2Labels := by
      have ha : raw19533step2 = (fun i j => raw19533step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19533step2 raw19533step1; decide +kernel
      have hl : raw19533step2Labels = raw19533step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19533step1 raw19533step1Labels permutation10 permutation3
    _ = mixedMoment B node1140 node1140Labels := by rfl

def raw19534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw19534Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw19534step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw19534step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19534step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw19534step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19534step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw19534step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19534 raw19534Labels = mixedMoment B node1307 node1307Labels := by
  calc
    mixedMoment B raw19534 raw19534Labels = mixedMoment B raw19534step0 raw19534step0Labels := by
      have hz : ∀ j, raw19534 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19534step0 = (fun i j => raw19534 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19534step0 raw19534; decide +kernel
      have hl : raw19534step0Labels = raw19534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19534 raw19534Labels permutation520 hz
    mixedMoment B raw19534step0 raw19534step0Labels = mixedMoment B raw19534step1 raw19534step1Labels := by
      have hz : ∀ j, raw19534step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19534step1 = (fun i j => raw19534step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19534step1 raw19534step0; decide +kernel
      have hl : raw19534step1Labels = raw19534step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19534step0 raw19534step0Labels permutation104 hz
    mixedMoment B raw19534step1 raw19534step1Labels = mixedMoment B raw19534step2 raw19534step2Labels := by
      have hz : ∀ j, raw19534step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19534step2 = (fun i j => raw19534step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19534step2 raw19534step1; decide +kernel
      have hl : raw19534step2Labels = raw19534step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19534step1 raw19534step1Labels permutation20 hz
    mixedMoment B raw19534step2 raw19534step2Labels = mixedMoment B raw19534step3 raw19534step3Labels := by
      have ha : raw19534step3 = (fun i j => raw19534step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19534step3 raw19534step2; decide +kernel
      have hl : raw19534step3Labels = raw19534step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19534step2 raw19534step2Labels permutation2 permutation3
    _ = mixedMoment B node1307 node1307Labels := by rfl

def raw19535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19535Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19535step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19535step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19535step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19535step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![4, -2, -2]]
def raw19535step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19535step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19535step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19535 raw19535Labels = mixedMoment B node615 node615Labels := by
  calc
    mixedMoment B raw19535 raw19535Labels = mixedMoment B raw19535step0 raw19535step0Labels := by
      have hz : ∀ j, raw19535 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19535step0 = (fun i j => raw19535 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19535step0 raw19535; decide +kernel
      have hl : raw19535step0Labels = raw19535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19535 raw19535Labels permutation520 hz
    mixedMoment B raw19535step0 raw19535step0Labels = mixedMoment B raw19535step1 raw19535step1Labels := by
      have hz : ∀ j, raw19535step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19535step1 = (fun i j => raw19535step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19535step1 raw19535step0; decide +kernel
      have hl : raw19535step1Labels = raw19535step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19535step0 raw19535step0Labels permutation104 hz
    mixedMoment B raw19535step1 raw19535step1Labels = mixedMoment B raw19535step2 raw19535step2Labels := by
      have hz : ∀ j, raw19535step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19535step2 = (fun i j => raw19535step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19535step2 raw19535step1; decide +kernel
      have hl : raw19535step2Labels = raw19535step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19535step1 raw19535step1Labels permutation14 hz
    mixedMoment B raw19535step2 raw19535step2Labels = mixedMoment B raw19535step3 raw19535step3Labels := by
      have ha : raw19535step3 = (fun i j => raw19535step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19535step3 raw19535step2; decide +kernel
      have hl : raw19535step3Labels = raw19535step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19535step2 raw19535step2Labels permutation2 permutation3
    _ = mixedMoment B node615 node615Labels := by rfl

def raw19536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19536Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19536step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19536step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19536step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19536step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19536step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19536 raw19536Labels = mixedMoment B node1140 node1140Labels := by
  calc
    mixedMoment B raw19536 raw19536Labels = mixedMoment B raw19536step0 raw19536step0Labels := by
      have hz : ∀ j, raw19536 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19536step0 = (fun i j => raw19536 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19536step0 raw19536; decide +kernel
      have hl : raw19536step0Labels = raw19536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19536 raw19536Labels permutation520 hz
    mixedMoment B raw19536step0 raw19536step0Labels = mixedMoment B raw19536step1 raw19536step1Labels := by
      have hz : ∀ j, raw19536step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19536step1 = (fun i j => raw19536step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19536step1 raw19536step0; decide +kernel
      have hl : raw19536step1Labels = raw19536step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19536step0 raw19536step0Labels permutation104 hz
    mixedMoment B raw19536step1 raw19536step1Labels = mixedMoment B raw19536step2 raw19536step2Labels := by
      have ha : raw19536step2 = (fun i j => raw19536step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19536step2 raw19536step1; decide +kernel
      have hl : raw19536step2Labels = raw19536step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19536step1 raw19536step1Labels permutation8 permutation3
    _ = mixedMoment B node1140 node1140Labels := by rfl

def raw19537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19537Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19537step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19537step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19537step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19537step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19537step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19537 raw19537Labels = mixedMoment B node1140 node1140Labels := by
  calc
    mixedMoment B raw19537 raw19537Labels = mixedMoment B raw19537step0 raw19537step0Labels := by
      have hz : ∀ j, raw19537 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19537step0 = (fun i j => raw19537 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19537step0 raw19537; decide +kernel
      have hl : raw19537step0Labels = raw19537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19537 raw19537Labels permutation520 hz
    mixedMoment B raw19537step0 raw19537step0Labels = mixedMoment B raw19537step1 raw19537step1Labels := by
      have hz : ∀ j, raw19537step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19537step1 = (fun i j => raw19537step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19537step1 raw19537step0; decide +kernel
      have hl : raw19537step1Labels = raw19537step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19537step0 raw19537step0Labels permutation56 hz
    mixedMoment B raw19537step1 raw19537step1Labels = mixedMoment B raw19537step2 raw19537step2Labels := by
      have ha : raw19537step2 = (fun i j => raw19537step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19537step2 raw19537step1; decide +kernel
      have hl : raw19537step2Labels = raw19537step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19537step1 raw19537step1Labels permutation10 permutation3
    _ = mixedMoment B node1140 node1140Labels := by rfl

def raw19538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19538Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19538step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19538step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19538step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19538step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19538step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19538 raw19538Labels = mixedMoment B node1140 node1140Labels := by
  calc
    mixedMoment B raw19538 raw19538Labels = mixedMoment B raw19538step0 raw19538step0Labels := by
      have hz : ∀ j, raw19538 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19538step0 = (fun i j => raw19538 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19538step0 raw19538; decide +kernel
      have hl : raw19538step0Labels = raw19538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19538 raw19538Labels permutation434 hz
    mixedMoment B raw19538step0 raw19538step0Labels = mixedMoment B raw19538step1 raw19538step1Labels := by
      have hz : ∀ j, raw19538step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19538step1 = (fun i j => raw19538step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19538step1 raw19538step0; decide +kernel
      have hl : raw19538step1Labels = raw19538step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19538step0 raw19538step0Labels permutation56 hz
    mixedMoment B raw19538step1 raw19538step1Labels = mixedMoment B raw19538step2 raw19538step2Labels := by
      have ha : raw19538step2 = (fun i j => raw19538step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19538step2 raw19538step1; decide +kernel
      have hl : raw19538step2Labels = raw19538step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19538step1 raw19538step1Labels permutation10 permutation3
    _ = mixedMoment B node1140 node1140Labels := by rfl

def raw19539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw19539Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw19539step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19539step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw19539step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19539step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw19539step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19539step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw19539step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19539 raw19539Labels = mixedMoment B node1307 node1307Labels := by
  calc
    mixedMoment B raw19539 raw19539Labels = mixedMoment B raw19539step0 raw19539step0Labels := by
      have hz : ∀ j, raw19539 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19539step0 = (fun i j => raw19539 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19539step0 raw19539; decide +kernel
      have hl : raw19539step0Labels = raw19539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19539 raw19539Labels permutation520 hz
    mixedMoment B raw19539step0 raw19539step0Labels = mixedMoment B raw19539step1 raw19539step1Labels := by
      have hz : ∀ j, raw19539step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19539step1 = (fun i j => raw19539step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19539step1 raw19539step0; decide +kernel
      have hl : raw19539step1Labels = raw19539step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19539step0 raw19539step0Labels permutation104 hz
    mixedMoment B raw19539step1 raw19539step1Labels = mixedMoment B raw19539step2 raw19539step2Labels := by
      have hz : ∀ j, raw19539step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19539step2 = (fun i j => raw19539step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19539step2 raw19539step1; decide +kernel
      have hl : raw19539step2Labels = raw19539step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19539step1 raw19539step1Labels permutation14 hz
    mixedMoment B raw19539step2 raw19539step2Labels = mixedMoment B raw19539step3 raw19539step3Labels := by
      have ha : raw19539step3 = (fun i j => raw19539step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19539step3 raw19539step2; decide +kernel
      have hl : raw19539step3Labels = raw19539step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19539step2 raw19539step2Labels permutation2 permutation3
    _ = mixedMoment B node1307 node1307Labels := by rfl

def raw19540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19540Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19540step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19540step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19540step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19540step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![4, -2, -2]]
def raw19540step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19540step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19540step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19540 raw19540Labels = mixedMoment B node615 node615Labels := by
  calc
    mixedMoment B raw19540 raw19540Labels = mixedMoment B raw19540step0 raw19540step0Labels := by
      have hz : ∀ j, raw19540 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19540step0 = (fun i j => raw19540 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19540step0 raw19540; decide +kernel
      have hl : raw19540step0Labels = raw19540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19540 raw19540Labels permutation520 hz
    mixedMoment B raw19540step0 raw19540step0Labels = mixedMoment B raw19540step1 raw19540step1Labels := by
      have hz : ∀ j, raw19540step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19540step1 = (fun i j => raw19540step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19540step1 raw19540step0; decide +kernel
      have hl : raw19540step1Labels = raw19540step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19540step0 raw19540step0Labels permutation80 hz
    mixedMoment B raw19540step1 raw19540step1Labels = mixedMoment B raw19540step2 raw19540step2Labels := by
      have hz : ∀ j, raw19540step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19540step2 = (fun i j => raw19540step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19540step2 raw19540step1; decide +kernel
      have hl : raw19540step2Labels = raw19540step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19540step1 raw19540step1Labels permutation14 hz
    mixedMoment B raw19540step2 raw19540step2Labels = mixedMoment B raw19540step3 raw19540step3Labels := by
      have ha : raw19540step3 = (fun i j => raw19540step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19540step3 raw19540step2; decide +kernel
      have hl : raw19540step3Labels = raw19540step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19540step2 raw19540step2Labels permutation2 permutation3
    _ = mixedMoment B node615 node615Labels := by rfl

def raw19541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19541Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19541step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19541step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19541step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19541step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19541step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19541 raw19541Labels = mixedMoment B node1140 node1140Labels := by
  calc
    mixedMoment B raw19541 raw19541Labels = mixedMoment B raw19541step0 raw19541step0Labels := by
      have hz : ∀ j, raw19541 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19541step0 = (fun i j => raw19541 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19541step0 raw19541; decide +kernel
      have hl : raw19541step0Labels = raw19541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19541 raw19541Labels permutation520 hz
    mixedMoment B raw19541step0 raw19541step0Labels = mixedMoment B raw19541step1 raw19541step1Labels := by
      have hz : ∀ j, raw19541step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19541step1 = (fun i j => raw19541step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19541step1 raw19541step0; decide +kernel
      have hl : raw19541step1Labels = raw19541step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19541step0 raw19541step0Labels permutation80 hz
    mixedMoment B raw19541step1 raw19541step1Labels = mixedMoment B raw19541step2 raw19541step2Labels := by
      have ha : raw19541step2 = (fun i j => raw19541step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19541step2 raw19541step1; decide +kernel
      have hl : raw19541step2Labels = raw19541step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19541step1 raw19541step1Labels permutation8 permutation3
    _ = mixedMoment B node1140 node1140Labels := by rfl

def raw19542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw19542Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19542step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19542step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19542step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19542step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19542step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19542 raw19542Labels = mixedMoment B node1140 node1140Labels := by
  calc
    mixedMoment B raw19542 raw19542Labels = mixedMoment B raw19542step0 raw19542step0Labels := by
      have hz : ∀ j, raw19542 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19542step0 = (fun i j => raw19542 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19542step0 raw19542; decide +kernel
      have hl : raw19542step0Labels = raw19542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19542 raw19542Labels permutation520 hz
    mixedMoment B raw19542step0 raw19542step0Labels = mixedMoment B raw19542step1 raw19542step1Labels := by
      have hz : ∀ j, raw19542step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19542step1 = (fun i j => raw19542step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19542step1 raw19542step0; decide +kernel
      have hl : raw19542step1Labels = raw19542step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19542step0 raw19542step0Labels permutation56 hz
    mixedMoment B raw19542step1 raw19542step1Labels = mixedMoment B raw19542step2 raw19542step2Labels := by
      have ha : raw19542step2 = (fun i j => raw19542step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19542step2 raw19542step1; decide +kernel
      have hl : raw19542step2Labels = raw19542step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19542step1 raw19542step1Labels permutation8 permutation3
    _ = mixedMoment B node1140 node1140Labels := by rfl

def raw19543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19543Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19543step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19543step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw19543step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19543step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19543step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19543 raw19543Labels = mixedMoment B node1140 node1140Labels := by
  calc
    mixedMoment B raw19543 raw19543Labels = mixedMoment B raw19543step0 raw19543step0Labels := by
      have hz : ∀ j, raw19543 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19543step0 = (fun i j => raw19543 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19543step0 raw19543; decide +kernel
      have hl : raw19543step0Labels = raw19543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19543 raw19543Labels permutation346 hz
    mixedMoment B raw19543step0 raw19543step0Labels = mixedMoment B raw19543step1 raw19543step1Labels := by
      have hz : ∀ j, raw19543step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19543step1 = (fun i j => raw19543step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19543step1 raw19543step0; decide +kernel
      have hl : raw19543step1Labels = raw19543step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19543step0 raw19543step0Labels permutation56 hz
    mixedMoment B raw19543step1 raw19543step1Labels = mixedMoment B raw19543step2 raw19543step2Labels := by
      have ha : raw19543step2 = (fun i j => raw19543step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19543step2 raw19543step1; decide +kernel
      have hl : raw19543step2Labels = raw19543step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19543step1 raw19543step1Labels permutation10 permutation3
    _ = mixedMoment B node1140 node1140Labels := by rfl

def raw19544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw19544Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw19544step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19544step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw19544step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19544step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw19544step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19544step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw19544step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19544 raw19544Labels = mixedMoment B node1307 node1307Labels := by
  calc
    mixedMoment B raw19544 raw19544Labels = mixedMoment B raw19544step0 raw19544step0Labels := by
      have hz : ∀ j, raw19544 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19544step0 = (fun i j => raw19544 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19544step0 raw19544; decide +kernel
      have hl : raw19544step0Labels = raw19544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19544 raw19544Labels permutation520 hz
    mixedMoment B raw19544step0 raw19544step0Labels = mixedMoment B raw19544step1 raw19544step1Labels := by
      have hz : ∀ j, raw19544step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19544step1 = (fun i j => raw19544step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19544step1 raw19544step0; decide +kernel
      have hl : raw19544step1Labels = raw19544step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19544step0 raw19544step0Labels permutation80 hz
    mixedMoment B raw19544step1 raw19544step1Labels = mixedMoment B raw19544step2 raw19544step2Labels := by
      have hz : ∀ j, raw19544step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19544step2 = (fun i j => raw19544step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19544step2 raw19544step1; decide +kernel
      have hl : raw19544step2Labels = raw19544step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19544step1 raw19544step1Labels permutation14 hz
    mixedMoment B raw19544step2 raw19544step2Labels = mixedMoment B raw19544step3 raw19544step3Labels := by
      have ha : raw19544step3 = (fun i j => raw19544step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19544step3 raw19544step2; decide +kernel
      have hl : raw19544step3Labels = raw19544step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19544step2 raw19544step2Labels permutation2 permutation3
    _ = mixedMoment B node1307 node1307Labels := by rfl

def raw19545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19545Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19545step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19545step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19545step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19545step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![4, -2, -2]]
def raw19545step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19545step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19545step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19545 raw19545Labels = mixedMoment B node615 node615Labels := by
  calc
    mixedMoment B raw19545 raw19545Labels = mixedMoment B raw19545step0 raw19545step0Labels := by
      have hz : ∀ j, raw19545 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19545step0 = (fun i j => raw19545 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19545step0 raw19545; decide +kernel
      have hl : raw19545step0Labels = raw19545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19545 raw19545Labels permutation434 hz
    mixedMoment B raw19545step0 raw19545step0Labels = mixedMoment B raw19545step1 raw19545step1Labels := by
      have hz : ∀ j, raw19545step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19545step1 = (fun i j => raw19545step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19545step1 raw19545step0; decide +kernel
      have hl : raw19545step1Labels = raw19545step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19545step0 raw19545step0Labels permutation80 hz
    mixedMoment B raw19545step1 raw19545step1Labels = mixedMoment B raw19545step2 raw19545step2Labels := by
      have hz : ∀ j, raw19545step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19545step2 = (fun i j => raw19545step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19545step2 raw19545step1; decide +kernel
      have hl : raw19545step2Labels = raw19545step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19545step1 raw19545step1Labels permutation14 hz
    mixedMoment B raw19545step2 raw19545step2Labels = mixedMoment B raw19545step3 raw19545step3Labels := by
      have ha : raw19545step3 = (fun i j => raw19545step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19545step3 raw19545step2; decide +kernel
      have hl : raw19545step3Labels = raw19545step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19545step2 raw19545step2Labels permutation2 permutation3
    _ = mixedMoment B node615 node615Labels := by rfl

def raw19546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19546Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19546step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19546step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19546step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19546 raw19546Labels = mixedMoment B node1140 node1140Labels := by
  calc
    mixedMoment B raw19546 raw19546Labels = mixedMoment B raw19546step0 raw19546step0Labels := by
      have hz : ∀ j, raw19546 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19546step0 = (fun i j => raw19546 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19546step0 raw19546; decide +kernel
      have hl : raw19546step0Labels = raw19546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19546 raw19546Labels permutation434 hz
    mixedMoment B raw19546step0 raw19546step0Labels = mixedMoment B raw19546step1 raw19546step1Labels := by
      have hz : ∀ j, raw19546step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19546step1 = (fun i j => raw19546step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19546step1 raw19546step0; decide +kernel
      have hl : raw19546step1Labels = raw19546step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19546step0 raw19546step0Labels permutation80 hz
    mixedMoment B raw19546step1 raw19546step1Labels = mixedMoment B raw19546step2 raw19546step2Labels := by
      have ha : raw19546step2 = (fun i j => raw19546step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19546step2 raw19546step1; decide +kernel
      have hl : raw19546step2Labels = raw19546step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19546step1 raw19546step1Labels permutation8 permutation3
    _ = mixedMoment B node1140 node1140Labels := by rfl

def raw19547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19547Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19547step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19547step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19547step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19547step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19547step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19547 raw19547Labels = mixedMoment B node1140 node1140Labels := by
  calc
    mixedMoment B raw19547 raw19547Labels = mixedMoment B raw19547step0 raw19547step0Labels := by
      have hz : ∀ j, raw19547 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19547step0 = (fun i j => raw19547 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19547step0 raw19547; decide +kernel
      have hl : raw19547step0Labels = raw19547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19547 raw19547Labels permutation434 hz
    mixedMoment B raw19547step0 raw19547step0Labels = mixedMoment B raw19547step1 raw19547step1Labels := by
      have hz : ∀ j, raw19547step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19547step1 = (fun i j => raw19547step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19547step1 raw19547step0; decide +kernel
      have hl : raw19547step1Labels = raw19547step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19547step0 raw19547step0Labels permutation56 hz
    mixedMoment B raw19547step1 raw19547step1Labels = mixedMoment B raw19547step2 raw19547step2Labels := by
      have ha : raw19547step2 = (fun i j => raw19547step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19547step2 raw19547step1; decide +kernel
      have hl : raw19547step2Labels = raw19547step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19547step1 raw19547step1Labels permutation8 permutation3
    _ = mixedMoment B node1140 node1140Labels := by rfl

def raw19548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19548Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19548step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19548step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![4, -2, -2]]
def raw19548step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19548step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw19548step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19548 raw19548Labels = mixedMoment B node1140 node1140Labels := by
  calc
    mixedMoment B raw19548 raw19548Labels = mixedMoment B raw19548step0 raw19548step0Labels := by
      have hz : ∀ j, raw19548 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19548step0 = (fun i j => raw19548 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19548step0 raw19548; decide +kernel
      have hl : raw19548step0Labels = raw19548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19548 raw19548Labels permutation346 hz
    mixedMoment B raw19548step0 raw19548step0Labels = mixedMoment B raw19548step1 raw19548step1Labels := by
      have hz : ∀ j, raw19548step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19548step1 = (fun i j => raw19548step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19548step1 raw19548step0; decide +kernel
      have hl : raw19548step1Labels = raw19548step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19548step0 raw19548step0Labels permutation56 hz
    mixedMoment B raw19548step1 raw19548step1Labels = mixedMoment B raw19548step2 raw19548step2Labels := by
      have ha : raw19548step2 = (fun i j => raw19548step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19548step2 raw19548step1; decide +kernel
      have hl : raw19548step2Labels = raw19548step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19548step1 raw19548step1Labels permutation8 permutation3
    _ = mixedMoment B node1140 node1140Labels := by rfl

def raw19549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw19549Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw19549step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw19549step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19549step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw19549step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19549step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw19549step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19549 raw19549Labels = mixedMoment B node1307 node1307Labels := by
  calc
    mixedMoment B raw19549 raw19549Labels = mixedMoment B raw19549step0 raw19549step0Labels := by
      have hz : ∀ j, raw19549 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19549step0 = (fun i j => raw19549 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19549step0 raw19549; decide +kernel
      have hl : raw19549step0Labels = raw19549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19549 raw19549Labels permutation434 hz
    mixedMoment B raw19549step0 raw19549step0Labels = mixedMoment B raw19549step1 raw19549step1Labels := by
      have hz : ∀ j, raw19549step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19549step1 = (fun i j => raw19549step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19549step1 raw19549step0; decide +kernel
      have hl : raw19549step1Labels = raw19549step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19549step0 raw19549step0Labels permutation80 hz
    mixedMoment B raw19549step1 raw19549step1Labels = mixedMoment B raw19549step2 raw19549step2Labels := by
      have hz : ∀ j, raw19549step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19549step2 = (fun i j => raw19549step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19549step2 raw19549step1; decide +kernel
      have hl : raw19549step2Labels = raw19549step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19549step1 raw19549step1Labels permutation14 hz
    mixedMoment B raw19549step2 raw19549step2Labels = mixedMoment B raw19549step3 raw19549step3Labels := by
      have ha : raw19549step3 = (fun i j => raw19549step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19549step3 raw19549step2; decide +kernel
      have hl : raw19549step3Labels = raw19549step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19549step2 raw19549step2Labels permutation2 permutation3
    _ = mixedMoment B node1307 node1307Labels := by rfl

def raw19550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19550Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19550step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19550step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19550step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![5, -3, -2]]
def raw19550step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19550step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 3, 2], ![5, -3, -2]]
def raw19550step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19550step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def raw19550step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19550 raw19550Labels = mixedMoment B node622 node622Labels := by
  calc
    mixedMoment B raw19550 raw19550Labels = mixedMoment B raw19550step0 raw19550step0Labels := by
      have hz : ∀ j, raw19550 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19550step0 = (fun i j => raw19550 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19550step0 raw19550; decide +kernel
      have hl : raw19550step0Labels = raw19550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19550 raw19550Labels permutation520 hz
    mixedMoment B raw19550step0 raw19550step0Labels = mixedMoment B raw19550step1 raw19550step1Labels := by
      have hz : ∀ j, raw19550step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19550step1 = (fun i j => raw19550step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19550step1 raw19550step0; decide +kernel
      have hl : raw19550step1Labels = raw19550step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19550step0 raw19550step0Labels permutation104 hz
    mixedMoment B raw19550step1 raw19550step1Labels = mixedMoment B raw19550step2 raw19550step2Labels := by
      have hz : ∀ j, raw19550step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19550step2 = (fun i j => raw19550step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19550step2 raw19550step1; decide +kernel
      have hl : raw19550step2Labels = raw19550step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19550step1 raw19550step1Labels permutation20 hz
    mixedMoment B raw19550step2 raw19550step2Labels = mixedMoment B raw19550step3 raw19550step3Labels := by
      have hz : ∀ j, raw19550step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19550step3 = (fun i j => raw19550step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19550step3 raw19550step2; decide +kernel
      have hl : raw19550step3Labels = raw19550step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19550step2 raw19550step2Labels permutation4 hz
    mixedMoment B raw19550step3 raw19550step3Labels = mixedMoment B raw19550step4 raw19550step4Labels := by
      have ha : raw19550step4 = (fun i j => raw19550step3 (permutation0 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19550step4 raw19550step3; decide +kernel
      have hl : raw19550step4Labels = raw19550step3Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19550step3 raw19550step3Labels permutation0 permutation3
    _ = mixedMoment B node622 node622Labels := by rfl

def raw19551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19551Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19551step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19551step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19551step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![5, -3, -2]]
def raw19551step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19551step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-4, 2, 2]]
def raw19551step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19551step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19551step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19551 raw19551Labels = mixedMoment B node615 node615Labels := by
  calc
    mixedMoment B raw19551 raw19551Labels = mixedMoment B raw19551step0 raw19551step0Labels := by
      have hz : ∀ j, raw19551 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19551step0 = (fun i j => raw19551 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19551step0 raw19551; decide +kernel
      have hl : raw19551step0Labels = raw19551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19551 raw19551Labels permutation520 hz
    mixedMoment B raw19551step0 raw19551step0Labels = mixedMoment B raw19551step1 raw19551step1Labels := by
      have hz : ∀ j, raw19551step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19551step1 = (fun i j => raw19551step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19551step1 raw19551step0; decide +kernel
      have hl : raw19551step1Labels = raw19551step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19551step0 raw19551step0Labels permutation104 hz
    mixedMoment B raw19551step1 raw19551step1Labels = mixedMoment B raw19551step2 raw19551step2Labels := by
      have hz : ∀ j, raw19551step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19551step2 = (fun i j => raw19551step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19551step2 raw19551step1; decide +kernel
      have hl : raw19551step2Labels = raw19551step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19551step1 raw19551step1Labels permutation20 hz
    mixedMoment B raw19551step2 raw19551step2Labels = mixedMoment B raw19551step3 raw19551step3Labels := by
      have ha : raw19551step3 = (fun i j => raw19551step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19551step3 raw19551step2; decide +kernel
      have hl : raw19551step3Labels = raw19551step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19551step2 raw19551step2Labels permutation7 permutation3
    mixedMoment B raw19551step3 raw19551step3Labels = mixedMoment B raw19551step4 raw19551step4Labels := by
      have ha : raw19551step4 = -raw19551step3 := by apply Matrix.ext; change ∀ i j, raw19551step4 i j = -(raw19551step3 i j); unfold raw19551step4 raw19551step3; decide +kernel
      have hl : raw19551step4Labels = raw19551step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node615 node615Labels := by rfl

def raw19552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19552Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19552step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19552step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![5, -3, -2]]
def raw19552step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19552step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![5, -3, -2]]
def raw19552step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19552step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-4, 2, 2]]
def raw19552step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19552step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19552step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19552 raw19552Labels = mixedMoment B node615 node615Labels := by
  calc
    mixedMoment B raw19552 raw19552Labels = mixedMoment B raw19552step0 raw19552step0Labels := by
      have hz : ∀ j, raw19552 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19552step0 = (fun i j => raw19552 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19552step0 raw19552; decide +kernel
      have hl : raw19552step0Labels = raw19552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19552 raw19552Labels permutation520 hz
    mixedMoment B raw19552step0 raw19552step0Labels = mixedMoment B raw19552step1 raw19552step1Labels := by
      have hz : ∀ j, raw19552step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19552step1 = (fun i j => raw19552step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19552step1 raw19552step0; decide +kernel
      have hl : raw19552step1Labels = raw19552step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19552step0 raw19552step0Labels permutation104 hz
    mixedMoment B raw19552step1 raw19552step1Labels = mixedMoment B raw19552step2 raw19552step2Labels := by
      have hz : ∀ j, raw19552step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19552step2 = (fun i j => raw19552step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19552step2 raw19552step1; decide +kernel
      have hl : raw19552step2Labels = raw19552step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19552step1 raw19552step1Labels permutation14 hz
    mixedMoment B raw19552step2 raw19552step2Labels = mixedMoment B raw19552step3 raw19552step3Labels := by
      have ha : raw19552step3 = (fun i j => raw19552step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19552step3 raw19552step2; decide +kernel
      have hl : raw19552step3Labels = raw19552step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19552step2 raw19552step2Labels permutation7 permutation3
    mixedMoment B raw19552step3 raw19552step3Labels = mixedMoment B raw19552step4 raw19552step4Labels := by
      have ha : raw19552step4 = -raw19552step3 := by apply Matrix.ext; change ∀ i j, raw19552step4 i j = -(raw19552step3 i j); unfold raw19552step4 raw19552step3; decide +kernel
      have hl : raw19552step4Labels = raw19552step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node615 node615Labels := by rfl

def raw19553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![5, -3, -2]]
def raw19553Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -3, -2]]
def raw19553step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19553step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![5, -3, -2]]
def raw19553step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19553step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![5, -3, -2]]
def raw19553step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19553step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-4, 2, 2]]
def raw19553step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19553step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19553step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19553 raw19553Labels = mixedMoment B node615 node615Labels := by
  calc
    mixedMoment B raw19553 raw19553Labels = mixedMoment B raw19553step0 raw19553step0Labels := by
      have hz : ∀ j, raw19553 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19553step0 = (fun i j => raw19553 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19553step0 raw19553; decide +kernel
      have hl : raw19553step0Labels = raw19553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19553 raw19553Labels permutation520 hz
    mixedMoment B raw19553step0 raw19553step0Labels = mixedMoment B raw19553step1 raw19553step1Labels := by
      have hz : ∀ j, raw19553step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19553step1 = (fun i j => raw19553step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19553step1 raw19553step0; decide +kernel
      have hl : raw19553step1Labels = raw19553step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19553step0 raw19553step0Labels permutation80 hz
    mixedMoment B raw19553step1 raw19553step1Labels = mixedMoment B raw19553step2 raw19553step2Labels := by
      have hz : ∀ j, raw19553step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19553step2 = (fun i j => raw19553step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19553step2 raw19553step1; decide +kernel
      have hl : raw19553step2Labels = raw19553step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19553step1 raw19553step1Labels permutation14 hz
    mixedMoment B raw19553step2 raw19553step2Labels = mixedMoment B raw19553step3 raw19553step3Labels := by
      have ha : raw19553step3 = (fun i j => raw19553step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19553step3 raw19553step2; decide +kernel
      have hl : raw19553step3Labels = raw19553step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19553step2 raw19553step2Labels permutation7 permutation3
    mixedMoment B raw19553step3 raw19553step3Labels = mixedMoment B raw19553step4 raw19553step4Labels := by
      have ha : raw19553step4 = -raw19553step3 := by apply Matrix.ext; change ∀ i j, raw19553step4 i j = -(raw19553step3 i j); unfold raw19553step4 raw19553step3; decide +kernel
      have hl : raw19553step4Labels = raw19553step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node615 node615Labels := by rfl

def raw19554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -3, -2]]
def raw19554Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -3, -2]]
def raw19554step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![5, -3, -2]]
def raw19554step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19554step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![5, -3, -2]]
def raw19554step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19554step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 0, 1], ![-4, 2, 2]]
def raw19554step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19554step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw19554step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19554 raw19554Labels = mixedMoment B node615 node615Labels := by
  calc
    mixedMoment B raw19554 raw19554Labels = mixedMoment B raw19554step0 raw19554step0Labels := by
      have hz : ∀ j, raw19554 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19554step0 = (fun i j => raw19554 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19554step0 raw19554; decide +kernel
      have hl : raw19554step0Labels = raw19554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19554 raw19554Labels permutation434 hz
    mixedMoment B raw19554step0 raw19554step0Labels = mixedMoment B raw19554step1 raw19554step1Labels := by
      have hz : ∀ j, raw19554step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19554step1 = (fun i j => raw19554step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19554step1 raw19554step0; decide +kernel
      have hl : raw19554step1Labels = raw19554step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19554step0 raw19554step0Labels permutation80 hz
    mixedMoment B raw19554step1 raw19554step1Labels = mixedMoment B raw19554step2 raw19554step2Labels := by
      have hz : ∀ j, raw19554step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19554step2 = (fun i j => raw19554step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19554step2 raw19554step1; decide +kernel
      have hl : raw19554step2Labels = raw19554step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19554step1 raw19554step1Labels permutation14 hz
    mixedMoment B raw19554step2 raw19554step2Labels = mixedMoment B raw19554step3 raw19554step3Labels := by
      have ha : raw19554step3 = (fun i j => raw19554step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19554step3 raw19554step2; decide +kernel
      have hl : raw19554step3Labels = raw19554step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19554step2 raw19554step2Labels permutation7 permutation3
    mixedMoment B raw19554step3 raw19554step3Labels = mixedMoment B raw19554step4 raw19554step4Labels := by
      have ha : raw19554step4 = -raw19554step3 := by apply Matrix.ext; change ∀ i j, raw19554step4 i j = -(raw19554step3 i j); unfold raw19554step4 raw19554step3; decide +kernel
      have hl : raw19554step4Labels = raw19554step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node615 node615Labels := by rfl

def raw19555 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19555Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19555step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19555step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19555step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19555step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19555step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19555step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19555step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19555step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19555 raw19555Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19555 raw19555Labels = mixedMoment B raw19555step0 raw19555step0Labels := by
      have hz : ∀ j, raw19555 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19555step0 = (fun i j => raw19555 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19555step0 raw19555; decide +kernel
      have hl : raw19555step0Labels = raw19555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19555 raw19555Labels permutation520 hz
    mixedMoment B raw19555step0 raw19555step0Labels = mixedMoment B raw19555step1 raw19555step1Labels := by
      have hz : ∀ j, raw19555step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19555step1 = (fun i j => raw19555step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19555step1 raw19555step0; decide +kernel
      have hl : raw19555step1Labels = raw19555step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19555step0 raw19555step0Labels permutation104 hz
    mixedMoment B raw19555step1 raw19555step1Labels = mixedMoment B raw19555step2 raw19555step2Labels := by
      have hz : ∀ j, raw19555step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19555step2 = (fun i j => raw19555step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19555step2 raw19555step1; decide +kernel
      have hl : raw19555step2Labels = raw19555step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19555step1 raw19555step1Labels permutation20 hz
    mixedMoment B raw19555step2 raw19555step2Labels = mixedMoment B raw19555step3 raw19555step3Labels := by
      have ha : raw19555step3 = (fun i j => raw19555step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19555step3 raw19555step2; decide +kernel
      have hl : raw19555step3Labels = raw19555step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19555step2 raw19555step2Labels permutation2 permutation7
    mixedMoment B raw19555step3 raw19555step3Labels = mixedMoment B raw19555step4 raw19555step4Labels := by
      have ha : raw19555step4 = raw19555step3 := by apply Matrix.ext; unfold raw19555step4 raw19555step3; decide +kernel
      have hl : raw19555step3Labels = labelEmbedding10 ∘ raw19555step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19555step3 raw19555step3Labels raw19555step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

def raw19556 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19556step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19556step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19556step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19556step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19556step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19556step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19556step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19556step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19556step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19556 raw19556Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19556 raw19556Labels = mixedMoment B raw19556step0 raw19556step0Labels := by
      have hz : ∀ j, raw19556 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19556step0 = (fun i j => raw19556 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19556step0 raw19556; decide +kernel
      have hl : raw19556step0Labels = raw19556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19556 raw19556Labels permutation520 hz
    mixedMoment B raw19556step0 raw19556step0Labels = mixedMoment B raw19556step1 raw19556step1Labels := by
      have hz : ∀ j, raw19556step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19556step1 = (fun i j => raw19556step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19556step1 raw19556step0; decide +kernel
      have hl : raw19556step1Labels = raw19556step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19556step0 raw19556step0Labels permutation104 hz
    mixedMoment B raw19556step1 raw19556step1Labels = mixedMoment B raw19556step2 raw19556step2Labels := by
      have hz : ∀ j, raw19556step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19556step2 = (fun i j => raw19556step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19556step2 raw19556step1; decide +kernel
      have hl : raw19556step2Labels = raw19556step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19556step1 raw19556step1Labels permutation14 hz
    mixedMoment B raw19556step2 raw19556step2Labels = mixedMoment B raw19556step3 raw19556step3Labels := by
      have ha : raw19556step3 = (fun i j => raw19556step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19556step3 raw19556step2; decide +kernel
      have hl : raw19556step3Labels = raw19556step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19556step2 raw19556step2Labels permutation2 permutation7
    mixedMoment B raw19556step3 raw19556step3Labels = mixedMoment B raw19556step4 raw19556step4Labels := by
      have ha : raw19556step4 = raw19556step3 := by apply Matrix.ext; unfold raw19556step4 raw19556step3; decide +kernel
      have hl : raw19556step3Labels = labelEmbedding10 ∘ raw19556step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19556step3 raw19556step3Labels raw19556step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

def raw19557 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19557Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19557step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19557step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19557step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19557step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19557step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19557step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19557step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19557step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19557 raw19557Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19557 raw19557Labels = mixedMoment B raw19557step0 raw19557step0Labels := by
      have hz : ∀ j, raw19557 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19557step0 = (fun i j => raw19557 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19557step0 raw19557; decide +kernel
      have hl : raw19557step0Labels = raw19557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19557 raw19557Labels permutation520 hz
    mixedMoment B raw19557step0 raw19557step0Labels = mixedMoment B raw19557step1 raw19557step1Labels := by
      have hz : ∀ j, raw19557step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19557step1 = (fun i j => raw19557step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19557step1 raw19557step0; decide +kernel
      have hl : raw19557step1Labels = raw19557step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19557step0 raw19557step0Labels permutation80 hz
    mixedMoment B raw19557step1 raw19557step1Labels = mixedMoment B raw19557step2 raw19557step2Labels := by
      have hz : ∀ j, raw19557step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19557step2 = (fun i j => raw19557step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19557step2 raw19557step1; decide +kernel
      have hl : raw19557step2Labels = raw19557step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19557step1 raw19557step1Labels permutation14 hz
    mixedMoment B raw19557step2 raw19557step2Labels = mixedMoment B raw19557step3 raw19557step3Labels := by
      have ha : raw19557step3 = (fun i j => raw19557step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19557step3 raw19557step2; decide +kernel
      have hl : raw19557step3Labels = raw19557step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19557step2 raw19557step2Labels permutation2 permutation7
    mixedMoment B raw19557step3 raw19557step3Labels = mixedMoment B raw19557step4 raw19557step4Labels := by
      have ha : raw19557step4 = raw19557step3 := by apply Matrix.ext; unfold raw19557step4 raw19557step3; decide +kernel
      have hl : raw19557step3Labels = labelEmbedding10 ∘ raw19557step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19557step3 raw19557step3Labels raw19557step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

def raw19558 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19558step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19558step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19558step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19558step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw19558step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19558step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19558step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19558step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19558step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19558 raw19558Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19558 raw19558Labels = mixedMoment B raw19558step0 raw19558step0Labels := by
      have hz : ∀ j, raw19558 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19558step0 = (fun i j => raw19558 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19558step0 raw19558; decide +kernel
      have hl : raw19558step0Labels = raw19558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19558 raw19558Labels permutation434 hz
    mixedMoment B raw19558step0 raw19558step0Labels = mixedMoment B raw19558step1 raw19558step1Labels := by
      have hz : ∀ j, raw19558step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19558step1 = (fun i j => raw19558step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19558step1 raw19558step0; decide +kernel
      have hl : raw19558step1Labels = raw19558step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19558step0 raw19558step0Labels permutation80 hz
    mixedMoment B raw19558step1 raw19558step1Labels = mixedMoment B raw19558step2 raw19558step2Labels := by
      have hz : ∀ j, raw19558step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19558step2 = (fun i j => raw19558step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19558step2 raw19558step1; decide +kernel
      have hl : raw19558step2Labels = raw19558step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19558step1 raw19558step1Labels permutation14 hz
    mixedMoment B raw19558step2 raw19558step2Labels = mixedMoment B raw19558step3 raw19558step3Labels := by
      have ha : raw19558step3 = (fun i j => raw19558step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19558step3 raw19558step2; decide +kernel
      have hl : raw19558step3Labels = raw19558step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19558step2 raw19558step2Labels permutation2 permutation7
    mixedMoment B raw19558step3 raw19558step3Labels = mixedMoment B raw19558step4 raw19558step4Labels := by
      have ha : raw19558step4 = raw19558step3 := by apply Matrix.ext; unfold raw19558step4 raw19558step3; decide +kernel
      have hl : raw19558step3Labels = labelEmbedding10 ∘ raw19558step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19558step3 raw19558step3Labels raw19558step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

def raw19559 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19559step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19559step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19559step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19559step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-3, -1, 4]]
def raw19559step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19559step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![3, 1, -4], ![-3, -1, 4]]
def raw19559step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19559step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 1, 3], ![4, -1, -3]]
def raw19559step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19559step5 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 1, 3], ![4, -1, -3]]
def raw19559step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19559 raw19559Labels = mixedMoment B node4512 node4512Labels := by
  calc
    mixedMoment B raw19559 raw19559Labels = mixedMoment B raw19559step0 raw19559step0Labels := by
      have hz : ∀ j, raw19559 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19559step0 = (fun i j => raw19559 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19559step0 raw19559; decide +kernel
      have hl : raw19559step0Labels = raw19559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19559 raw19559Labels permutation520 hz
    mixedMoment B raw19559step0 raw19559step0Labels = mixedMoment B raw19559step1 raw19559step1Labels := by
      have hz : ∀ j, raw19559step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19559step1 = (fun i j => raw19559step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19559step1 raw19559step0; decide +kernel
      have hl : raw19559step1Labels = raw19559step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19559step0 raw19559step0Labels permutation104 hz
    mixedMoment B raw19559step1 raw19559step1Labels = mixedMoment B raw19559step2 raw19559step2Labels := by
      have hz : ∀ j, raw19559step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19559step2 = (fun i j => raw19559step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19559step2 raw19559step1; decide +kernel
      have hl : raw19559step2Labels = raw19559step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19559step1 raw19559step1Labels permutation20 hz
    mixedMoment B raw19559step2 raw19559step2Labels = mixedMoment B raw19559step3 raw19559step3Labels := by
      have hz : ∀ j, raw19559step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19559step3 = (fun i j => raw19559step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19559step3 raw19559step2; decide +kernel
      have hl : raw19559step3Labels = raw19559step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19559step2 raw19559step2Labels permutation4 hz
    mixedMoment B raw19559step3 raw19559step3Labels = mixedMoment B raw19559step4 raw19559step4Labels := by
      have ha : raw19559step4 = (fun i j => raw19559step3 (permutation0 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19559step4 raw19559step3; decide +kernel
      have hl : raw19559step4Labels = raw19559step3Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19559step3 raw19559step3Labels permutation0 permutation7
    mixedMoment B raw19559step4 raw19559step4Labels = mixedMoment B raw19559step5 raw19559step5Labels := by
      have ha : raw19559step5 = raw19559step4 := by apply Matrix.ext; unfold raw19559step5 raw19559step4; decide +kernel
      have hl : raw19559step4Labels = labelEmbedding10 ∘ raw19559step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19559step4 raw19559step4Labels raw19559step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4512 node4512Labels := by rfl

def raw19560 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19560step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19560step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19560step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19560step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, -2, 4]]
def raw19560step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19560step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19560step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19560step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19560step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19560 raw19560Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19560 raw19560Labels = mixedMoment B raw19560step0 raw19560step0Labels := by
      have hz : ∀ j, raw19560 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19560step0 = (fun i j => raw19560 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19560step0 raw19560; decide +kernel
      have hl : raw19560step0Labels = raw19560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19560 raw19560Labels permutation520 hz
    mixedMoment B raw19560step0 raw19560step0Labels = mixedMoment B raw19560step1 raw19560step1Labels := by
      have hz : ∀ j, raw19560step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19560step1 = (fun i j => raw19560step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19560step1 raw19560step0; decide +kernel
      have hl : raw19560step1Labels = raw19560step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19560step0 raw19560step0Labels permutation104 hz
    mixedMoment B raw19560step1 raw19560step1Labels = mixedMoment B raw19560step2 raw19560step2Labels := by
      have hz : ∀ j, raw19560step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19560step2 = (fun i j => raw19560step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19560step2 raw19560step1; decide +kernel
      have hl : raw19560step2Labels = raw19560step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19560step1 raw19560step1Labels permutation20 hz
    mixedMoment B raw19560step2 raw19560step2Labels = mixedMoment B raw19560step3 raw19560step3Labels := by
      have ha : raw19560step3 = (fun i j => raw19560step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19560step3 raw19560step2; decide +kernel
      have hl : raw19560step3Labels = raw19560step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19560step2 raw19560step2Labels permutation2 permutation6
    mixedMoment B raw19560step3 raw19560step3Labels = mixedMoment B raw19560step4 raw19560step4Labels := by
      have ha : raw19560step4 = raw19560step3 := by apply Matrix.ext; unfold raw19560step4 raw19560step3; decide +kernel
      have hl : raw19560step3Labels = labelEmbedding9 ∘ raw19560step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19560step3 raw19560step3Labels raw19560step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

def raw19561 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19561Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19561step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19561step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19561step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19561step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19561step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19561step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19561 raw19561Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw19561 raw19561Labels = mixedMoment B raw19561step0 raw19561step0Labels := by
      have hz : ∀ j, raw19561 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19561step0 = (fun i j => raw19561 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19561step0 raw19561; decide +kernel
      have hl : raw19561step0Labels = raw19561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19561 raw19561Labels permutation520 hz
    mixedMoment B raw19561step0 raw19561step0Labels = mixedMoment B raw19561step1 raw19561step1Labels := by
      have hz : ∀ j, raw19561step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19561step1 = (fun i j => raw19561step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19561step1 raw19561step0; decide +kernel
      have hl : raw19561step1Labels = raw19561step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19561step0 raw19561step0Labels permutation104 hz
    mixedMoment B raw19561step1 raw19561step1Labels = mixedMoment B raw19561step2 raw19561step2Labels := by
      have ha : raw19561step2 = (fun i j => raw19561step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19561step2 raw19561step1; decide +kernel
      have hl : raw19561step2Labels = raw19561step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19561step1 raw19561step1Labels permutation10 permutation6
    mixedMoment B raw19561step2 raw19561step2Labels = mixedMoment B raw19561step3 raw19561step3Labels := by
      have ha : raw19561step3 = raw19561step2 := by apply Matrix.ext; unfold raw19561step3 raw19561step2; decide +kernel
      have hl : raw19561step2Labels = labelEmbedding9 ∘ raw19561step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19561step2 raw19561step2Labels raw19561step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4594 node4594Labels := by rfl

def raw19562 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19562step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19562step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19562step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19562step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19562step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19562 raw19562Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw19562 raw19562Labels = mixedMoment B raw19562step0 raw19562step0Labels := by
      have hz : ∀ j, raw19562 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19562step0 = (fun i j => raw19562 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19562step0 raw19562; decide +kernel
      have hl : raw19562step0Labels = raw19562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19562 raw19562Labels permutation520 hz
    mixedMoment B raw19562step0 raw19562step0Labels = mixedMoment B raw19562step1 raw19562step1Labels := by
      have hz : ∀ j, raw19562step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19562step1 = (fun i j => raw19562step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19562step1 raw19562step0; decide +kernel
      have hl : raw19562step1Labels = raw19562step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19562step0 raw19562step0Labels permutation80 hz
    mixedMoment B raw19562step1 raw19562step1Labels = mixedMoment B raw19562step2 raw19562step2Labels := by
      have ha : raw19562step2 = (fun i j => raw19562step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19562step2 raw19562step1; decide +kernel
      have hl : raw19562step2Labels = raw19562step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19562step1 raw19562step1Labels permutation10 permutation6
    mixedMoment B raw19562step2 raw19562step2Labels = mixedMoment B raw19562step3 raw19562step3Labels := by
      have ha : raw19562step3 = raw19562step2 := by apply Matrix.ext; unfold raw19562step3 raw19562step2; decide +kernel
      have hl : raw19562step2Labels = labelEmbedding9 ∘ raw19562step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19562step2 raw19562step2Labels raw19562step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4594 node4594Labels := by rfl

def raw19563 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19563step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19563step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19563step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19563step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19563step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19563step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19563 raw19563Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw19563 raw19563Labels = mixedMoment B raw19563step0 raw19563step0Labels := by
      have hz : ∀ j, raw19563 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19563step0 = (fun i j => raw19563 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19563step0 raw19563; decide +kernel
      have hl : raw19563step0Labels = raw19563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19563 raw19563Labels permutation434 hz
    mixedMoment B raw19563step0 raw19563step0Labels = mixedMoment B raw19563step1 raw19563step1Labels := by
      have hz : ∀ j, raw19563step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19563step1 = (fun i j => raw19563step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19563step1 raw19563step0; decide +kernel
      have hl : raw19563step1Labels = raw19563step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19563step0 raw19563step0Labels permutation80 hz
    mixedMoment B raw19563step1 raw19563step1Labels = mixedMoment B raw19563step2 raw19563step2Labels := by
      have ha : raw19563step2 = (fun i j => raw19563step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19563step2 raw19563step1; decide +kernel
      have hl : raw19563step2Labels = raw19563step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19563step1 raw19563step1Labels permutation10 permutation6
    mixedMoment B raw19563step2 raw19563step2Labels = mixedMoment B raw19563step3 raw19563step3Labels := by
      have ha : raw19563step3 = raw19563step2 := by apply Matrix.ext; unfold raw19563step3 raw19563step2; decide +kernel
      have hl : raw19563step2Labels = labelEmbedding9 ∘ raw19563step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19563step2 raw19563step2Labels raw19563step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4594 node4594Labels := by rfl

def raw19564 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19564step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19564step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19564step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, -1, 4]]
def raw19564step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19564step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw19564step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19564step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19564step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19564step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19564step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19564 raw19564Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19564 raw19564Labels = mixedMoment B raw19564step0 raw19564step0Labels := by
      have hz : ∀ j, raw19564 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19564step0 = (fun i j => raw19564 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19564step0 raw19564; decide +kernel
      have hl : raw19564step0Labels = raw19564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19564 raw19564Labels permutation520 hz
    mixedMoment B raw19564step0 raw19564step0Labels = mixedMoment B raw19564step1 raw19564step1Labels := by
      have hz : ∀ j, raw19564step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19564step1 = (fun i j => raw19564step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19564step1 raw19564step0; decide +kernel
      have hl : raw19564step1Labels = raw19564step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19564step0 raw19564step0Labels permutation104 hz
    mixedMoment B raw19564step1 raw19564step1Labels = mixedMoment B raw19564step2 raw19564step2Labels := by
      have hz : ∀ j, raw19564step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19564step2 = (fun i j => raw19564step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19564step2 raw19564step1; decide +kernel
      have hl : raw19564step2Labels = raw19564step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19564step1 raw19564step1Labels permutation20 hz
    mixedMoment B raw19564step2 raw19564step2Labels = mixedMoment B raw19564step3 raw19564step3Labels := by
      have ha : raw19564step3 = (fun i j => raw19564step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19564step3 raw19564step2; decide +kernel
      have hl : raw19564step3Labels = raw19564step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19564step2 raw19564step2Labels permutation7 permutation7
    mixedMoment B raw19564step3 raw19564step3Labels = mixedMoment B raw19564step4 raw19564step4Labels := by
      have ha : raw19564step4 = -raw19564step3 := by apply Matrix.ext; change ∀ i j, raw19564step4 i j = -(raw19564step3 i j); unfold raw19564step4 raw19564step3; decide +kernel
      have hl : raw19564step4Labels = raw19564step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19564step4 raw19564step4Labels = mixedMoment B raw19564step5 raw19564step5Labels := by
      have ha : raw19564step5 = raw19564step4 := by apply Matrix.ext; unfold raw19564step5 raw19564step4; decide +kernel
      have hl : raw19564step4Labels = labelEmbedding10 ∘ raw19564step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19564step4 raw19564step4Labels raw19564step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

def raw19565 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19565step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19565step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19565step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, -2, 4]]
def raw19565step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19565step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19565step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19565step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19565step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19565 raw19565Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19565 raw19565Labels = mixedMoment B raw19565step0 raw19565step0Labels := by
      have hz : ∀ j, raw19565 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19565step0 = (fun i j => raw19565 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19565step0 raw19565; decide +kernel
      have hl : raw19565step0Labels = raw19565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19565 raw19565Labels permutation520 hz
    mixedMoment B raw19565step0 raw19565step0Labels = mixedMoment B raw19565step1 raw19565step1Labels := by
      have hz : ∀ j, raw19565step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19565step1 = (fun i j => raw19565step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19565step1 raw19565step0; decide +kernel
      have hl : raw19565step1Labels = raw19565step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19565step0 raw19565step0Labels permutation104 hz
    mixedMoment B raw19565step1 raw19565step1Labels = mixedMoment B raw19565step2 raw19565step2Labels := by
      have hz : ∀ j, raw19565step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19565step2 = (fun i j => raw19565step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19565step2 raw19565step1; decide +kernel
      have hl : raw19565step2Labels = raw19565step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19565step1 raw19565step1Labels permutation14 hz
    mixedMoment B raw19565step2 raw19565step2Labels = mixedMoment B raw19565step3 raw19565step3Labels := by
      have ha : raw19565step3 = (fun i j => raw19565step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19565step3 raw19565step2; decide +kernel
      have hl : raw19565step3Labels = raw19565step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19565step2 raw19565step2Labels permutation2 permutation6
    mixedMoment B raw19565step3 raw19565step3Labels = mixedMoment B raw19565step4 raw19565step4Labels := by
      have ha : raw19565step4 = raw19565step3 := by apply Matrix.ext; unfold raw19565step4 raw19565step3; decide +kernel
      have hl : raw19565step3Labels = labelEmbedding9 ∘ raw19565step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19565step3 raw19565step3Labels raw19565step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

def raw19566 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19566step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19566step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19566step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19566step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19566step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19566 raw19566Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw19566 raw19566Labels = mixedMoment B raw19566step0 raw19566step0Labels := by
      have hz : ∀ j, raw19566 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19566step0 = (fun i j => raw19566 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19566step0 raw19566; decide +kernel
      have hl : raw19566step0Labels = raw19566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19566 raw19566Labels permutation520 hz
    mixedMoment B raw19566step0 raw19566step0Labels = mixedMoment B raw19566step1 raw19566step1Labels := by
      have hz : ∀ j, raw19566step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19566step1 = (fun i j => raw19566step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19566step1 raw19566step0; decide +kernel
      have hl : raw19566step1Labels = raw19566step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19566step0 raw19566step0Labels permutation104 hz
    mixedMoment B raw19566step1 raw19566step1Labels = mixedMoment B raw19566step2 raw19566step2Labels := by
      have ha : raw19566step2 = (fun i j => raw19566step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19566step2 raw19566step1; decide +kernel
      have hl : raw19566step2Labels = raw19566step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19566step1 raw19566step1Labels permutation8 permutation6
    mixedMoment B raw19566step2 raw19566step2Labels = mixedMoment B raw19566step3 raw19566step3Labels := by
      have ha : raw19566step3 = raw19566step2 := by apply Matrix.ext; unfold raw19566step3 raw19566step2; decide +kernel
      have hl : raw19566step2Labels = labelEmbedding9 ∘ raw19566step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19566step2 raw19566step2Labels raw19566step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4594 node4594Labels := by rfl

def raw19567 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19567step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19567step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19567step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19567step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19567step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19567 raw19567Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw19567 raw19567Labels = mixedMoment B raw19567step0 raw19567step0Labels := by
      have hz : ∀ j, raw19567 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19567step0 = (fun i j => raw19567 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19567step0 raw19567; decide +kernel
      have hl : raw19567step0Labels = raw19567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19567 raw19567Labels permutation520 hz
    mixedMoment B raw19567step0 raw19567step0Labels = mixedMoment B raw19567step1 raw19567step1Labels := by
      have hz : ∀ j, raw19567step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19567step1 = (fun i j => raw19567step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19567step1 raw19567step0; decide +kernel
      have hl : raw19567step1Labels = raw19567step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19567step0 raw19567step0Labels permutation56 hz
    mixedMoment B raw19567step1 raw19567step1Labels = mixedMoment B raw19567step2 raw19567step2Labels := by
      have ha : raw19567step2 = (fun i j => raw19567step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19567step2 raw19567step1; decide +kernel
      have hl : raw19567step2Labels = raw19567step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19567step1 raw19567step1Labels permutation10 permutation6
    mixedMoment B raw19567step2 raw19567step2Labels = mixedMoment B raw19567step3 raw19567step3Labels := by
      have ha : raw19567step3 = raw19567step2 := by apply Matrix.ext; unfold raw19567step3 raw19567step2; decide +kernel
      have hl : raw19567step2Labels = labelEmbedding9 ∘ raw19567step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19567step2 raw19567step2Labels raw19567step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4594 node4594Labels := by rfl

def raw19568 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19568step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19568step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19568step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19568step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19568step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19568step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19568step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19568 raw19568Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw19568 raw19568Labels = mixedMoment B raw19568step0 raw19568step0Labels := by
      have hz : ∀ j, raw19568 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19568step0 = (fun i j => raw19568 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19568step0 raw19568; decide +kernel
      have hl : raw19568step0Labels = raw19568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19568 raw19568Labels permutation434 hz
    mixedMoment B raw19568step0 raw19568step0Labels = mixedMoment B raw19568step1 raw19568step1Labels := by
      have hz : ∀ j, raw19568step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19568step1 = (fun i j => raw19568step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19568step1 raw19568step0; decide +kernel
      have hl : raw19568step1Labels = raw19568step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19568step0 raw19568step0Labels permutation56 hz
    mixedMoment B raw19568step1 raw19568step1Labels = mixedMoment B raw19568step2 raw19568step2Labels := by
      have ha : raw19568step2 = (fun i j => raw19568step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19568step2 raw19568step1; decide +kernel
      have hl : raw19568step2Labels = raw19568step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19568step1 raw19568step1Labels permutation10 permutation6
    mixedMoment B raw19568step2 raw19568step2Labels = mixedMoment B raw19568step3 raw19568step3Labels := by
      have ha : raw19568step3 = raw19568step2 := by apply Matrix.ext; unfold raw19568step3 raw19568step2; decide +kernel
      have hl : raw19568step2Labels = labelEmbedding9 ∘ raw19568step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19568step2 raw19568step2Labels raw19568step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4594 node4594Labels := by rfl

def raw19569 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19569step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19569step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19569step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, -1, 4]]
def raw19569step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19569step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw19569step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19569step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19569step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19569step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19569step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19569 raw19569Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19569 raw19569Labels = mixedMoment B raw19569step0 raw19569step0Labels := by
      have hz : ∀ j, raw19569 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19569step0 = (fun i j => raw19569 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19569step0 raw19569; decide +kernel
      have hl : raw19569step0Labels = raw19569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19569 raw19569Labels permutation520 hz
    mixedMoment B raw19569step0 raw19569step0Labels = mixedMoment B raw19569step1 raw19569step1Labels := by
      have hz : ∀ j, raw19569step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19569step1 = (fun i j => raw19569step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19569step1 raw19569step0; decide +kernel
      have hl : raw19569step1Labels = raw19569step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19569step0 raw19569step0Labels permutation104 hz
    mixedMoment B raw19569step1 raw19569step1Labels = mixedMoment B raw19569step2 raw19569step2Labels := by
      have hz : ∀ j, raw19569step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19569step2 = (fun i j => raw19569step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19569step2 raw19569step1; decide +kernel
      have hl : raw19569step2Labels = raw19569step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19569step1 raw19569step1Labels permutation14 hz
    mixedMoment B raw19569step2 raw19569step2Labels = mixedMoment B raw19569step3 raw19569step3Labels := by
      have ha : raw19569step3 = (fun i j => raw19569step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19569step3 raw19569step2; decide +kernel
      have hl : raw19569step3Labels = raw19569step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19569step2 raw19569step2Labels permutation7 permutation7
    mixedMoment B raw19569step3 raw19569step3Labels = mixedMoment B raw19569step4 raw19569step4Labels := by
      have ha : raw19569step4 = -raw19569step3 := by apply Matrix.ext; change ∀ i j, raw19569step4 i j = -(raw19569step3 i j); unfold raw19569step4 raw19569step3; decide +kernel
      have hl : raw19569step4Labels = raw19569step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19569step4 raw19569step4Labels = mixedMoment B raw19569step5 raw19569step5Labels := by
      have ha : raw19569step5 = raw19569step4 := by apply Matrix.ext; unfold raw19569step5 raw19569step4; decide +kernel
      have hl : raw19569step4Labels = labelEmbedding10 ∘ raw19569step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19569step4 raw19569step4Labels raw19569step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

def raw19570 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19570step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19570step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19570step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19570step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, -2, 4]]
def raw19570step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19570step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19570step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19570step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19570step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19570 raw19570Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19570 raw19570Labels = mixedMoment B raw19570step0 raw19570step0Labels := by
      have hz : ∀ j, raw19570 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19570step0 = (fun i j => raw19570 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19570step0 raw19570; decide +kernel
      have hl : raw19570step0Labels = raw19570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19570 raw19570Labels permutation520 hz
    mixedMoment B raw19570step0 raw19570step0Labels = mixedMoment B raw19570step1 raw19570step1Labels := by
      have hz : ∀ j, raw19570step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19570step1 = (fun i j => raw19570step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19570step1 raw19570step0; decide +kernel
      have hl : raw19570step1Labels = raw19570step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19570step0 raw19570step0Labels permutation80 hz
    mixedMoment B raw19570step1 raw19570step1Labels = mixedMoment B raw19570step2 raw19570step2Labels := by
      have hz : ∀ j, raw19570step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19570step2 = (fun i j => raw19570step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19570step2 raw19570step1; decide +kernel
      have hl : raw19570step2Labels = raw19570step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19570step1 raw19570step1Labels permutation14 hz
    mixedMoment B raw19570step2 raw19570step2Labels = mixedMoment B raw19570step3 raw19570step3Labels := by
      have ha : raw19570step3 = (fun i j => raw19570step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19570step3 raw19570step2; decide +kernel
      have hl : raw19570step3Labels = raw19570step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19570step2 raw19570step2Labels permutation2 permutation6
    mixedMoment B raw19570step3 raw19570step3Labels = mixedMoment B raw19570step4 raw19570step4Labels := by
      have ha : raw19570step4 = raw19570step3 := by apply Matrix.ext; unfold raw19570step4 raw19570step3; decide +kernel
      have hl : raw19570step3Labels = labelEmbedding9 ∘ raw19570step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19570step3 raw19570step3Labels raw19570step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

def raw19571 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19571step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19571step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19571step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19571step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19571step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19571step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19571step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19571 raw19571Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw19571 raw19571Labels = mixedMoment B raw19571step0 raw19571step0Labels := by
      have hz : ∀ j, raw19571 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19571step0 = (fun i j => raw19571 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19571step0 raw19571; decide +kernel
      have hl : raw19571step0Labels = raw19571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19571 raw19571Labels permutation520 hz
    mixedMoment B raw19571step0 raw19571step0Labels = mixedMoment B raw19571step1 raw19571step1Labels := by
      have hz : ∀ j, raw19571step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19571step1 = (fun i j => raw19571step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19571step1 raw19571step0; decide +kernel
      have hl : raw19571step1Labels = raw19571step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19571step0 raw19571step0Labels permutation80 hz
    mixedMoment B raw19571step1 raw19571step1Labels = mixedMoment B raw19571step2 raw19571step2Labels := by
      have ha : raw19571step2 = (fun i j => raw19571step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19571step2 raw19571step1; decide +kernel
      have hl : raw19571step2Labels = raw19571step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19571step1 raw19571step1Labels permutation8 permutation6
    mixedMoment B raw19571step2 raw19571step2Labels = mixedMoment B raw19571step3 raw19571step3Labels := by
      have ha : raw19571step3 = raw19571step2 := by apply Matrix.ext; unfold raw19571step3 raw19571step2; decide +kernel
      have hl : raw19571step2Labels = labelEmbedding9 ∘ raw19571step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19571step2 raw19571step2Labels raw19571step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4594 node4594Labels := by rfl

def raw19572 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, -2, 4]]
def raw19572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19572step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19572step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19572step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19572step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19572step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19572step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19572step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19572 raw19572Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw19572 raw19572Labels = mixedMoment B raw19572step0 raw19572step0Labels := by
      have hz : ∀ j, raw19572 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19572step0 = (fun i j => raw19572 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19572step0 raw19572; decide +kernel
      have hl : raw19572step0Labels = raw19572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19572 raw19572Labels permutation520 hz
    mixedMoment B raw19572step0 raw19572step0Labels = mixedMoment B raw19572step1 raw19572step1Labels := by
      have hz : ∀ j, raw19572step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19572step1 = (fun i j => raw19572step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19572step1 raw19572step0; decide +kernel
      have hl : raw19572step1Labels = raw19572step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19572step0 raw19572step0Labels permutation56 hz
    mixedMoment B raw19572step1 raw19572step1Labels = mixedMoment B raw19572step2 raw19572step2Labels := by
      have ha : raw19572step2 = (fun i j => raw19572step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19572step2 raw19572step1; decide +kernel
      have hl : raw19572step2Labels = raw19572step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19572step1 raw19572step1Labels permutation8 permutation6
    mixedMoment B raw19572step2 raw19572step2Labels = mixedMoment B raw19572step3 raw19572step3Labels := by
      have ha : raw19572step3 = raw19572step2 := by apply Matrix.ext; unfold raw19572step3 raw19572step2; decide +kernel
      have hl : raw19572step2Labels = labelEmbedding9 ∘ raw19572step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19572step2 raw19572step2Labels raw19572step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4594 node4594Labels := by rfl

def raw19573 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw19573step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19573step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19573step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19573step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19573step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19573 raw19573Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw19573 raw19573Labels = mixedMoment B raw19573step0 raw19573step0Labels := by
      have hz : ∀ j, raw19573 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19573step0 = (fun i j => raw19573 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19573step0 raw19573; decide +kernel
      have hl : raw19573step0Labels = raw19573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19573 raw19573Labels permutation346 hz
    mixedMoment B raw19573step0 raw19573step0Labels = mixedMoment B raw19573step1 raw19573step1Labels := by
      have hz : ∀ j, raw19573step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19573step1 = (fun i j => raw19573step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19573step1 raw19573step0; decide +kernel
      have hl : raw19573step1Labels = raw19573step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19573step0 raw19573step0Labels permutation56 hz
    mixedMoment B raw19573step1 raw19573step1Labels = mixedMoment B raw19573step2 raw19573step2Labels := by
      have ha : raw19573step2 = (fun i j => raw19573step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19573step2 raw19573step1; decide +kernel
      have hl : raw19573step2Labels = raw19573step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19573step1 raw19573step1Labels permutation10 permutation6
    mixedMoment B raw19573step2 raw19573step2Labels = mixedMoment B raw19573step3 raw19573step3Labels := by
      have ha : raw19573step3 = raw19573step2 := by apply Matrix.ext; unfold raw19573step3 raw19573step2; decide +kernel
      have hl : raw19573step2Labels = labelEmbedding9 ∘ raw19573step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19573step2 raw19573step2Labels raw19573step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4594 node4594Labels := by rfl

def raw19574 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-3, -1, 4]]
def raw19574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19574step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19574step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19574step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19574step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, -1, 4]]
def raw19574step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19574step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw19574step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19574step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19574step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19574step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19574step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19574 raw19574Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19574 raw19574Labels = mixedMoment B raw19574step0 raw19574step0Labels := by
      have hz : ∀ j, raw19574 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19574step0 = (fun i j => raw19574 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19574step0 raw19574; decide +kernel
      have hl : raw19574step0Labels = raw19574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19574 raw19574Labels permutation520 hz
    mixedMoment B raw19574step0 raw19574step0Labels = mixedMoment B raw19574step1 raw19574step1Labels := by
      have hz : ∀ j, raw19574step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19574step1 = (fun i j => raw19574step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19574step1 raw19574step0; decide +kernel
      have hl : raw19574step1Labels = raw19574step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19574step0 raw19574step0Labels permutation80 hz
    mixedMoment B raw19574step1 raw19574step1Labels = mixedMoment B raw19574step2 raw19574step2Labels := by
      have hz : ∀ j, raw19574step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19574step2 = (fun i j => raw19574step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19574step2 raw19574step1; decide +kernel
      have hl : raw19574step2Labels = raw19574step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19574step1 raw19574step1Labels permutation14 hz
    mixedMoment B raw19574step2 raw19574step2Labels = mixedMoment B raw19574step3 raw19574step3Labels := by
      have ha : raw19574step3 = (fun i j => raw19574step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19574step3 raw19574step2; decide +kernel
      have hl : raw19574step3Labels = raw19574step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19574step2 raw19574step2Labels permutation7 permutation7
    mixedMoment B raw19574step3 raw19574step3Labels = mixedMoment B raw19574step4 raw19574step4Labels := by
      have ha : raw19574step4 = -raw19574step3 := by apply Matrix.ext; change ∀ i j, raw19574step4 i j = -(raw19574step3 i j); unfold raw19574step4 raw19574step3; decide +kernel
      have hl : raw19574step4Labels = raw19574step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19574step4 raw19574step4Labels = mixedMoment B raw19574step5 raw19574step5Labels := by
      have ha : raw19574step5 = raw19574step4 := by apply Matrix.ext; unfold raw19574step5 raw19574step4; decide +kernel
      have hl : raw19574step4Labels = labelEmbedding10 ∘ raw19574step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19574step4 raw19574step4Labels raw19574step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

def raw19575 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19575step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19575step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19575step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, -2, 4]]
def raw19575step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19575step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19575step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19575step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19575step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19575 raw19575Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19575 raw19575Labels = mixedMoment B raw19575step0 raw19575step0Labels := by
      have hz : ∀ j, raw19575 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19575step0 = (fun i j => raw19575 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19575step0 raw19575; decide +kernel
      have hl : raw19575step0Labels = raw19575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19575 raw19575Labels permutation434 hz
    mixedMoment B raw19575step0 raw19575step0Labels = mixedMoment B raw19575step1 raw19575step1Labels := by
      have hz : ∀ j, raw19575step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19575step1 = (fun i j => raw19575step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19575step1 raw19575step0; decide +kernel
      have hl : raw19575step1Labels = raw19575step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19575step0 raw19575step0Labels permutation80 hz
    mixedMoment B raw19575step1 raw19575step1Labels = mixedMoment B raw19575step2 raw19575step2Labels := by
      have hz : ∀ j, raw19575step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19575step2 = (fun i j => raw19575step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19575step2 raw19575step1; decide +kernel
      have hl : raw19575step2Labels = raw19575step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19575step1 raw19575step1Labels permutation14 hz
    mixedMoment B raw19575step2 raw19575step2Labels = mixedMoment B raw19575step3 raw19575step3Labels := by
      have ha : raw19575step3 = (fun i j => raw19575step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19575step3 raw19575step2; decide +kernel
      have hl : raw19575step3Labels = raw19575step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19575step2 raw19575step2Labels permutation2 permutation6
    mixedMoment B raw19575step3 raw19575step3Labels = mixedMoment B raw19575step4 raw19575step4Labels := by
      have ha : raw19575step4 = raw19575step3 := by apply Matrix.ext; unfold raw19575step4 raw19575step3; decide +kernel
      have hl : raw19575step3Labels = labelEmbedding9 ∘ raw19575step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19575step3 raw19575step3Labels raw19575step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

def raw19576 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19576step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19576step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19576step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19576step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19576step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19576step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19576step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19576 raw19576Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw19576 raw19576Labels = mixedMoment B raw19576step0 raw19576step0Labels := by
      have hz : ∀ j, raw19576 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19576step0 = (fun i j => raw19576 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19576step0 raw19576; decide +kernel
      have hl : raw19576step0Labels = raw19576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19576 raw19576Labels permutation434 hz
    mixedMoment B raw19576step0 raw19576step0Labels = mixedMoment B raw19576step1 raw19576step1Labels := by
      have hz : ∀ j, raw19576step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19576step1 = (fun i j => raw19576step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19576step1 raw19576step0; decide +kernel
      have hl : raw19576step1Labels = raw19576step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19576step0 raw19576step0Labels permutation80 hz
    mixedMoment B raw19576step1 raw19576step1Labels = mixedMoment B raw19576step2 raw19576step2Labels := by
      have ha : raw19576step2 = (fun i j => raw19576step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19576step2 raw19576step1; decide +kernel
      have hl : raw19576step2Labels = raw19576step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19576step1 raw19576step1Labels permutation8 permutation6
    mixedMoment B raw19576step2 raw19576step2Labels = mixedMoment B raw19576step3 raw19576step3Labels := by
      have ha : raw19576step3 = raw19576step2 := by apply Matrix.ext; unfold raw19576step3 raw19576step2; decide +kernel
      have hl : raw19576step2Labels = labelEmbedding9 ∘ raw19576step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19576step2 raw19576step2Labels raw19576step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4594 node4594Labels := by rfl

def raw19577 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19577step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19577step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19577step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19577step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19577step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19577step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19577step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19577 raw19577Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw19577 raw19577Labels = mixedMoment B raw19577step0 raw19577step0Labels := by
      have hz : ∀ j, raw19577 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19577step0 = (fun i j => raw19577 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19577step0 raw19577; decide +kernel
      have hl : raw19577step0Labels = raw19577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19577 raw19577Labels permutation434 hz
    mixedMoment B raw19577step0 raw19577step0Labels = mixedMoment B raw19577step1 raw19577step1Labels := by
      have hz : ∀ j, raw19577step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19577step1 = (fun i j => raw19577step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19577step1 raw19577step0; decide +kernel
      have hl : raw19577step1Labels = raw19577step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19577step0 raw19577step0Labels permutation56 hz
    mixedMoment B raw19577step1 raw19577step1Labels = mixedMoment B raw19577step2 raw19577step2Labels := by
      have ha : raw19577step2 = (fun i j => raw19577step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19577step2 raw19577step1; decide +kernel
      have hl : raw19577step2Labels = raw19577step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19577step1 raw19577step1Labels permutation8 permutation6
    mixedMoment B raw19577step2 raw19577step2Labels = mixedMoment B raw19577step3 raw19577step3Labels := by
      have ha : raw19577step3 = raw19577step2 := by apply Matrix.ext; unfold raw19577step3 raw19577step2; decide +kernel
      have hl : raw19577step2Labels = labelEmbedding9 ∘ raw19577step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19577step2 raw19577step2Labels raw19577step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4594 node4594Labels := by rfl

def raw19578 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19578step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, -2, 4]]
def raw19578step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19578step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19578step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19578step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![4, -2, -2]]
def raw19578step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19578 raw19578Labels = mixedMoment B node4594 node4594Labels := by
  calc
    mixedMoment B raw19578 raw19578Labels = mixedMoment B raw19578step0 raw19578step0Labels := by
      have hz : ∀ j, raw19578 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19578step0 = (fun i j => raw19578 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19578step0 raw19578; decide +kernel
      have hl : raw19578step0Labels = raw19578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19578 raw19578Labels permutation346 hz
    mixedMoment B raw19578step0 raw19578step0Labels = mixedMoment B raw19578step1 raw19578step1Labels := by
      have hz : ∀ j, raw19578step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19578step1 = (fun i j => raw19578step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19578step1 raw19578step0; decide +kernel
      have hl : raw19578step1Labels = raw19578step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19578step0 raw19578step0Labels permutation56 hz
    mixedMoment B raw19578step1 raw19578step1Labels = mixedMoment B raw19578step2 raw19578step2Labels := by
      have ha : raw19578step2 = (fun i j => raw19578step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19578step2 raw19578step1; decide +kernel
      have hl : raw19578step2Labels = raw19578step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19578step1 raw19578step1Labels permutation8 permutation6
    mixedMoment B raw19578step2 raw19578step2Labels = mixedMoment B raw19578step3 raw19578step3Labels := by
      have ha : raw19578step3 = raw19578step2 := by apply Matrix.ext; unfold raw19578step3 raw19578step2; decide +kernel
      have hl : raw19578step2Labels = labelEmbedding9 ∘ raw19578step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19578step2 raw19578step2Labels raw19578step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4594 node4594Labels := by rfl

def raw19579 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19579step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-3, -1, 4]]
def raw19579step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19579step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-3, -1, 4]]
def raw19579step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19579step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw19579step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19579step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19579step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19579step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19579step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19579 raw19579Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19579 raw19579Labels = mixedMoment B raw19579step0 raw19579step0Labels := by
      have hz : ∀ j, raw19579 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19579step0 = (fun i j => raw19579 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19579step0 raw19579; decide +kernel
      have hl : raw19579step0Labels = raw19579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19579 raw19579Labels permutation434 hz
    mixedMoment B raw19579step0 raw19579step0Labels = mixedMoment B raw19579step1 raw19579step1Labels := by
      have hz : ∀ j, raw19579step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19579step1 = (fun i j => raw19579step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19579step1 raw19579step0; decide +kernel
      have hl : raw19579step1Labels = raw19579step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19579step0 raw19579step0Labels permutation80 hz
    mixedMoment B raw19579step1 raw19579step1Labels = mixedMoment B raw19579step2 raw19579step2Labels := by
      have hz : ∀ j, raw19579step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19579step2 = (fun i j => raw19579step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19579step2 raw19579step1; decide +kernel
      have hl : raw19579step2Labels = raw19579step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19579step1 raw19579step1Labels permutation14 hz
    mixedMoment B raw19579step2 raw19579step2Labels = mixedMoment B raw19579step3 raw19579step3Labels := by
      have ha : raw19579step3 = (fun i j => raw19579step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19579step3 raw19579step2; decide +kernel
      have hl : raw19579step3Labels = raw19579step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19579step2 raw19579step2Labels permutation7 permutation7
    mixedMoment B raw19579step3 raw19579step3Labels = mixedMoment B raw19579step4 raw19579step4Labels := by
      have ha : raw19579step4 = -raw19579step3 := by apply Matrix.ext; change ∀ i j, raw19579step4 i j = -(raw19579step3 i j); unfold raw19579step4 raw19579step3; decide +kernel
      have hl : raw19579step4Labels = raw19579step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19579step4 raw19579step4Labels = mixedMoment B raw19579step5 raw19579step5Labels := by
      have ha : raw19579step5 = raw19579step4 := by apply Matrix.ext; unfold raw19579step5 raw19579step4; decide +kernel
      have hl : raw19579step4Labels = labelEmbedding10 ∘ raw19579step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19579step4 raw19579step4Labels raw19579step5Labels labelEmbedding10 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

def raw19580 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19580step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19580step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19580step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19580step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, -3, 4]]
def raw19580step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19580step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![1, 3, -4], ![-1, -3, 4]]
def raw19580step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19580step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 1, 3], ![4, -1, -3]]
def raw19580step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19580step5 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 1, 3], ![4, -1, -3]]
def raw19580step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19580 raw19580Labels = mixedMoment B node4512 node4512Labels := by
  calc
    mixedMoment B raw19580 raw19580Labels = mixedMoment B raw19580step0 raw19580step0Labels := by
      have hz : ∀ j, raw19580 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19580step0 = (fun i j => raw19580 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19580step0 raw19580; decide +kernel
      have hl : raw19580step0Labels = raw19580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19580 raw19580Labels permutation520 hz
    mixedMoment B raw19580step0 raw19580step0Labels = mixedMoment B raw19580step1 raw19580step1Labels := by
      have hz : ∀ j, raw19580step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19580step1 = (fun i j => raw19580step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19580step1 raw19580step0; decide +kernel
      have hl : raw19580step1Labels = raw19580step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19580step0 raw19580step0Labels permutation104 hz
    mixedMoment B raw19580step1 raw19580step1Labels = mixedMoment B raw19580step2 raw19580step2Labels := by
      have hz : ∀ j, raw19580step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19580step2 = (fun i j => raw19580step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19580step2 raw19580step1; decide +kernel
      have hl : raw19580step2Labels = raw19580step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19580step1 raw19580step1Labels permutation20 hz
    mixedMoment B raw19580step2 raw19580step2Labels = mixedMoment B raw19580step3 raw19580step3Labels := by
      have hz : ∀ j, raw19580step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19580step3 = (fun i j => raw19580step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19580step3 raw19580step2; decide +kernel
      have hl : raw19580step3Labels = raw19580step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19580step2 raw19580step2Labels permutation4 hz
    mixedMoment B raw19580step3 raw19580step3Labels = mixedMoment B raw19580step4 raw19580step4Labels := by
      have ha : raw19580step4 = (fun i j => raw19580step3 (permutation0 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19580step4 raw19580step3; decide +kernel
      have hl : raw19580step4Labels = raw19580step3Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19580step3 raw19580step3Labels permutation0 permutation6
    mixedMoment B raw19580step4 raw19580step4Labels = mixedMoment B raw19580step5 raw19580step5Labels := by
      have ha : raw19580step5 = raw19580step4 := by apply Matrix.ext; unfold raw19580step5 raw19580step4; decide +kernel
      have hl : raw19580step4Labels = labelEmbedding9 ∘ raw19580step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19580step4 raw19580step4Labels raw19580step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4512 node4512Labels := by rfl

def raw19581 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19581step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19581step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -3, 4]]
def raw19581step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19581step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw19581step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19581step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19581step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19581step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19581step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19581 raw19581Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19581 raw19581Labels = mixedMoment B raw19581step0 raw19581step0Labels := by
      have hz : ∀ j, raw19581 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19581step0 = (fun i j => raw19581 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19581step0 raw19581; decide +kernel
      have hl : raw19581step0Labels = raw19581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19581 raw19581Labels permutation520 hz
    mixedMoment B raw19581step0 raw19581step0Labels = mixedMoment B raw19581step1 raw19581step1Labels := by
      have hz : ∀ j, raw19581step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19581step1 = (fun i j => raw19581step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19581step1 raw19581step0; decide +kernel
      have hl : raw19581step1Labels = raw19581step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19581step0 raw19581step0Labels permutation104 hz
    mixedMoment B raw19581step1 raw19581step1Labels = mixedMoment B raw19581step2 raw19581step2Labels := by
      have hz : ∀ j, raw19581step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19581step2 = (fun i j => raw19581step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19581step2 raw19581step1; decide +kernel
      have hl : raw19581step2Labels = raw19581step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19581step1 raw19581step1Labels permutation20 hz
    mixedMoment B raw19581step2 raw19581step2Labels = mixedMoment B raw19581step3 raw19581step3Labels := by
      have ha : raw19581step3 = (fun i j => raw19581step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19581step3 raw19581step2; decide +kernel
      have hl : raw19581step3Labels = raw19581step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19581step2 raw19581step2Labels permutation7 permutation6
    mixedMoment B raw19581step3 raw19581step3Labels = mixedMoment B raw19581step4 raw19581step4Labels := by
      have ha : raw19581step4 = -raw19581step3 := by apply Matrix.ext; change ∀ i j, raw19581step4 i j = -(raw19581step3 i j); unfold raw19581step4 raw19581step3; decide +kernel
      have hl : raw19581step4Labels = raw19581step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19581step4 raw19581step4Labels = mixedMoment B raw19581step5 raw19581step5Labels := by
      have ha : raw19581step5 = raw19581step4 := by apply Matrix.ext; unfold raw19581step5 raw19581step4; decide +kernel
      have hl : raw19581step4Labels = labelEmbedding9 ∘ raw19581step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19581step4 raw19581step4Labels raw19581step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

def raw19582 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19582step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19582step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19582step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19582step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -3, 4]]
def raw19582step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19582step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw19582step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19582step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19582step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19582step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19582step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19582 raw19582Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19582 raw19582Labels = mixedMoment B raw19582step0 raw19582step0Labels := by
      have hz : ∀ j, raw19582 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19582step0 = (fun i j => raw19582 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19582step0 raw19582; decide +kernel
      have hl : raw19582step0Labels = raw19582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19582 raw19582Labels permutation520 hz
    mixedMoment B raw19582step0 raw19582step0Labels = mixedMoment B raw19582step1 raw19582step1Labels := by
      have hz : ∀ j, raw19582step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19582step1 = (fun i j => raw19582step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19582step1 raw19582step0; decide +kernel
      have hl : raw19582step1Labels = raw19582step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19582step0 raw19582step0Labels permutation104 hz
    mixedMoment B raw19582step1 raw19582step1Labels = mixedMoment B raw19582step2 raw19582step2Labels := by
      have hz : ∀ j, raw19582step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19582step2 = (fun i j => raw19582step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19582step2 raw19582step1; decide +kernel
      have hl : raw19582step2Labels = raw19582step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19582step1 raw19582step1Labels permutation14 hz
    mixedMoment B raw19582step2 raw19582step2Labels = mixedMoment B raw19582step3 raw19582step3Labels := by
      have ha : raw19582step3 = (fun i j => raw19582step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19582step3 raw19582step2; decide +kernel
      have hl : raw19582step3Labels = raw19582step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19582step2 raw19582step2Labels permutation7 permutation6
    mixedMoment B raw19582step3 raw19582step3Labels = mixedMoment B raw19582step4 raw19582step4Labels := by
      have ha : raw19582step4 = -raw19582step3 := by apply Matrix.ext; change ∀ i j, raw19582step4 i j = -(raw19582step3 i j); unfold raw19582step4 raw19582step3; decide +kernel
      have hl : raw19582step4Labels = raw19582step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19582step4 raw19582step4Labels = mixedMoment B raw19582step5 raw19582step5Labels := by
      have ha : raw19582step5 = raw19582step4 := by apply Matrix.ext; unfold raw19582step5 raw19582step4; decide +kernel
      have hl : raw19582step4Labels = labelEmbedding9 ∘ raw19582step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19582step4 raw19582step4Labels raw19582step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

def raw19583 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19583step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19583step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, -3, 4]]
def raw19583step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19583step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw19583step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19583step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19583step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19583step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw19583step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19583 raw19583Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw19583 raw19583Labels = mixedMoment B raw19583step0 raw19583step0Labels := by
      have hz : ∀ j, raw19583 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19583step0 = (fun i j => raw19583 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19583step0 raw19583; decide +kernel
      have hl : raw19583step0Labels = raw19583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19583 raw19583Labels permutation520 hz
    mixedMoment B raw19583step0 raw19583step0Labels = mixedMoment B raw19583step1 raw19583step1Labels := by
      have hz : ∀ j, raw19583step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19583step1 = (fun i j => raw19583step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19583step1 raw19583step0; decide +kernel
      have hl : raw19583step1Labels = raw19583step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19583step0 raw19583step0Labels permutation80 hz
    mixedMoment B raw19583step1 raw19583step1Labels = mixedMoment B raw19583step2 raw19583step2Labels := by
      have hz : ∀ j, raw19583step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19583step2 = (fun i j => raw19583step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19583step2 raw19583step1; decide +kernel
      have hl : raw19583step2Labels = raw19583step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19583step1 raw19583step1Labels permutation14 hz
    mixedMoment B raw19583step2 raw19583step2Labels = mixedMoment B raw19583step3 raw19583step3Labels := by
      have ha : raw19583step3 = (fun i j => raw19583step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19583step3 raw19583step2; decide +kernel
      have hl : raw19583step3Labels = raw19583step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19583step2 raw19583step2Labels permutation7 permutation6
    mixedMoment B raw19583step3 raw19583step3Labels = mixedMoment B raw19583step4 raw19583step4Labels := by
      have ha : raw19583step4 = -raw19583step3 := by apply Matrix.ext; change ∀ i j, raw19583step4 i j = -(raw19583step3 i j); unfold raw19583step4 raw19583step3; decide +kernel
      have hl : raw19583step4Labels = raw19583step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19583step4 raw19583step4Labels = mixedMoment B raw19583step5 raw19583step5Labels := by
      have ha : raw19583step5 = raw19583step4 := by apply Matrix.ext; unfold raw19583step5 raw19583step4; decide +kernel
      have hl : raw19583step4Labels = labelEmbedding9 ∘ raw19583step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19583step4 raw19583step4Labels raw19583step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
