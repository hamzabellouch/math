import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw19840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![5, -1, -4]]
def raw19840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![5, -1, -4]]
def raw19840step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19840step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, -1, 2], ![5, -1, -4]]
def raw19840step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19840step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![5, -1, -4]]
def raw19840step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19840step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -1, -4], ![-1, -1, 2], ![-4, 2, 2]]
def raw19840step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19840step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def raw19840step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19840 raw19840Labels = mixedMoment B node564 node564Labels := by
  calc
    mixedMoment B raw19840 raw19840Labels = mixedMoment B raw19840step0 raw19840step0Labels := by
      have hz : ∀ j, raw19840 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19840step0 = (fun i j => raw19840 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19840step0 raw19840; decide +kernel
      have hl : raw19840step0Labels = raw19840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19840 raw19840Labels permutation434 hz
    mixedMoment B raw19840step0 raw19840step0Labels = mixedMoment B raw19840step1 raw19840step1Labels := by
      have hz : ∀ j, raw19840step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19840step1 = (fun i j => raw19840step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19840step1 raw19840step0; decide +kernel
      have hl : raw19840step1Labels = raw19840step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19840step0 raw19840step0Labels permutation80 hz
    mixedMoment B raw19840step1 raw19840step1Labels = mixedMoment B raw19840step2 raw19840step2Labels := by
      have hz : ∀ j, raw19840step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19840step2 = (fun i j => raw19840step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19840step2 raw19840step1; decide +kernel
      have hl : raw19840step2Labels = raw19840step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19840step1 raw19840step1Labels permutation14 hz
    mixedMoment B raw19840step2 raw19840step2Labels = mixedMoment B raw19840step3 raw19840step3Labels := by
      have ha : raw19840step3 = (fun i j => raw19840step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19840step3 raw19840step2; decide +kernel
      have hl : raw19840step3Labels = raw19840step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19840step2 raw19840step2Labels permutation7 permutation2
    mixedMoment B raw19840step3 raw19840step3Labels = mixedMoment B raw19840step4 raw19840step4Labels := by
      have ha : raw19840step4 = -raw19840step3 := by apply Matrix.ext; change ∀ i j, raw19840step4 i j = -(raw19840step3 i j); unfold raw19840step4 raw19840step3; decide +kernel
      have hl : raw19840step4Labels = raw19840step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node564 node564Labels := by rfl

def raw19841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 1, -4]]
def raw19841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 1, -4]]
def raw19841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19841step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -2, 2], ![3, 1, -4]]
def raw19841step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19841step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def raw19841step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19841 raw19841Labels = mixedMoment B node1186 node1186Labels := by
  calc
    mixedMoment B raw19841 raw19841Labels = mixedMoment B raw19841step0 raw19841step0Labels := by
      have hz : ∀ j, raw19841 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19841step0 = (fun i j => raw19841 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19841step0 raw19841; decide +kernel
      have hl : raw19841step0Labels = raw19841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19841 raw19841Labels permutation434 hz
    mixedMoment B raw19841step0 raw19841step0Labels = mixedMoment B raw19841step1 raw19841step1Labels := by
      have hz : ∀ j, raw19841step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19841step1 = (fun i j => raw19841step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19841step1 raw19841step0; decide +kernel
      have hl : raw19841step1Labels = raw19841step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19841step0 raw19841step0Labels permutation80 hz
    mixedMoment B raw19841step1 raw19841step1Labels = mixedMoment B raw19841step2 raw19841step2Labels := by
      have ha : raw19841step2 = (fun i j => raw19841step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19841step2 raw19841step1; decide +kernel
      have hl : raw19841step2Labels = raw19841step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19841step1 raw19841step1Labels permutation10 permutation2
    _ = mixedMoment B node1186 node1186Labels := by rfl

def raw19842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![3, 1, -4]]
def raw19842Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 1, -4]]
def raw19842step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19842step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -2, 2], ![3, 1, -4]]
def raw19842step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19842step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def raw19842step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19842 raw19842Labels = mixedMoment B node1186 node1186Labels := by
  calc
    mixedMoment B raw19842 raw19842Labels = mixedMoment B raw19842step0 raw19842step0Labels := by
      have hz : ∀ j, raw19842 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19842step0 = (fun i j => raw19842 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19842step0 raw19842; decide +kernel
      have hl : raw19842step0Labels = raw19842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19842 raw19842Labels permutation434 hz
    mixedMoment B raw19842step0 raw19842step0Labels = mixedMoment B raw19842step1 raw19842step1Labels := by
      have hz : ∀ j, raw19842step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19842step1 = (fun i j => raw19842step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19842step1 raw19842step0; decide +kernel
      have hl : raw19842step1Labels = raw19842step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19842step0 raw19842step0Labels permutation56 hz
    mixedMoment B raw19842step1 raw19842step1Labels = mixedMoment B raw19842step2 raw19842step2Labels := by
      have ha : raw19842step2 = (fun i j => raw19842step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19842step2 raw19842step1; decide +kernel
      have hl : raw19842step2Labels = raw19842step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19842step1 raw19842step1Labels permutation10 permutation2
    _ = mixedMoment B node1186 node1186Labels := by rfl

def raw19843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 1, -4]]
def raw19843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![3, 1, -4]]
def raw19843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19843step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -2, 2], ![3, 1, -4]]
def raw19843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19843step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def raw19843step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19843 raw19843Labels = mixedMoment B node1186 node1186Labels := by
  calc
    mixedMoment B raw19843 raw19843Labels = mixedMoment B raw19843step0 raw19843step0Labels := by
      have hz : ∀ j, raw19843 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19843step0 = (fun i j => raw19843 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19843step0 raw19843; decide +kernel
      have hl : raw19843step0Labels = raw19843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19843 raw19843Labels permutation346 hz
    mixedMoment B raw19843step0 raw19843step0Labels = mixedMoment B raw19843step1 raw19843step1Labels := by
      have hz : ∀ j, raw19843step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19843step1 = (fun i j => raw19843step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19843step1 raw19843step0; decide +kernel
      have hl : raw19843step1Labels = raw19843step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19843step0 raw19843step0Labels permutation56 hz
    mixedMoment B raw19843step1 raw19843step1Labels = mixedMoment B raw19843step2 raw19843step2Labels := by
      have ha : raw19843step2 = (fun i j => raw19843step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19843step2 raw19843step1; decide +kernel
      have hl : raw19843step2Labels = raw19843step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19843step1 raw19843step1Labels permutation10 permutation2
    _ = mixedMoment B node1186 node1186Labels := by rfl

def raw19844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 1, -4]]
def raw19844Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 1, -4]]
def raw19844step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19844step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -3, 2], ![3, 1, -4]]
def raw19844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19844step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![3, 1, -4]]
def raw19844step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19844 raw19844Labels = mixedMoment B node1289 node1289Labels := by
  calc
    mixedMoment B raw19844 raw19844Labels = mixedMoment B raw19844step0 raw19844step0Labels := by
      have hz : ∀ j, raw19844 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19844step0 = (fun i j => raw19844 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19844step0 raw19844; decide +kernel
      have hl : raw19844step0Labels = raw19844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19844 raw19844Labels permutation434 hz
    mixedMoment B raw19844step0 raw19844step0Labels = mixedMoment B raw19844step1 raw19844step1Labels := by
      have hz : ∀ j, raw19844step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19844step1 = (fun i j => raw19844step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19844step1 raw19844step0; decide +kernel
      have hl : raw19844step1Labels = raw19844step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19844step0 raw19844step0Labels permutation80 hz
    mixedMoment B raw19844step1 raw19844step1Labels = mixedMoment B raw19844step2 raw19844step2Labels := by
      have hz : ∀ j, raw19844step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19844step2 = (fun i j => raw19844step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19844step2 raw19844step1; decide +kernel
      have hl : raw19844step2Labels = raw19844step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19844step1 raw19844step1Labels permutation14 hz
    _ = mixedMoment B node1289 node1289Labels := by rfl

def raw19845 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw19845Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw19845step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19845step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw19845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19845step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -4, 4]]
def raw19845step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19845step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![2, -2, 0], ![2, 2, -4]]
def raw19845step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19845 raw19845Labels = mixedMoment B node862 node862Labels := by
  calc
    mixedMoment B raw19845 raw19845Labels = mixedMoment B raw19845step0 raw19845step0Labels := by
      have hz : ∀ j, raw19845 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19845step0 = (fun i j => raw19845 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19845step0 raw19845; decide +kernel
      have hl : raw19845step0Labels = raw19845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19845 raw19845Labels permutation434 hz
    mixedMoment B raw19845step0 raw19845step0Labels = mixedMoment B raw19845step1 raw19845step1Labels := by
      have hz : ∀ j, raw19845step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19845step1 = (fun i j => raw19845step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19845step1 raw19845step0; decide +kernel
      have hl : raw19845step1Labels = raw19845step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19845step0 raw19845step0Labels permutation80 hz
    mixedMoment B raw19845step1 raw19845step1Labels = mixedMoment B raw19845step2 raw19845step2Labels := by
      have hz : ∀ j, raw19845step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19845step2 = (fun i j => raw19845step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19845step2 raw19845step1; decide +kernel
      have hl : raw19845step2Labels = raw19845step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19845step1 raw19845step1Labels permutation14 hz
    mixedMoment B raw19845step2 raw19845step2Labels = mixedMoment B raw19845step3 raw19845step3Labels := by
      have ha : raw19845step3 = (fun i j => raw19845step2 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19845step3 raw19845step2; decide +kernel
      have hl : raw19845step3Labels = raw19845step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19845step2 raw19845step2Labels permutation7 permutation4
    _ = mixedMoment B node862 node862Labels := by rfl

def raw19846 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw19846Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw19846step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19846step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw19846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19846step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -2, 0], ![3, 1, -4]]
def raw19846step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19846 raw19846Labels = mixedMoment B node727 node727Labels := by
  calc
    mixedMoment B raw19846 raw19846Labels = mixedMoment B raw19846step0 raw19846step0Labels := by
      have hz : ∀ j, raw19846 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19846step0 = (fun i j => raw19846 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19846step0 raw19846; decide +kernel
      have hl : raw19846step0Labels = raw19846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19846 raw19846Labels permutation434 hz
    mixedMoment B raw19846step0 raw19846step0Labels = mixedMoment B raw19846step1 raw19846step1Labels := by
      have hz : ∀ j, raw19846step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19846step1 = (fun i j => raw19846step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19846step1 raw19846step0; decide +kernel
      have hl : raw19846step1Labels = raw19846step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19846step0 raw19846step0Labels permutation80 hz
    mixedMoment B raw19846step1 raw19846step1Labels = mixedMoment B raw19846step2 raw19846step2Labels := by
      have ha : raw19846step2 = (fun i j => raw19846step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19846step2 raw19846step1; decide +kernel
      have hl : raw19846step2Labels = raw19846step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19846step1 raw19846step1Labels permutation29 permutation4
    _ = mixedMoment B node727 node727Labels := by rfl

def raw19847 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw19847Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw19847step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19847step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw19847step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19847step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -2, 0], ![3, 1, -4]]
def raw19847step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19847 raw19847Labels = mixedMoment B node727 node727Labels := by
  calc
    mixedMoment B raw19847 raw19847Labels = mixedMoment B raw19847step0 raw19847step0Labels := by
      have hz : ∀ j, raw19847 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19847step0 = (fun i j => raw19847 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19847step0 raw19847; decide +kernel
      have hl : raw19847step0Labels = raw19847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19847 raw19847Labels permutation434 hz
    mixedMoment B raw19847step0 raw19847step0Labels = mixedMoment B raw19847step1 raw19847step1Labels := by
      have hz : ∀ j, raw19847step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19847step1 = (fun i j => raw19847step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19847step1 raw19847step0; decide +kernel
      have hl : raw19847step1Labels = raw19847step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19847step0 raw19847step0Labels permutation56 hz
    mixedMoment B raw19847step1 raw19847step1Labels = mixedMoment B raw19847step2 raw19847step2Labels := by
      have ha : raw19847step2 = (fun i j => raw19847step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19847step2 raw19847step1; decide +kernel
      have hl : raw19847step2Labels = raw19847step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19847step1 raw19847step1Labels permutation29 permutation4
    _ = mixedMoment B node727 node727Labels := by rfl

def raw19848 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw19848Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw19848step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw19848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19848step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -2, 0], ![3, 1, -4]]
def raw19848step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19848 raw19848Labels = mixedMoment B node727 node727Labels := by
  calc
    mixedMoment B raw19848 raw19848Labels = mixedMoment B raw19848step0 raw19848step0Labels := by
      have hz : ∀ j, raw19848 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19848step0 = (fun i j => raw19848 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19848step0 raw19848; decide +kernel
      have hl : raw19848step0Labels = raw19848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19848 raw19848Labels permutation346 hz
    mixedMoment B raw19848step0 raw19848step0Labels = mixedMoment B raw19848step1 raw19848step1Labels := by
      have hz : ∀ j, raw19848step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19848step1 = (fun i j => raw19848step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19848step1 raw19848step0; decide +kernel
      have hl : raw19848step1Labels = raw19848step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19848step0 raw19848step0Labels permutation56 hz
    mixedMoment B raw19848step1 raw19848step1Labels = mixedMoment B raw19848step2 raw19848step2Labels := by
      have ha : raw19848step2 = (fun i j => raw19848step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19848step2 raw19848step1; decide +kernel
      have hl : raw19848step2Labels = raw19848step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19848step1 raw19848step1Labels permutation29 permutation4
    _ = mixedMoment B node727 node727Labels := by rfl

def raw19849 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -5, 4]]
def raw19849Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -5, 4]]
def raw19849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19849step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 2, 0], ![1, -5, 4]]
def raw19849step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19849step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 2, 0], ![1, -5, 4]]
def raw19849step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19849step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, -2, 0], ![3, 1, -4]]
def raw19849step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19849 raw19849Labels = mixedMoment B node565 node565Labels := by
  calc
    mixedMoment B raw19849 raw19849Labels = mixedMoment B raw19849step0 raw19849step0Labels := by
      have hz : ∀ j, raw19849 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19849step0 = (fun i j => raw19849 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19849step0 raw19849; decide +kernel
      have hl : raw19849step0Labels = raw19849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19849 raw19849Labels permutation434 hz
    mixedMoment B raw19849step0 raw19849step0Labels = mixedMoment B raw19849step1 raw19849step1Labels := by
      have hz : ∀ j, raw19849step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19849step1 = (fun i j => raw19849step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19849step1 raw19849step0; decide +kernel
      have hl : raw19849step1Labels = raw19849step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19849step0 raw19849step0Labels permutation80 hz
    mixedMoment B raw19849step1 raw19849step1Labels = mixedMoment B raw19849step2 raw19849step2Labels := by
      have hz : ∀ j, raw19849step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19849step2 = (fun i j => raw19849step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19849step2 raw19849step1; decide +kernel
      have hl : raw19849step2Labels = raw19849step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19849step1 raw19849step1Labels permutation14 hz
    mixedMoment B raw19849step2 raw19849step2Labels = mixedMoment B raw19849step3 raw19849step3Labels := by
      have ha : raw19849step3 = (fun i j => raw19849step2 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19849step3 raw19849step2; decide +kernel
      have hl : raw19849step3Labels = raw19849step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19849step2 raw19849step2Labels permutation7 permutation4
    _ = mixedMoment B node565 node565Labels := by rfl

def raw19850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19850Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19850step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19850step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19850step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw19850step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19850step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw19850step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19850 raw19850Labels = mixedMoment B node791 node791Labels := by
  calc
    mixedMoment B raw19850 raw19850Labels = mixedMoment B raw19850step0 raw19850step0Labels := by
      have hz : ∀ j, raw19850 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19850step0 = (fun i j => raw19850 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19850step0 raw19850; decide +kernel
      have hl : raw19850step0Labels = raw19850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19850 raw19850Labels permutation346 hz
    mixedMoment B raw19850step0 raw19850step0Labels = mixedMoment B raw19850step1 raw19850step1Labels := by
      have hz : ∀ j, raw19850step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19850step1 = (fun i j => raw19850step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19850step1 raw19850step0; decide +kernel
      have hl : raw19850step1Labels = raw19850step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19850step0 raw19850step0Labels permutation56 hz
    mixedMoment B raw19850step1 raw19850step1Labels = mixedMoment B raw19850step2 raw19850step2Labels := by
      have ha : raw19850step2 = (fun i j => raw19850step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19850step2 raw19850step1; decide +kernel
      have hl : raw19850step2Labels = raw19850step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19850step1 raw19850step1Labels permutation29 permutation2
    mixedMoment B raw19850step2 raw19850step2Labels = mixedMoment B raw19850step3 raw19850step3Labels := by
      have ha : raw19850step3 = -raw19850step2 := by apply Matrix.ext; change ∀ i j, raw19850step3 i j = -(raw19850step2 i j); unfold raw19850step3 raw19850step2; decide +kernel
      have hl : raw19850step3Labels = raw19850step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node791 node791Labels := by rfl

def raw19851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19851Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19851step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw19851step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19851step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw19851step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19851 raw19851Labels = mixedMoment B node785 node785Labels := by
  calc
    mixedMoment B raw19851 raw19851Labels = mixedMoment B raw19851step0 raw19851step0Labels := by
      have hz : ∀ j, raw19851 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19851step0 = (fun i j => raw19851 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19851step0 raw19851; decide +kernel
      have hl : raw19851step0Labels = raw19851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19851 raw19851Labels permutation346 hz
    mixedMoment B raw19851step0 raw19851step0Labels = mixedMoment B raw19851step1 raw19851step1Labels := by
      have ha : raw19851step1 = (fun i j => raw19851step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19851step1 raw19851step0; decide +kernel
      have hl : raw19851step1Labels = raw19851step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19851step0 raw19851step0Labels permutation145 permutation2
    mixedMoment B raw19851step1 raw19851step1Labels = mixedMoment B raw19851step2 raw19851step2Labels := by
      have ha : raw19851step2 = -raw19851step1 := by apply Matrix.ext; change ∀ i j, raw19851step2 i j = -(raw19851step1 i j); unfold raw19851step2 raw19851step1; decide +kernel
      have hl : raw19851step2Labels = raw19851step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node785 node785Labels := by rfl

def raw19852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19852Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19852step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw19852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19852step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw19852step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19852 raw19852Labels = mixedMoment B node785 node785Labels := by
  calc
    mixedMoment B raw19852 raw19852Labels = mixedMoment B raw19852step0 raw19852step0Labels := by
      have hz : ∀ j, raw19852 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19852step0 = (fun i j => raw19852 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19852step0 raw19852; decide +kernel
      have hl : raw19852step0Labels = raw19852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19852 raw19852Labels permutation265 hz
    mixedMoment B raw19852step0 raw19852step0Labels = mixedMoment B raw19852step1 raw19852step1Labels := by
      have ha : raw19852step1 = (fun i j => raw19852step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19852step1 raw19852step0; decide +kernel
      have hl : raw19852step1Labels = raw19852step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19852step0 raw19852step0Labels permutation145 permutation2
    mixedMoment B raw19852step1 raw19852step1Labels = mixedMoment B raw19852step2 raw19852step2Labels := by
      have ha : raw19852step2 = -raw19852step1 := by apply Matrix.ext; change ∀ i j, raw19852step2 i j = -(raw19852step1 i j); unfold raw19852step2 raw19852step1; decide +kernel
      have hl : raw19852step2Labels = raw19852step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node785 node785Labels := by rfl

def raw19853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19853Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19853step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19853step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19853step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw19853step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19853step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw19853step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19853 raw19853Labels = mixedMoment B node812 node812Labels := by
  calc
    mixedMoment B raw19853 raw19853Labels = mixedMoment B raw19853step0 raw19853step0Labels := by
      have hz : ∀ j, raw19853 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19853step0 = (fun i j => raw19853 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19853step0 raw19853; decide +kernel
      have hl : raw19853step0Labels = raw19853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19853 raw19853Labels permutation346 hz
    mixedMoment B raw19853step0 raw19853step0Labels = mixedMoment B raw19853step1 raw19853step1Labels := by
      have hz : ∀ j, raw19853step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19853step1 = (fun i j => raw19853step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19853step1 raw19853step0; decide +kernel
      have hl : raw19853step1Labels = raw19853step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19853step0 raw19853step0Labels permutation56 hz
    mixedMoment B raw19853step1 raw19853step1Labels = mixedMoment B raw19853step2 raw19853step2Labels := by
      have ha : raw19853step2 = (fun i j => raw19853step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19853step2 raw19853step1; decide +kernel
      have hl : raw19853step2Labels = raw19853step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19853step1 raw19853step1Labels permutation31 permutation2
    mixedMoment B raw19853step2 raw19853step2Labels = mixedMoment B raw19853step3 raw19853step3Labels := by
      have ha : raw19853step3 = -raw19853step2 := by apply Matrix.ext; change ∀ i j, raw19853step3 i j = -(raw19853step2 i j); unfold raw19853step3 raw19853step2; decide +kernel
      have hl : raw19853step3Labels = raw19853step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node812 node812Labels := by rfl

def raw19854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, 0, -4]]
def raw19854Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![4, 0, -4]]
def raw19854step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19854step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![4, 0, -4]]
def raw19854step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19854step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw19854step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19854step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw19854step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19854 raw19854Labels = mixedMoment B node812 node812Labels := by
  calc
    mixedMoment B raw19854 raw19854Labels = mixedMoment B raw19854step0 raw19854step0Labels := by
      have hz : ∀ j, raw19854 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19854step0 = (fun i j => raw19854 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19854step0 raw19854; decide +kernel
      have hl : raw19854step0Labels = raw19854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19854 raw19854Labels permutation346 hz
    mixedMoment B raw19854step0 raw19854step0Labels = mixedMoment B raw19854step1 raw19854step1Labels := by
      have hz : ∀ j, raw19854step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19854step1 = (fun i j => raw19854step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19854step1 raw19854step0; decide +kernel
      have hl : raw19854step1Labels = raw19854step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19854step0 raw19854step0Labels permutation56 hz
    mixedMoment B raw19854step1 raw19854step1Labels = mixedMoment B raw19854step2 raw19854step2Labels := by
      have ha : raw19854step2 = (fun i j => raw19854step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19854step2 raw19854step1; decide +kernel
      have hl : raw19854step2Labels = raw19854step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19854step1 raw19854step1Labels permutation29 permutation2
    mixedMoment B raw19854step2 raw19854step2Labels = mixedMoment B raw19854step3 raw19854step3Labels := by
      have ha : raw19854step3 = -raw19854step2 := by apply Matrix.ext; change ∀ i j, raw19854step3 i j = -(raw19854step2 i j); unfold raw19854step3 raw19854step2; decide +kernel
      have hl : raw19854step3Labels = raw19854step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node812 node812Labels := by rfl

def raw19855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 1, -4]]
def raw19855Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 1, -4]]
def raw19855step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19855step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![3, 1, -4]]
def raw19855step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19855step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw19855step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19855step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw19855step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19855 raw19855Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw19855 raw19855Labels = mixedMoment B raw19855step0 raw19855step0Labels := by
      have hz : ∀ j, raw19855 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19855step0 = (fun i j => raw19855 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19855step0 raw19855; decide +kernel
      have hl : raw19855step0Labels = raw19855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19855 raw19855Labels permutation346 hz
    mixedMoment B raw19855step0 raw19855step0Labels = mixedMoment B raw19855step1 raw19855step1Labels := by
      have hz : ∀ j, raw19855step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19855step1 = (fun i j => raw19855step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19855step1 raw19855step0; decide +kernel
      have hl : raw19855step1Labels = raw19855step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19855step0 raw19855step0Labels permutation56 hz
    mixedMoment B raw19855step1 raw19855step1Labels = mixedMoment B raw19855step2 raw19855step2Labels := by
      have ha : raw19855step2 = (fun i j => raw19855step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19855step2 raw19855step1; decide +kernel
      have hl : raw19855step2Labels = raw19855step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19855step1 raw19855step1Labels permutation29 permutation2
    mixedMoment B raw19855step2 raw19855step2Labels = mixedMoment B raw19855step3 raw19855step3Labels := by
      have ha : raw19855step3 = -raw19855step2 := by apply Matrix.ext; change ∀ i j, raw19855step3 i j = -(raw19855step2 i j); unfold raw19855step3 raw19855step2; decide +kernel
      have hl : raw19855step3Labels = raw19855step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1710 node1710Labels := by rfl

def raw19856 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-1, 1], ![-1, 1], ![4, -4]]
def raw19856Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19856step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![-1, 1], ![4, -4]]
def raw19856step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19856step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![4, -4]]
def raw19856step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19856step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw19856step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19856step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw19856step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19856 raw19856Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw19856 raw19856Labels = mixedMoment B raw19856step0 raw19856step0Labels := by
      have hz : ∀ j, raw19856 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19856step0 = (fun i j => raw19856 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19856step0 raw19856; decide +kernel
      have hl : raw19856step0Labels = raw19856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19856 raw19856Labels permutation346 hz
    mixedMoment B raw19856step0 raw19856step0Labels = mixedMoment B raw19856step1 raw19856step1Labels := by
      have hz : ∀ j, raw19856step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19856step1 = (fun i j => raw19856step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19856step1 raw19856step0; decide +kernel
      have hl : raw19856step1Labels = raw19856step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19856step0 raw19856step0Labels permutation56 hz
    mixedMoment B raw19856step1 raw19856step1Labels = mixedMoment B raw19856step2 raw19856step2Labels := by
      have ha : raw19856step2 = (fun i j => raw19856step1 (permutation29 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19856step2 raw19856step1; decide +kernel
      have hl : raw19856step2Labels = raw19856step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19856step1 raw19856step1Labels permutation29 permutation0
    mixedMoment B raw19856step2 raw19856step2Labels = mixedMoment B raw19856step3 raw19856step3Labels := by
      have ha : raw19856step3 = -raw19856step2 := by apply Matrix.ext; change ∀ i j, raw19856step3 i j = -(raw19856step2 i j); unfold raw19856step3 raw19856step2; decide +kernel
      have hl : raw19856step3Labels = raw19856step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw19857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19857Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19857step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19857step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19857 raw19857Labels = mixedMoment B node705 node705Labels := by
  calc
    mixedMoment B raw19857 raw19857Labels = mixedMoment B raw19857step0 raw19857step0Labels := by
      have hz : ∀ j, raw19857 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19857step0 = (fun i j => raw19857 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19857step0 raw19857; decide +kernel
      have hl : raw19857step0Labels = raw19857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19857 raw19857Labels permutation346 hz
    mixedMoment B raw19857step0 raw19857step0Labels = mixedMoment B raw19857step1 raw19857step1Labels := by
      have ha : raw19857step1 = (fun i j => raw19857step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19857step1 raw19857step0; decide +kernel
      have hl : raw19857step1Labels = raw19857step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19857step0 raw19857step0Labels permutation139 permutation2
    mixedMoment B raw19857step1 raw19857step1Labels = mixedMoment B raw19857step2 raw19857step2Labels := by
      have ha : raw19857step2 = -raw19857step1 := by apply Matrix.ext; change ∀ i j, raw19857step2 i j = -(raw19857step1 i j); unfold raw19857step2 raw19857step1; decide +kernel
      have hl : raw19857step2Labels = raw19857step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node705 node705Labels := by rfl

def raw19858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19858Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![4, 0, -4]]
def raw19858step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19858step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19858step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19858step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19858 raw19858Labels = mixedMoment B node705 node705Labels := by
  calc
    mixedMoment B raw19858 raw19858Labels = mixedMoment B raw19858step0 raw19858step0Labels := by
      have hz : ∀ j, raw19858 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19858step0 = (fun i j => raw19858 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19858step0 raw19858; decide +kernel
      have hl : raw19858step0Labels = raw19858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19858 raw19858Labels permutation265 hz
    mixedMoment B raw19858step0 raw19858step0Labels = mixedMoment B raw19858step1 raw19858step1Labels := by
      have ha : raw19858step1 = (fun i j => raw19858step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19858step1 raw19858step0; decide +kernel
      have hl : raw19858step1Labels = raw19858step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19858step0 raw19858step0Labels permutation139 permutation2
    mixedMoment B raw19858step1 raw19858step1Labels = mixedMoment B raw19858step2 raw19858step2Labels := by
      have ha : raw19858step2 = -raw19858step1 := by apply Matrix.ext; change ∀ i j, raw19858step2 i j = -(raw19858step1 i j); unfold raw19858step2 raw19858step1; decide +kernel
      have hl : raw19858step2Labels = raw19858step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node705 node705Labels := by rfl

def raw19859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![4, 0, -4]]
def raw19859Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![4, 0, -4]]
def raw19859step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![4, 0, -4]]
def raw19859step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19859step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19859step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19859step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19859step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19859 raw19859Labels = mixedMoment B node740 node740Labels := by
  calc
    mixedMoment B raw19859 raw19859Labels = mixedMoment B raw19859step0 raw19859step0Labels := by
      have hz : ∀ j, raw19859 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19859step0 = (fun i j => raw19859 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19859step0 raw19859; decide +kernel
      have hl : raw19859step0Labels = raw19859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19859 raw19859Labels permutation346 hz
    mixedMoment B raw19859step0 raw19859step0Labels = mixedMoment B raw19859step1 raw19859step1Labels := by
      have hz : ∀ j, raw19859step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19859step1 = (fun i j => raw19859step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19859step1 raw19859step0; decide +kernel
      have hl : raw19859step1Labels = raw19859step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19859step0 raw19859step0Labels permutation56 hz
    mixedMoment B raw19859step1 raw19859step1Labels = mixedMoment B raw19859step2 raw19859step2Labels := by
      have ha : raw19859step2 = (fun i j => raw19859step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19859step2 raw19859step1; decide +kernel
      have hl : raw19859step2Labels = raw19859step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19859step1 raw19859step1Labels permutation31 permutation2
    mixedMoment B raw19859step2 raw19859step2Labels = mixedMoment B raw19859step3 raw19859step3Labels := by
      have ha : raw19859step3 = -raw19859step2 := by apply Matrix.ext; change ∀ i j, raw19859step3 i j = -(raw19859step2 i j); unfold raw19859step3 raw19859step2; decide +kernel
      have hl : raw19859step3Labels = raw19859step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node740 node740Labels := by rfl

def raw19860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![5, -1, -4]]
def raw19860Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![5, -1, -4]]
def raw19860step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19860step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![5, -1, -4]]
def raw19860step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19860step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw19860step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19860step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw19860step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19860 raw19860Labels = mixedMoment B node545 node545Labels := by
  calc
    mixedMoment B raw19860 raw19860Labels = mixedMoment B raw19860step0 raw19860step0Labels := by
      have hz : ∀ j, raw19860 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19860step0 = (fun i j => raw19860 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19860step0 raw19860; decide +kernel
      have hl : raw19860step0Labels = raw19860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19860 raw19860Labels permutation346 hz
    mixedMoment B raw19860step0 raw19860step0Labels = mixedMoment B raw19860step1 raw19860step1Labels := by
      have hz : ∀ j, raw19860step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19860step1 = (fun i j => raw19860step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19860step1 raw19860step0; decide +kernel
      have hl : raw19860step1Labels = raw19860step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19860step0 raw19860step0Labels permutation56 hz
    mixedMoment B raw19860step1 raw19860step1Labels = mixedMoment B raw19860step2 raw19860step2Labels := by
      have ha : raw19860step2 = (fun i j => raw19860step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19860step2 raw19860step1; decide +kernel
      have hl : raw19860step2Labels = raw19860step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19860step1 raw19860step1Labels permutation31 permutation2
    mixedMoment B raw19860step2 raw19860step2Labels = mixedMoment B raw19860step3 raw19860step3Labels := by
      have ha : raw19860step3 = -raw19860step2 := by apply Matrix.ext; change ∀ i j, raw19860step3 i j = -(raw19860step2 i j); unfold raw19860step3 raw19860step2; decide +kernel
      have hl : raw19860step3Labels = raw19860step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node545 node545Labels := by rfl

def raw19861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 1, -4]]
def raw19861Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 1, -4]]
def raw19861step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw19861step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19861 raw19861Labels = mixedMoment B node1199 node1199Labels := by
  calc
    mixedMoment B raw19861 raw19861Labels = mixedMoment B raw19861step0 raw19861step0Labels := by
      have hz : ∀ j, raw19861 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19861step0 = (fun i j => raw19861 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19861step0 raw19861; decide +kernel
      have hl : raw19861step0Labels = raw19861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19861 raw19861Labels permutation346 hz
    mixedMoment B raw19861step0 raw19861step0Labels = mixedMoment B raw19861step1 raw19861step1Labels := by
      have ha : raw19861step1 = (fun i j => raw19861step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19861step1 raw19861step0; decide +kernel
      have hl : raw19861step1Labels = raw19861step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19861step0 raw19861step0Labels permutation40 permutation2
    _ = mixedMoment B node1199 node1199Labels := by rfl

def raw19862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 1, -4]]
def raw19862Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![3, 1, -4]]
def raw19862step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw19862step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19862 raw19862Labels = mixedMoment B node1199 node1199Labels := by
  calc
    mixedMoment B raw19862 raw19862Labels = mixedMoment B raw19862step0 raw19862step0Labels := by
      have hz : ∀ j, raw19862 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19862step0 = (fun i j => raw19862 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19862step0 raw19862; decide +kernel
      have hl : raw19862step0Labels = raw19862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19862 raw19862Labels permutation265 hz
    mixedMoment B raw19862step0 raw19862step0Labels = mixedMoment B raw19862step1 raw19862step1Labels := by
      have ha : raw19862step1 = (fun i j => raw19862step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19862step1 raw19862step0; decide +kernel
      have hl : raw19862step1Labels = raw19862step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19862step0 raw19862step0Labels permutation40 permutation2
    _ = mixedMoment B node1199 node1199Labels := by rfl

def raw19863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 1, -4]]
def raw19863Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![3, 1, -4]]
def raw19863step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19863step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, -1, 1], ![3, 1, -4]]
def raw19863step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19863step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw19863step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19863 raw19863Labels = mixedMoment B node1231 node1231Labels := by
  calc
    mixedMoment B raw19863 raw19863Labels = mixedMoment B raw19863step0 raw19863step0Labels := by
      have hz : ∀ j, raw19863 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19863step0 = (fun i j => raw19863 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19863step0 raw19863; decide +kernel
      have hl : raw19863step0Labels = raw19863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19863 raw19863Labels permutation346 hz
    mixedMoment B raw19863step0 raw19863step0Labels = mixedMoment B raw19863step1 raw19863step1Labels := by
      have hz : ∀ j, raw19863step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19863step1 = (fun i j => raw19863step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19863step1 raw19863step0; decide +kernel
      have hl : raw19863step1Labels = raw19863step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19863step0 raw19863step0Labels permutation56 hz
    mixedMoment B raw19863step1 raw19863step1Labels = mixedMoment B raw19863step2 raw19863step2Labels := by
      have ha : raw19863step2 = (fun i j => raw19863step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19863step2 raw19863step1; decide +kernel
      have hl : raw19863step2Labels = raw19863step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19863step1 raw19863step1Labels permutation10 permutation2
    _ = mixedMoment B node1231 node1231Labels := by rfl

def raw19864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw19864Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw19864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19864step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw19864step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19864 raw19864Labels = mixedMoment B node1231 node1231Labels := by
  calc
    mixedMoment B raw19864 raw19864Labels = mixedMoment B raw19864step0 raw19864step0Labels := by
      have hz : ∀ j, raw19864 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19864step0 = (fun i j => raw19864 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19864step0 raw19864; decide +kernel
      have hl : raw19864step0Labels = raw19864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19864 raw19864Labels permutation346 hz
    mixedMoment B raw19864step0 raw19864step0Labels = mixedMoment B raw19864step1 raw19864step1Labels := by
      have hz : ∀ j, raw19864step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19864step1 = (fun i j => raw19864step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19864step1 raw19864step0; decide +kernel
      have hl : raw19864step1Labels = raw19864step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19864step0 raw19864step0Labels permutation56 hz
    _ = mixedMoment B node1231 node1231Labels := by rfl

def raw19865 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19865Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19865step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19865step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19865step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw19865step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19865 raw19865Labels = mixedMoment B node849 node849Labels := by
  calc
    mixedMoment B raw19865 raw19865Labels = mixedMoment B raw19865step0 raw19865step0Labels := by
      have hz : ∀ j, raw19865 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19865step0 = (fun i j => raw19865 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19865step0 raw19865; decide +kernel
      have hl : raw19865step0Labels = raw19865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19865 raw19865Labels permutation346 hz
    mixedMoment B raw19865step0 raw19865step0Labels = mixedMoment B raw19865step1 raw19865step1Labels := by
      have hz : ∀ j, raw19865step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19865step1 = (fun i j => raw19865step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19865step1 raw19865step0; decide +kernel
      have hl : raw19865step1Labels = raw19865step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19865step0 raw19865step0Labels permutation56 hz
    mixedMoment B raw19865step1 raw19865step1Labels = mixedMoment B raw19865step2 raw19865step2Labels := by
      have ha : raw19865step2 = (fun i j => raw19865step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19865step2 raw19865step1; decide +kernel
      have hl : raw19865step2Labels = raw19865step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19865step1 raw19865step1Labels permutation29 permutation4
    _ = mixedMoment B node849 node849Labels := by rfl

def raw19866 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19866Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19866step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw19866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19866 raw19866Labels = mixedMoment B node711 node711Labels := by
  calc
    mixedMoment B raw19866 raw19866Labels = mixedMoment B raw19866step0 raw19866step0Labels := by
      have hz : ∀ j, raw19866 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19866step0 = (fun i j => raw19866 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19866step0 raw19866; decide +kernel
      have hl : raw19866step0Labels = raw19866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19866 raw19866Labels permutation346 hz
    mixedMoment B raw19866step0 raw19866step0Labels = mixedMoment B raw19866step1 raw19866step1Labels := by
      have ha : raw19866step1 = (fun i j => raw19866step0 (permutation137 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19866step1 raw19866step0; decide +kernel
      have hl : raw19866step1Labels = raw19866step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19866step0 raw19866step0Labels permutation137 permutation4
    _ = mixedMoment B node711 node711Labels := by rfl

def raw19867 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19867Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19867step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw19867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19867 raw19867Labels = mixedMoment B node711 node711Labels := by
  calc
    mixedMoment B raw19867 raw19867Labels = mixedMoment B raw19867step0 raw19867step0Labels := by
      have hz : ∀ j, raw19867 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19867step0 = (fun i j => raw19867 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19867step0 raw19867; decide +kernel
      have hl : raw19867step0Labels = raw19867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19867 raw19867Labels permutation265 hz
    mixedMoment B raw19867step0 raw19867step0Labels = mixedMoment B raw19867step1 raw19867step1Labels := by
      have ha : raw19867step1 = (fun i j => raw19867step0 (permutation137 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19867step1 raw19867step0; decide +kernel
      have hl : raw19867step1Labels = raw19867step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19867step0 raw19867step0Labels permutation137 permutation4
    _ = mixedMoment B node711 node711Labels := by rfl

def raw19868 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -4, 4]]
def raw19868Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19868step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19868step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19868step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -4, 4]]
def raw19868step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19868step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![3, 1, -4]]
def raw19868step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19868 raw19868Labels = mixedMoment B node855 node855Labels := by
  calc
    mixedMoment B raw19868 raw19868Labels = mixedMoment B raw19868step0 raw19868step0Labels := by
      have hz : ∀ j, raw19868 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19868step0 = (fun i j => raw19868 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19868step0 raw19868; decide +kernel
      have hl : raw19868step0Labels = raw19868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19868 raw19868Labels permutation520 hz
    mixedMoment B raw19868step0 raw19868step0Labels = mixedMoment B raw19868step1 raw19868step1Labels := by
      have hz : ∀ j, raw19868step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19868step1 = (fun i j => raw19868step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19868step1 raw19868step0; decide +kernel
      have hl : raw19868step1Labels = raw19868step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19868step0 raw19868step0Labels permutation80 hz
    mixedMoment B raw19868step1 raw19868step1Labels = mixedMoment B raw19868step2 raw19868step2Labels := by
      have hz : ∀ j, raw19868step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19868step2 = (fun i j => raw19868step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19868step2 raw19868step1; decide +kernel
      have hl : raw19868step2Labels = raw19868step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19868step1 raw19868step1Labels permutation14 hz
    mixedMoment B raw19868step2 raw19868step2Labels = mixedMoment B raw19868step3 raw19868step3Labels := by
      have ha : raw19868step3 = (fun i j => raw19868step2 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19868step3 raw19868step2; decide +kernel
      have hl : raw19868step3Labels = raw19868step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19868step2 raw19868step2Labels permutation7 permutation4
    _ = mixedMoment B node855 node855Labels := by rfl

def raw19869 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -5, 4]]
def raw19869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -5, 4]]
def raw19869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -5, 4]]
def raw19869step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19869step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw19869step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19869 raw19869Labels = mixedMoment B node553 node553Labels := by
  calc
    mixedMoment B raw19869 raw19869Labels = mixedMoment B raw19869step0 raw19869step0Labels := by
      have hz : ∀ j, raw19869 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19869step0 = (fun i j => raw19869 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19869step0 raw19869; decide +kernel
      have hl : raw19869step0Labels = raw19869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19869 raw19869Labels permutation346 hz
    mixedMoment B raw19869step0 raw19869step0Labels = mixedMoment B raw19869step1 raw19869step1Labels := by
      have hz : ∀ j, raw19869step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19869step1 = (fun i j => raw19869step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19869step1 raw19869step0; decide +kernel
      have hl : raw19869step1Labels = raw19869step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19869step0 raw19869step0Labels permutation56 hz
    mixedMoment B raw19869step1 raw19869step1Labels = mixedMoment B raw19869step2 raw19869step2Labels := by
      have ha : raw19869step2 = (fun i j => raw19869step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19869step2 raw19869step1; decide +kernel
      have hl : raw19869step2Labels = raw19869step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19869step1 raw19869step1Labels permutation29 permutation4
    _ = mixedMoment B node553 node553Labels := by rfl

def raw19870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19870step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, -1, 1], ![4, -1, -3]]
def raw19870step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19870step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19870step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19870 raw19870Labels = mixedMoment B node986 node986Labels := by
  calc
    mixedMoment B raw19870 raw19870Labels = mixedMoment B raw19870step0 raw19870step0Labels := by
      have hz : ∀ j, raw19870 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19870step0 = (fun i j => raw19870 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19870step0 raw19870; decide +kernel
      have hl : raw19870step0Labels = raw19870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19870 raw19870Labels permutation434 hz
    mixedMoment B raw19870step0 raw19870step0Labels = mixedMoment B raw19870step1 raw19870step1Labels := by
      have hz : ∀ j, raw19870step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19870step1 = (fun i j => raw19870step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19870step1 raw19870step0; decide +kernel
      have hl : raw19870step1Labels = raw19870step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19870step0 raw19870step0Labels permutation80 hz
    mixedMoment B raw19870step1 raw19870step1Labels = mixedMoment B raw19870step2 raw19870step2Labels := by
      have ha : raw19870step2 = (fun i j => raw19870step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19870step2 raw19870step1; decide +kernel
      have hl : raw19870step2Labels = raw19870step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19870step1 raw19870step1Labels permutation10 permutation2
    _ = mixedMoment B node986 node986Labels := by rfl

def raw19871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19871step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![4, -1, -3]]
def raw19871step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19871step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 2, -1], ![-3, 0, 3]]
def raw19871step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19871step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw19871step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19871 raw19871Labels = mixedMoment B node1037 node1037Labels := by
  calc
    mixedMoment B raw19871 raw19871Labels = mixedMoment B raw19871step0 raw19871step0Labels := by
      have hz : ∀ j, raw19871 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19871step0 = (fun i j => raw19871 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19871step0 raw19871; decide +kernel
      have hl : raw19871step0Labels = raw19871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19871 raw19871Labels permutation434 hz
    mixedMoment B raw19871step0 raw19871step0Labels = mixedMoment B raw19871step1 raw19871step1Labels := by
      have hz : ∀ j, raw19871step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19871step1 = (fun i j => raw19871step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19871step1 raw19871step0; decide +kernel
      have hl : raw19871step1Labels = raw19871step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19871step0 raw19871step0Labels permutation80 hz
    mixedMoment B raw19871step1 raw19871step1Labels = mixedMoment B raw19871step2 raw19871step2Labels := by
      have ha : raw19871step2 = (fun i j => raw19871step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19871step2 raw19871step1; decide +kernel
      have hl : raw19871step2Labels = raw19871step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19871step1 raw19871step1Labels permutation31 permutation2
    mixedMoment B raw19871step2 raw19871step2Labels = mixedMoment B raw19871step3 raw19871step3Labels := by
      have ha : raw19871step3 = -raw19871step2 := by apply Matrix.ext; change ∀ i j, raw19871step3 i j = -(raw19871step2 i j); unfold raw19871step3 raw19871step2; decide +kernel
      have hl : raw19871step3Labels = raw19871step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1037 node1037Labels := by rfl

def raw19872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw19872step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19872step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw19872step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19872 raw19872Labels = mixedMoment B node979 node979Labels := by
  calc
    mixedMoment B raw19872 raw19872Labels = mixedMoment B raw19872step0 raw19872step0Labels := by
      have hz : ∀ j, raw19872 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19872step0 = (fun i j => raw19872 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19872step0 raw19872; decide +kernel
      have hl : raw19872step0Labels = raw19872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19872 raw19872Labels permutation434 hz
    mixedMoment B raw19872step0 raw19872step0Labels = mixedMoment B raw19872step1 raw19872step1Labels := by
      have ha : raw19872step1 = (fun i j => raw19872step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19872step1 raw19872step0; decide +kernel
      have hl : raw19872step1Labels = raw19872step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19872step0 raw19872step0Labels permutation139 permutation2
    mixedMoment B raw19872step1 raw19872step1Labels = mixedMoment B raw19872step2 raw19872step2Labels := by
      have ha : raw19872step2 = -raw19872step1 := by apply Matrix.ext; change ∀ i j, raw19872step2 i j = -(raw19872step1 i j); unfold raw19872step2 raw19872step1; decide +kernel
      have hl : raw19872step2Labels = raw19872step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node979 node979Labels := by rfl

def raw19873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw19873step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19873step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw19873step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19873 raw19873Labels = mixedMoment B node979 node979Labels := by
  calc
    mixedMoment B raw19873 raw19873Labels = mixedMoment B raw19873step0 raw19873step0Labels := by
      have hz : ∀ j, raw19873 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19873step0 = (fun i j => raw19873 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19873step0 raw19873; decide +kernel
      have hl : raw19873step0Labels = raw19873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19873 raw19873Labels permutation346 hz
    mixedMoment B raw19873step0 raw19873step0Labels = mixedMoment B raw19873step1 raw19873step1Labels := by
      have ha : raw19873step1 = (fun i j => raw19873step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19873step1 raw19873step0; decide +kernel
      have hl : raw19873step1Labels = raw19873step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19873step0 raw19873step0Labels permutation139 permutation2
    mixedMoment B raw19873step1 raw19873step1Labels = mixedMoment B raw19873step2 raw19873step2Labels := by
      have ha : raw19873step2 = -raw19873step1 := by apply Matrix.ext; change ∀ i j, raw19873step2 i j = -(raw19873step1 i j); unfold raw19873step2 raw19873step1; decide +kernel
      have hl : raw19873step2Labels = raw19873step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node979 node979Labels := by rfl

def raw19874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19874step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 0, 1], ![4, -1, -3]]
def raw19874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19874step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 0, 1], ![-3, 0, 3]]
def raw19874step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19874step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw19874step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19874 raw19874Labels = mixedMoment B node1007 node1007Labels := by
  calc
    mixedMoment B raw19874 raw19874Labels = mixedMoment B raw19874step0 raw19874step0Labels := by
      have hz : ∀ j, raw19874 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19874step0 = (fun i j => raw19874 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19874step0 raw19874; decide +kernel
      have hl : raw19874step0Labels = raw19874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19874 raw19874Labels permutation434 hz
    mixedMoment B raw19874step0 raw19874step0Labels = mixedMoment B raw19874step1 raw19874step1Labels := by
      have hz : ∀ j, raw19874step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19874step1 = (fun i j => raw19874step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19874step1 raw19874step0; decide +kernel
      have hl : raw19874step1Labels = raw19874step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19874step0 raw19874step0Labels permutation80 hz
    mixedMoment B raw19874step1 raw19874step1Labels = mixedMoment B raw19874step2 raw19874step2Labels := by
      have ha : raw19874step2 = (fun i j => raw19874step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19874step2 raw19874step1; decide +kernel
      have hl : raw19874step2Labels = raw19874step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19874step1 raw19874step1Labels permutation29 permutation2
    mixedMoment B raw19874step2 raw19874step2Labels = mixedMoment B raw19874step3 raw19874step3Labels := by
      have ha : raw19874step3 = -raw19874step2 := by apply Matrix.ext; change ∀ i j, raw19874step3 i j = -(raw19874step2 i j); unfold raw19874step3 raw19874step2; decide +kernel
      have hl : raw19874step3Labels = raw19874step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1007 node1007Labels := by rfl

def raw19875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19875Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19875step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, -1, 1], ![3, 0, -3]]
def raw19875step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19875step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw19875step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19875 raw19875Labels = mixedMoment B node2208 node2208Labels := by
  calc
    mixedMoment B raw19875 raw19875Labels = mixedMoment B raw19875step0 raw19875step0Labels := by
      have hz : ∀ j, raw19875 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19875step0 = (fun i j => raw19875 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19875step0 raw19875; decide +kernel
      have hl : raw19875step0Labels = raw19875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19875 raw19875Labels permutation434 hz
    mixedMoment B raw19875step0 raw19875step0Labels = mixedMoment B raw19875step1 raw19875step1Labels := by
      have hz : ∀ j, raw19875step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19875step1 = (fun i j => raw19875step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19875step1 raw19875step0; decide +kernel
      have hl : raw19875step1Labels = raw19875step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19875step0 raw19875step0Labels permutation80 hz
    mixedMoment B raw19875step1 raw19875step1Labels = mixedMoment B raw19875step2 raw19875step2Labels := by
      have ha : raw19875step2 = (fun i j => raw19875step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19875step2 raw19875step1; decide +kernel
      have hl : raw19875step2Labels = raw19875step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19875step1 raw19875step1Labels permutation10 permutation2
    _ = mixedMoment B node2208 node2208Labels := by rfl

def raw19876 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![0, 0], ![-1, 1], ![3, -3]]
def raw19876Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19876step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![-1, 1], ![3, -3]]
def raw19876step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19876step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![3, -3]]
def raw19876step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19876step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw19876step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19876 raw19876Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw19876 raw19876Labels = mixedMoment B raw19876step0 raw19876step0Labels := by
      have hz : ∀ j, raw19876 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19876step0 = (fun i j => raw19876 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19876step0 raw19876; decide +kernel
      have hl : raw19876step0Labels = raw19876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19876 raw19876Labels permutation434 hz
    mixedMoment B raw19876step0 raw19876step0Labels = mixedMoment B raw19876step1 raw19876step1Labels := by
      have hz : ∀ j, raw19876step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19876step1 = (fun i j => raw19876step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19876step1 raw19876step0; decide +kernel
      have hl : raw19876step1Labels = raw19876step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19876step0 raw19876step0Labels permutation80 hz
    mixedMoment B raw19876step1 raw19876step1Labels = mixedMoment B raw19876step2 raw19876step2Labels := by
      have ha : raw19876step2 = (fun i j => raw19876step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19876step2 raw19876step1; decide +kernel
      have hl : raw19876step2Labels = raw19876step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19876step1 raw19876step1Labels permutation10 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw19877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19877Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19877step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, -1, 1], ![4, -1, -3]]
def raw19877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19877step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw19877step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19877 raw19877Labels = mixedMoment B node574 node574Labels := by
  calc
    mixedMoment B raw19877 raw19877Labels = mixedMoment B raw19877step0 raw19877step0Labels := by
      have hz : ∀ j, raw19877 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19877step0 = (fun i j => raw19877 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19877step0 raw19877; decide +kernel
      have hl : raw19877step0Labels = raw19877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19877 raw19877Labels permutation434 hz
    mixedMoment B raw19877step0 raw19877step0Labels = mixedMoment B raw19877step1 raw19877step1Labels := by
      have hz : ∀ j, raw19877step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19877step1 = (fun i j => raw19877step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19877step1 raw19877step0; decide +kernel
      have hl : raw19877step1Labels = raw19877step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19877step0 raw19877step0Labels permutation80 hz
    mixedMoment B raw19877step1 raw19877step1Labels = mixedMoment B raw19877step2 raw19877step2Labels := by
      have ha : raw19877step2 = (fun i j => raw19877step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19877step2 raw19877step1; decide +kernel
      have hl : raw19877step2Labels = raw19877step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19877step1 raw19877step1Labels permutation10 permutation2
    _ = mixedMoment B node574 node574Labels := by rfl

def raw19878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19878step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19878step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19878step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19878 raw19878Labels = mixedMoment B node867 node867Labels := by
  calc
    mixedMoment B raw19878 raw19878Labels = mixedMoment B raw19878step0 raw19878step0Labels := by
      have hz : ∀ j, raw19878 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19878step0 = (fun i j => raw19878 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19878step0 raw19878; decide +kernel
      have hl : raw19878step0Labels = raw19878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19878 raw19878Labels permutation434 hz
    mixedMoment B raw19878step0 raw19878step0Labels = mixedMoment B raw19878step1 raw19878step1Labels := by
      have ha : raw19878step1 = (fun i j => raw19878step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19878step1 raw19878step0; decide +kernel
      have hl : raw19878step1Labels = raw19878step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19878step0 raw19878step0Labels permutation139 permutation2
    mixedMoment B raw19878step1 raw19878step1Labels = mixedMoment B raw19878step2 raw19878step2Labels := by
      have ha : raw19878step2 = -raw19878step1 := by apply Matrix.ext; change ∀ i j, raw19878step2 i j = -(raw19878step1 i j); unfold raw19878step2 raw19878step1; decide +kernel
      have hl : raw19878step2Labels = raw19878step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node867 node867Labels := by rfl

def raw19879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![4, -1, -3]]
def raw19879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19879step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19879step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19879step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19879step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19879 raw19879Labels = mixedMoment B node867 node867Labels := by
  calc
    mixedMoment B raw19879 raw19879Labels = mixedMoment B raw19879step0 raw19879step0Labels := by
      have hz : ∀ j, raw19879 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19879step0 = (fun i j => raw19879 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19879step0 raw19879; decide +kernel
      have hl : raw19879step0Labels = raw19879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19879 raw19879Labels permutation346 hz
    mixedMoment B raw19879step0 raw19879step0Labels = mixedMoment B raw19879step1 raw19879step1Labels := by
      have ha : raw19879step1 = (fun i j => raw19879step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19879step1 raw19879step0; decide +kernel
      have hl : raw19879step1Labels = raw19879step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19879step0 raw19879step0Labels permutation139 permutation2
    mixedMoment B raw19879step1 raw19879step1Labels = mixedMoment B raw19879step2 raw19879step2Labels := by
      have ha : raw19879step2 = -raw19879step1 := by apply Matrix.ext; change ∀ i j, raw19879step2 i j = -(raw19879step1 i j); unfold raw19879step2 raw19879step1; decide +kernel
      have hl : raw19879step2Labels = raw19879step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node867 node867Labels := by rfl

def raw19880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![4, -1, -3]]
def raw19880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19880step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 0, 1], ![4, -1, -3]]
def raw19880step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19880step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw19880step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19880 raw19880Labels = mixedMoment B node890 node890Labels := by
  calc
    mixedMoment B raw19880 raw19880Labels = mixedMoment B raw19880step0 raw19880step0Labels := by
      have hz : ∀ j, raw19880 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19880step0 = (fun i j => raw19880 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19880step0 raw19880; decide +kernel
      have hl : raw19880step0Labels = raw19880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19880 raw19880Labels permutation434 hz
    mixedMoment B raw19880step0 raw19880step0Labels = mixedMoment B raw19880step1 raw19880step1Labels := by
      have hz : ∀ j, raw19880step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19880step1 = (fun i j => raw19880step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19880step1 raw19880step0; decide +kernel
      have hl : raw19880step1Labels = raw19880step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19880step0 raw19880step0Labels permutation80 hz
    mixedMoment B raw19880step1 raw19880step1Labels = mixedMoment B raw19880step2 raw19880step2Labels := by
      have ha : raw19880step2 = (fun i j => raw19880step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19880step2 raw19880step1; decide +kernel
      have hl : raw19880step2Labels = raw19880step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19880step1 raw19880step1Labels permutation10 permutation2
    _ = mixedMoment B node890 node890Labels := by rfl

def raw19881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19881Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw19881step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19881step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, -1, 1], ![3, 0, -3]]
def raw19881step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19881step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw19881step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19881 raw19881Labels = mixedMoment B node1007 node1007Labels := by
  calc
    mixedMoment B raw19881 raw19881Labels = mixedMoment B raw19881step0 raw19881step0Labels := by
      have hz : ∀ j, raw19881 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19881step0 = (fun i j => raw19881 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19881step0 raw19881; decide +kernel
      have hl : raw19881step0Labels = raw19881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19881 raw19881Labels permutation434 hz
    mixedMoment B raw19881step0 raw19881step0Labels = mixedMoment B raw19881step1 raw19881step1Labels := by
      have hz : ∀ j, raw19881step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19881step1 = (fun i j => raw19881step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19881step1 raw19881step0; decide +kernel
      have hl : raw19881step1Labels = raw19881step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19881step0 raw19881step0Labels permutation80 hz
    mixedMoment B raw19881step1 raw19881step1Labels = mixedMoment B raw19881step2 raw19881step2Labels := by
      have ha : raw19881step2 = (fun i j => raw19881step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19881step2 raw19881step1; decide +kernel
      have hl : raw19881step2Labels = raw19881step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19881step1 raw19881step1Labels permutation10 permutation2
    _ = mixedMoment B node1007 node1007Labels := by rfl

def raw19882 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19882Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19882step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19882step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, 2, 0], ![-3, -1, 4]]
def raw19882step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19882step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -2, 0], ![3, 1, -4]]
def raw19882step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19882 raw19882Labels = mixedMoment B node727 node727Labels := by
  calc
    mixedMoment B raw19882 raw19882Labels = mixedMoment B raw19882step0 raw19882step0Labels := by
      have hz : ∀ j, raw19882 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19882step0 = (fun i j => raw19882 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19882step0 raw19882; decide +kernel
      have hl : raw19882step0Labels = raw19882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19882 raw19882Labels permutation434 hz
    mixedMoment B raw19882step0 raw19882step0Labels = mixedMoment B raw19882step1 raw19882step1Labels := by
      have hz : ∀ j, raw19882step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19882step1 = (fun i j => raw19882step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19882step1 raw19882step0; decide +kernel
      have hl : raw19882step1Labels = raw19882step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19882step0 raw19882step0Labels permutation80 hz
    mixedMoment B raw19882step1 raw19882step1Labels = mixedMoment B raw19882step2 raw19882step2Labels := by
      have ha : raw19882step2 = (fun i j => raw19882step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19882step2 raw19882step1; decide +kernel
      have hl : raw19882step2Labels = raw19882step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19882step1 raw19882step1Labels permutation10 permutation4
    mixedMoment B raw19882step2 raw19882step2Labels = mixedMoment B raw19882step3 raw19882step3Labels := by
      have ha : raw19882step3 = -raw19882step2 := by apply Matrix.ext; change ∀ i j, raw19882step3 i j = -(raw19882step2 i j); unfold raw19882step3 raw19882step2; decide +kernel
      have hl : raw19882step3Labels = raw19882step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node727 node727Labels := by rfl

def raw19883 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19883Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19883step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, -1, 4]]
def raw19883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw19883step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19883 raw19883Labels = mixedMoment B node711 node711Labels := by
  calc
    mixedMoment B raw19883 raw19883Labels = mixedMoment B raw19883step0 raw19883step0Labels := by
      have hz : ∀ j, raw19883 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19883step0 = (fun i j => raw19883 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19883step0 raw19883; decide +kernel
      have hl : raw19883step0Labels = raw19883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19883 raw19883Labels permutation434 hz
    mixedMoment B raw19883step0 raw19883step0Labels = mixedMoment B raw19883step1 raw19883step1Labels := by
      have ha : raw19883step1 = (fun i j => raw19883step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19883step1 raw19883step0; decide +kernel
      have hl : raw19883step1Labels = raw19883step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19883step0 raw19883step0Labels permutation44 permutation4
    mixedMoment B raw19883step1 raw19883step1Labels = mixedMoment B raw19883step2 raw19883step2Labels := by
      have ha : raw19883step2 = -raw19883step1 := by apply Matrix.ext; change ∀ i j, raw19883step2 i j = -(raw19883step1 i j); unfold raw19883step2 raw19883step1; decide +kernel
      have hl : raw19883step2Labels = raw19883step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node711 node711Labels := by rfl

def raw19884 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19884Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19884step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, -1, 4]]
def raw19884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19884step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw19884step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19884 raw19884Labels = mixedMoment B node711 node711Labels := by
  calc
    mixedMoment B raw19884 raw19884Labels = mixedMoment B raw19884step0 raw19884step0Labels := by
      have hz : ∀ j, raw19884 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19884step0 = (fun i j => raw19884 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19884step0 raw19884; decide +kernel
      have hl : raw19884step0Labels = raw19884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19884 raw19884Labels permutation346 hz
    mixedMoment B raw19884step0 raw19884step0Labels = mixedMoment B raw19884step1 raw19884step1Labels := by
      have ha : raw19884step1 = (fun i j => raw19884step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19884step1 raw19884step0; decide +kernel
      have hl : raw19884step1Labels = raw19884step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19884step0 raw19884step0Labels permutation44 permutation4
    mixedMoment B raw19884step1 raw19884step1Labels = mixedMoment B raw19884step2 raw19884step2Labels := by
      have ha : raw19884step2 = -raw19884step1 := by apply Matrix.ext; change ∀ i j, raw19884step2 i j = -(raw19884step1 i j); unfold raw19884step2 raw19884step1; decide +kernel
      have hl : raw19884step2Labels = raw19884step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node711 node711Labels := by rfl

def raw19885 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19885Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19885step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19885step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19885step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, -3, 4]]
def raw19885step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19885step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-3, -1, 4]]
def raw19885step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19885step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![3, 1, -4]]
def raw19885step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19885 raw19885Labels = mixedMoment B node855 node855Labels := by
  calc
    mixedMoment B raw19885 raw19885Labels = mixedMoment B raw19885step0 raw19885step0Labels := by
      have hz : ∀ j, raw19885 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19885step0 = (fun i j => raw19885 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19885step0 raw19885; decide +kernel
      have hl : raw19885step0Labels = raw19885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19885 raw19885Labels permutation520 hz
    mixedMoment B raw19885step0 raw19885step0Labels = mixedMoment B raw19885step1 raw19885step1Labels := by
      have hz : ∀ j, raw19885step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19885step1 = (fun i j => raw19885step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19885step1 raw19885step0; decide +kernel
      have hl : raw19885step1Labels = raw19885step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19885step0 raw19885step0Labels permutation104 hz
    mixedMoment B raw19885step1 raw19885step1Labels = mixedMoment B raw19885step2 raw19885step2Labels := by
      have hz : ∀ j, raw19885step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19885step2 = (fun i j => raw19885step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19885step2 raw19885step1; decide +kernel
      have hl : raw19885step2Labels = raw19885step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19885step1 raw19885step1Labels permutation20 hz
    mixedMoment B raw19885step2 raw19885step2Labels = mixedMoment B raw19885step3 raw19885step3Labels := by
      have ha : raw19885step3 = (fun i j => raw19885step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19885step3 raw19885step2; decide +kernel
      have hl : raw19885step3Labels = raw19885step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19885step2 raw19885step2Labels permutation2 permutation4
    mixedMoment B raw19885step3 raw19885step3Labels = mixedMoment B raw19885step4 raw19885step4Labels := by
      have ha : raw19885step4 = -raw19885step3 := by apply Matrix.ext; change ∀ i j, raw19885step4 i j = -(raw19885step3 i j); unfold raw19885step4 raw19885step3; decide +kernel
      have hl : raw19885step4Labels = raw19885step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node855 node855Labels := by rfl

def raw19886 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19886Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19886step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19886step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19886step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![4, 0, -4]]
def raw19886step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19886 raw19886Labels = mixedMoment B node718 node718Labels := by
  calc
    mixedMoment B raw19886 raw19886Labels = mixedMoment B raw19886step0 raw19886step0Labels := by
      have hz : ∀ j, raw19886 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19886step0 = (fun i j => raw19886 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19886step0 raw19886; decide +kernel
      have hl : raw19886step0Labels = raw19886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19886 raw19886Labels permutation434 hz
    mixedMoment B raw19886step0 raw19886step0Labels = mixedMoment B raw19886step1 raw19886step1Labels := by
      have hz : ∀ j, raw19886step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19886step1 = (fun i j => raw19886step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19886step1 raw19886step0; decide +kernel
      have hl : raw19886step1Labels = raw19886step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19886step0 raw19886step0Labels permutation80 hz
    mixedMoment B raw19886step1 raw19886step1Labels = mixedMoment B raw19886step2 raw19886step2Labels := by
      have ha : raw19886step2 = (fun i j => raw19886step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19886step2 raw19886step1; decide +kernel
      have hl : raw19886step2Labels = raw19886step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19886step1 raw19886step1Labels permutation29 permutation4
    _ = mixedMoment B node718 node718Labels := by rfl

def raw19887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19887step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19887step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19887step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![4, -1, -3]]
def raw19887step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19887step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-3, 0, 3]]
def raw19887step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19887step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19887step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19887 raw19887Labels = mixedMoment B node4501 node4501Labels := by
  calc
    mixedMoment B raw19887 raw19887Labels = mixedMoment B raw19887step0 raw19887step0Labels := by
      have hz : ∀ j, raw19887 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19887step0 = (fun i j => raw19887 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19887step0 raw19887; decide +kernel
      have hl : raw19887step0Labels = raw19887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19887 raw19887Labels permutation520 hz
    mixedMoment B raw19887step0 raw19887step0Labels = mixedMoment B raw19887step1 raw19887step1Labels := by
      have hz : ∀ j, raw19887step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19887step1 = (fun i j => raw19887step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19887step1 raw19887step0; decide +kernel
      have hl : raw19887step1Labels = raw19887step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19887step0 raw19887step0Labels permutation104 hz
    mixedMoment B raw19887step1 raw19887step1Labels = mixedMoment B raw19887step2 raw19887step2Labels := by
      have hz : ∀ j, raw19887step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19887step2 = (fun i j => raw19887step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19887step2 raw19887step1; decide +kernel
      have hl : raw19887step2Labels = raw19887step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19887step1 raw19887step1Labels permutation20 hz
    mixedMoment B raw19887step2 raw19887step2Labels = mixedMoment B raw19887step3 raw19887step3Labels := by
      have ha : raw19887step3 = (fun i j => raw19887step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19887step3 raw19887step2; decide +kernel
      have hl : raw19887step3Labels = raw19887step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19887step2 raw19887step2Labels permutation7 permutation2
    mixedMoment B raw19887step3 raw19887step3Labels = mixedMoment B raw19887step4 raw19887step4Labels := by
      have ha : raw19887step4 = -raw19887step3 := by apply Matrix.ext; change ∀ i j, raw19887step4 i j = -(raw19887step3 i j); unfold raw19887step4 raw19887step3; decide +kernel
      have hl : raw19887step4Labels = raw19887step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4501 node4501Labels := by rfl

def raw19888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19888step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19888step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![4, -1, -3]]
def raw19888step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19888step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-3, 0, 3]]
def raw19888step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19888step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19888step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19888 raw19888Labels = mixedMoment B node4501 node4501Labels := by
  calc
    mixedMoment B raw19888 raw19888Labels = mixedMoment B raw19888step0 raw19888step0Labels := by
      have hz : ∀ j, raw19888 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19888step0 = (fun i j => raw19888 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19888step0 raw19888; decide +kernel
      have hl : raw19888step0Labels = raw19888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19888 raw19888Labels permutation520 hz
    mixedMoment B raw19888step0 raw19888step0Labels = mixedMoment B raw19888step1 raw19888step1Labels := by
      have hz : ∀ j, raw19888step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19888step1 = (fun i j => raw19888step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19888step1 raw19888step0; decide +kernel
      have hl : raw19888step1Labels = raw19888step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19888step0 raw19888step0Labels permutation104 hz
    mixedMoment B raw19888step1 raw19888step1Labels = mixedMoment B raw19888step2 raw19888step2Labels := by
      have hz : ∀ j, raw19888step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19888step2 = (fun i j => raw19888step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19888step2 raw19888step1; decide +kernel
      have hl : raw19888step2Labels = raw19888step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19888step1 raw19888step1Labels permutation14 hz
    mixedMoment B raw19888step2 raw19888step2Labels = mixedMoment B raw19888step3 raw19888step3Labels := by
      have ha : raw19888step3 = (fun i j => raw19888step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19888step3 raw19888step2; decide +kernel
      have hl : raw19888step3Labels = raw19888step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19888step2 raw19888step2Labels permutation7 permutation2
    mixedMoment B raw19888step3 raw19888step3Labels = mixedMoment B raw19888step4 raw19888step4Labels := by
      have ha : raw19888step4 = -raw19888step3 := by apply Matrix.ext; change ∀ i j, raw19888step4 i j = -(raw19888step3 i j); unfold raw19888step4 raw19888step3; decide +kernel
      have hl : raw19888step4Labels = raw19888step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4501 node4501Labels := by rfl

def raw19889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19889step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19889step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19889step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![4, -1, -3]]
def raw19889step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19889step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-3, 0, 3]]
def raw19889step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19889step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19889step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19889 raw19889Labels = mixedMoment B node4501 node4501Labels := by
  calc
    mixedMoment B raw19889 raw19889Labels = mixedMoment B raw19889step0 raw19889step0Labels := by
      have hz : ∀ j, raw19889 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19889step0 = (fun i j => raw19889 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19889step0 raw19889; decide +kernel
      have hl : raw19889step0Labels = raw19889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19889 raw19889Labels permutation520 hz
    mixedMoment B raw19889step0 raw19889step0Labels = mixedMoment B raw19889step1 raw19889step1Labels := by
      have hz : ∀ j, raw19889step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19889step1 = (fun i j => raw19889step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19889step1 raw19889step0; decide +kernel
      have hl : raw19889step1Labels = raw19889step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19889step0 raw19889step0Labels permutation80 hz
    mixedMoment B raw19889step1 raw19889step1Labels = mixedMoment B raw19889step2 raw19889step2Labels := by
      have hz : ∀ j, raw19889step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19889step2 = (fun i j => raw19889step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19889step2 raw19889step1; decide +kernel
      have hl : raw19889step2Labels = raw19889step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19889step1 raw19889step1Labels permutation14 hz
    mixedMoment B raw19889step2 raw19889step2Labels = mixedMoment B raw19889step3 raw19889step3Labels := by
      have ha : raw19889step3 = (fun i j => raw19889step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19889step3 raw19889step2; decide +kernel
      have hl : raw19889step3Labels = raw19889step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19889step2 raw19889step2Labels permutation7 permutation2
    mixedMoment B raw19889step3 raw19889step3Labels = mixedMoment B raw19889step4 raw19889step4Labels := by
      have ha : raw19889step4 = -raw19889step3 := by apply Matrix.ext; change ∀ i j, raw19889step4 i j = -(raw19889step3 i j); unfold raw19889step4 raw19889step3; decide +kernel
      have hl : raw19889step4Labels = raw19889step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4501 node4501Labels := by rfl

def raw19890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19890step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19890step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19890step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19890step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![4, -1, -3]]
def raw19890step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19890step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-3, 0, 3]]
def raw19890step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19890step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19890step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19890 raw19890Labels = mixedMoment B node4501 node4501Labels := by
  calc
    mixedMoment B raw19890 raw19890Labels = mixedMoment B raw19890step0 raw19890step0Labels := by
      have hz : ∀ j, raw19890 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19890step0 = (fun i j => raw19890 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19890step0 raw19890; decide +kernel
      have hl : raw19890step0Labels = raw19890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19890 raw19890Labels permutation434 hz
    mixedMoment B raw19890step0 raw19890step0Labels = mixedMoment B raw19890step1 raw19890step1Labels := by
      have hz : ∀ j, raw19890step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19890step1 = (fun i j => raw19890step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19890step1 raw19890step0; decide +kernel
      have hl : raw19890step1Labels = raw19890step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19890step0 raw19890step0Labels permutation80 hz
    mixedMoment B raw19890step1 raw19890step1Labels = mixedMoment B raw19890step2 raw19890step2Labels := by
      have hz : ∀ j, raw19890step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19890step2 = (fun i j => raw19890step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19890step2 raw19890step1; decide +kernel
      have hl : raw19890step2Labels = raw19890step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19890step1 raw19890step1Labels permutation14 hz
    mixedMoment B raw19890step2 raw19890step2Labels = mixedMoment B raw19890step3 raw19890step3Labels := by
      have ha : raw19890step3 = (fun i j => raw19890step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19890step3 raw19890step2; decide +kernel
      have hl : raw19890step3Labels = raw19890step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19890step2 raw19890step2Labels permutation7 permutation2
    mixedMoment B raw19890step3 raw19890step3Labels = mixedMoment B raw19890step4 raw19890step4Labels := by
      have ha : raw19890step4 = -raw19890step3 := by apply Matrix.ext; change ∀ i j, raw19890step4 i j = -(raw19890step3 i j); unfold raw19890step4 raw19890step3; decide +kernel
      have hl : raw19890step4Labels = raw19890step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4501 node4501Labels := by rfl

def raw19891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19891step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19891step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![3, 0, -3]]
def raw19891step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19891step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 0, 3], ![3, 0, -3]]
def raw19891step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19891step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw19891step4Labels : Fin 2 → Fin 3 := ![0, 2]

def raw19891step5 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw19891step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19891 raw19891Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw19891 raw19891Labels = mixedMoment B raw19891step0 raw19891step0Labels := by
      have hz : ∀ j, raw19891 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19891step0 = (fun i j => raw19891 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19891step0 raw19891; decide +kernel
      have hl : raw19891step0Labels = raw19891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19891 raw19891Labels permutation520 hz
    mixedMoment B raw19891step0 raw19891step0Labels = mixedMoment B raw19891step1 raw19891step1Labels := by
      have hz : ∀ j, raw19891step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19891step1 = (fun i j => raw19891step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19891step1 raw19891step0; decide +kernel
      have hl : raw19891step1Labels = raw19891step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19891step0 raw19891step0Labels permutation104 hz
    mixedMoment B raw19891step1 raw19891step1Labels = mixedMoment B raw19891step2 raw19891step2Labels := by
      have hz : ∀ j, raw19891step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19891step2 = (fun i j => raw19891step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19891step2 raw19891step1; decide +kernel
      have hl : raw19891step2Labels = raw19891step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19891step1 raw19891step1Labels permutation20 hz
    mixedMoment B raw19891step2 raw19891step2Labels = mixedMoment B raw19891step3 raw19891step3Labels := by
      have hz : ∀ j, raw19891step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19891step3 = (fun i j => raw19891step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19891step3 raw19891step2; decide +kernel
      have hl : raw19891step3Labels = raw19891step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19891step2 raw19891step2Labels permutation4 hz
    mixedMoment B raw19891step3 raw19891step3Labels = mixedMoment B raw19891step4 raw19891step4Labels := by
      have hz : ∀ i, raw19891step3 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw19891step4 = (fun i j => raw19891step3 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw19891step4 raw19891step3; decide +kernel
      have hl : raw19891step4Labels = (fun j => raw19891step3Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19891step3 raw19891step3Labels permutation4 hz
    mixedMoment B raw19891step4 raw19891step4Labels = mixedMoment B raw19891step5 raw19891step5Labels := by
      have ha : raw19891step5 = raw19891step4 := by apply Matrix.ext; unfold raw19891step5 raw19891step4; decide +kernel
      have hl : raw19891step4Labels = labelEmbedding2 ∘ raw19891step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19891step4 raw19891step4Labels raw19891step5Labels labelEmbedding2 hl
    _ = mixedMoment B node4085 node4085Labels := by rfl

def raw19892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19892step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19892step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19892step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19892step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19892 raw19892Labels = mixedMoment B node4181 node4181Labels := by
  calc
    mixedMoment B raw19892 raw19892Labels = mixedMoment B raw19892step0 raw19892step0Labels := by
      have hz : ∀ j, raw19892 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19892step0 = (fun i j => raw19892 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19892step0 raw19892; decide +kernel
      have hl : raw19892step0Labels = raw19892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19892 raw19892Labels permutation520 hz
    mixedMoment B raw19892step0 raw19892step0Labels = mixedMoment B raw19892step1 raw19892step1Labels := by
      have hz : ∀ j, raw19892step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19892step1 = (fun i j => raw19892step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19892step1 raw19892step0; decide +kernel
      have hl : raw19892step1Labels = raw19892step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19892step0 raw19892step0Labels permutation104 hz
    mixedMoment B raw19892step1 raw19892step1Labels = mixedMoment B raw19892step2 raw19892step2Labels := by
      have hz : ∀ j, raw19892step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19892step2 = (fun i j => raw19892step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19892step2 raw19892step1; decide +kernel
      have hl : raw19892step2Labels = raw19892step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19892step1 raw19892step1Labels permutation20 hz
    _ = mixedMoment B node4181 node4181Labels := by rfl

def raw19893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19893step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19893step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19893step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19893 raw19893Labels = mixedMoment B node4350 node4350Labels := by
  calc
    mixedMoment B raw19893 raw19893Labels = mixedMoment B raw19893step0 raw19893step0Labels := by
      have hz : ∀ j, raw19893 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19893step0 = (fun i j => raw19893 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19893step0 raw19893; decide +kernel
      have hl : raw19893step0Labels = raw19893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19893 raw19893Labels permutation520 hz
    mixedMoment B raw19893step0 raw19893step0Labels = mixedMoment B raw19893step1 raw19893step1Labels := by
      have hz : ∀ j, raw19893step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19893step1 = (fun i j => raw19893step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19893step1 raw19893step0; decide +kernel
      have hl : raw19893step1Labels = raw19893step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19893step0 raw19893step0Labels permutation104 hz
    mixedMoment B raw19893step1 raw19893step1Labels = mixedMoment B raw19893step2 raw19893step2Labels := by
      have ha : raw19893step2 = (fun i j => raw19893step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19893step2 raw19893step1; decide +kernel
      have hl : raw19893step2Labels = raw19893step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19893step1 raw19893step1Labels permutation10 permutation2
    _ = mixedMoment B node4350 node4350Labels := by rfl

def raw19894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19894step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19894step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19894step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19894step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19894 raw19894Labels = mixedMoment B node4350 node4350Labels := by
  calc
    mixedMoment B raw19894 raw19894Labels = mixedMoment B raw19894step0 raw19894step0Labels := by
      have hz : ∀ j, raw19894 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19894step0 = (fun i j => raw19894 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19894step0 raw19894; decide +kernel
      have hl : raw19894step0Labels = raw19894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19894 raw19894Labels permutation520 hz
    mixedMoment B raw19894step0 raw19894step0Labels = mixedMoment B raw19894step1 raw19894step1Labels := by
      have hz : ∀ j, raw19894step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19894step1 = (fun i j => raw19894step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19894step1 raw19894step0; decide +kernel
      have hl : raw19894step1Labels = raw19894step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19894step0 raw19894step0Labels permutation80 hz
    mixedMoment B raw19894step1 raw19894step1Labels = mixedMoment B raw19894step2 raw19894step2Labels := by
      have ha : raw19894step2 = (fun i j => raw19894step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19894step2 raw19894step1; decide +kernel
      have hl : raw19894step2Labels = raw19894step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19894step1 raw19894step1Labels permutation10 permutation2
    _ = mixedMoment B node4350 node4350Labels := by rfl

def raw19895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19895step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19895step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19895step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19895step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19895step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19895 raw19895Labels = mixedMoment B node4350 node4350Labels := by
  calc
    mixedMoment B raw19895 raw19895Labels = mixedMoment B raw19895step0 raw19895step0Labels := by
      have hz : ∀ j, raw19895 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19895step0 = (fun i j => raw19895 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19895step0 raw19895; decide +kernel
      have hl : raw19895step0Labels = raw19895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19895 raw19895Labels permutation434 hz
    mixedMoment B raw19895step0 raw19895step0Labels = mixedMoment B raw19895step1 raw19895step1Labels := by
      have hz : ∀ j, raw19895step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19895step1 = (fun i j => raw19895step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19895step1 raw19895step0; decide +kernel
      have hl : raw19895step1Labels = raw19895step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19895step0 raw19895step0Labels permutation80 hz
    mixedMoment B raw19895step1 raw19895step1Labels = mixedMoment B raw19895step2 raw19895step2Labels := by
      have ha : raw19895step2 = (fun i j => raw19895step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19895step2 raw19895step1; decide +kernel
      have hl : raw19895step2Labels = raw19895step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19895step1 raw19895step1Labels permutation10 permutation2
    _ = mixedMoment B node4350 node4350Labels := by rfl

def raw19896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19896step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19896step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19896step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19896step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19896 raw19896Labels = mixedMoment B node4501 node4501Labels := by
  calc
    mixedMoment B raw19896 raw19896Labels = mixedMoment B raw19896step0 raw19896step0Labels := by
      have hz : ∀ j, raw19896 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19896step0 = (fun i j => raw19896 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19896step0 raw19896; decide +kernel
      have hl : raw19896step0Labels = raw19896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19896 raw19896Labels permutation520 hz
    mixedMoment B raw19896step0 raw19896step0Labels = mixedMoment B raw19896step1 raw19896step1Labels := by
      have hz : ∀ j, raw19896step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19896step1 = (fun i j => raw19896step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19896step1 raw19896step0; decide +kernel
      have hl : raw19896step1Labels = raw19896step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19896step0 raw19896step0Labels permutation104 hz
    mixedMoment B raw19896step1 raw19896step1Labels = mixedMoment B raw19896step2 raw19896step2Labels := by
      have hz : ∀ j, raw19896step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19896step2 = (fun i j => raw19896step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19896step2 raw19896step1; decide +kernel
      have hl : raw19896step2Labels = raw19896step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19896step1 raw19896step1Labels permutation20 hz
    _ = mixedMoment B node4501 node4501Labels := by rfl

def raw19897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19897step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19897step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19897step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19897step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19897step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19897 raw19897Labels = mixedMoment B node4181 node4181Labels := by
  calc
    mixedMoment B raw19897 raw19897Labels = mixedMoment B raw19897step0 raw19897step0Labels := by
      have hz : ∀ j, raw19897 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19897step0 = (fun i j => raw19897 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19897step0 raw19897; decide +kernel
      have hl : raw19897step0Labels = raw19897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19897 raw19897Labels permutation520 hz
    mixedMoment B raw19897step0 raw19897step0Labels = mixedMoment B raw19897step1 raw19897step1Labels := by
      have hz : ∀ j, raw19897step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19897step1 = (fun i j => raw19897step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19897step1 raw19897step0; decide +kernel
      have hl : raw19897step1Labels = raw19897step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19897step0 raw19897step0Labels permutation104 hz
    mixedMoment B raw19897step1 raw19897step1Labels = mixedMoment B raw19897step2 raw19897step2Labels := by
      have hz : ∀ j, raw19897step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19897step2 = (fun i j => raw19897step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19897step2 raw19897step1; decide +kernel
      have hl : raw19897step2Labels = raw19897step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19897step1 raw19897step1Labels permutation14 hz
    _ = mixedMoment B node4181 node4181Labels := by rfl

def raw19898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19898step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19898step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19898step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19898 raw19898Labels = mixedMoment B node4350 node4350Labels := by
  calc
    mixedMoment B raw19898 raw19898Labels = mixedMoment B raw19898step0 raw19898step0Labels := by
      have hz : ∀ j, raw19898 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19898step0 = (fun i j => raw19898 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19898step0 raw19898; decide +kernel
      have hl : raw19898step0Labels = raw19898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19898 raw19898Labels permutation520 hz
    mixedMoment B raw19898step0 raw19898step0Labels = mixedMoment B raw19898step1 raw19898step1Labels := by
      have hz : ∀ j, raw19898step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19898step1 = (fun i j => raw19898step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19898step1 raw19898step0; decide +kernel
      have hl : raw19898step1Labels = raw19898step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19898step0 raw19898step0Labels permutation104 hz
    _ = mixedMoment B node4350 node4350Labels := by rfl

def raw19899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19899step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19899step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19899step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19899step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19899step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19899 raw19899Labels = mixedMoment B node4350 node4350Labels := by
  calc
    mixedMoment B raw19899 raw19899Labels = mixedMoment B raw19899step0 raw19899step0Labels := by
      have hz : ∀ j, raw19899 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19899step0 = (fun i j => raw19899 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19899step0 raw19899; decide +kernel
      have hl : raw19899step0Labels = raw19899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19899 raw19899Labels permutation520 hz
    mixedMoment B raw19899step0 raw19899step0Labels = mixedMoment B raw19899step1 raw19899step1Labels := by
      have hz : ∀ j, raw19899step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19899step1 = (fun i j => raw19899step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19899step1 raw19899step0; decide +kernel
      have hl : raw19899step1Labels = raw19899step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19899step0 raw19899step0Labels permutation56 hz
    mixedMoment B raw19899step1 raw19899step1Labels = mixedMoment B raw19899step2 raw19899step2Labels := by
      have ha : raw19899step2 = (fun i j => raw19899step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19899step2 raw19899step1; decide +kernel
      have hl : raw19899step2Labels = raw19899step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19899step1 raw19899step1Labels permutation10 permutation2
    _ = mixedMoment B node4350 node4350Labels := by rfl

def raw19900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19900step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19900step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19900step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19900 raw19900Labels = mixedMoment B node4350 node4350Labels := by
  calc
    mixedMoment B raw19900 raw19900Labels = mixedMoment B raw19900step0 raw19900step0Labels := by
      have hz : ∀ j, raw19900 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19900step0 = (fun i j => raw19900 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19900step0 raw19900; decide +kernel
      have hl : raw19900step0Labels = raw19900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19900 raw19900Labels permutation434 hz
    mixedMoment B raw19900step0 raw19900step0Labels = mixedMoment B raw19900step1 raw19900step1Labels := by
      have hz : ∀ j, raw19900step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19900step1 = (fun i j => raw19900step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19900step1 raw19900step0; decide +kernel
      have hl : raw19900step1Labels = raw19900step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19900step0 raw19900step0Labels permutation56 hz
    mixedMoment B raw19900step1 raw19900step1Labels = mixedMoment B raw19900step2 raw19900step2Labels := by
      have ha : raw19900step2 = (fun i j => raw19900step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19900step2 raw19900step1; decide +kernel
      have hl : raw19900step2Labels = raw19900step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19900step1 raw19900step1Labels permutation10 permutation2
    _ = mixedMoment B node4350 node4350Labels := by rfl

def raw19901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw19901step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19901step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19901step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19901 raw19901Labels = mixedMoment B node4501 node4501Labels := by
  calc
    mixedMoment B raw19901 raw19901Labels = mixedMoment B raw19901step0 raw19901step0Labels := by
      have hz : ∀ j, raw19901 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19901step0 = (fun i j => raw19901 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19901step0 raw19901; decide +kernel
      have hl : raw19901step0Labels = raw19901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19901 raw19901Labels permutation520 hz
    mixedMoment B raw19901step0 raw19901step0Labels = mixedMoment B raw19901step1 raw19901step1Labels := by
      have hz : ∀ j, raw19901step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19901step1 = (fun i j => raw19901step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19901step1 raw19901step0; decide +kernel
      have hl : raw19901step1Labels = raw19901step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19901step0 raw19901step0Labels permutation104 hz
    mixedMoment B raw19901step1 raw19901step1Labels = mixedMoment B raw19901step2 raw19901step2Labels := by
      have hz : ∀ j, raw19901step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19901step2 = (fun i j => raw19901step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19901step2 raw19901step1; decide +kernel
      have hl : raw19901step2Labels = raw19901step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19901step1 raw19901step1Labels permutation14 hz
    _ = mixedMoment B node4501 node4501Labels := by rfl

def raw19902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19902step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19902step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19902step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19902step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19902step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19902 raw19902Labels = mixedMoment B node4181 node4181Labels := by
  calc
    mixedMoment B raw19902 raw19902Labels = mixedMoment B raw19902step0 raw19902step0Labels := by
      have hz : ∀ j, raw19902 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19902step0 = (fun i j => raw19902 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19902step0 raw19902; decide +kernel
      have hl : raw19902step0Labels = raw19902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19902 raw19902Labels permutation520 hz
    mixedMoment B raw19902step0 raw19902step0Labels = mixedMoment B raw19902step1 raw19902step1Labels := by
      have hz : ∀ j, raw19902step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19902step1 = (fun i j => raw19902step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19902step1 raw19902step0; decide +kernel
      have hl : raw19902step1Labels = raw19902step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19902step0 raw19902step0Labels permutation80 hz
    mixedMoment B raw19902step1 raw19902step1Labels = mixedMoment B raw19902step2 raw19902step2Labels := by
      have hz : ∀ j, raw19902step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19902step2 = (fun i j => raw19902step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19902step2 raw19902step1; decide +kernel
      have hl : raw19902step2Labels = raw19902step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19902step1 raw19902step1Labels permutation14 hz
    _ = mixedMoment B node4181 node4181Labels := by rfl

def raw19903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19903step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19903step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19903 raw19903Labels = mixedMoment B node4350 node4350Labels := by
  calc
    mixedMoment B raw19903 raw19903Labels = mixedMoment B raw19903step0 raw19903step0Labels := by
      have hz : ∀ j, raw19903 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19903step0 = (fun i j => raw19903 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19903step0 raw19903; decide +kernel
      have hl : raw19903step0Labels = raw19903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19903 raw19903Labels permutation520 hz
    mixedMoment B raw19903step0 raw19903step0Labels = mixedMoment B raw19903step1 raw19903step1Labels := by
      have hz : ∀ j, raw19903step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19903step1 = (fun i j => raw19903step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19903step1 raw19903step0; decide +kernel
      have hl : raw19903step1Labels = raw19903step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19903step0 raw19903step0Labels permutation80 hz
    _ = mixedMoment B node4350 node4350Labels := by rfl

def raw19904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19904step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19904step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19904 raw19904Labels = mixedMoment B node4350 node4350Labels := by
  calc
    mixedMoment B raw19904 raw19904Labels = mixedMoment B raw19904step0 raw19904step0Labels := by
      have hz : ∀ j, raw19904 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19904step0 = (fun i j => raw19904 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19904step0 raw19904; decide +kernel
      have hl : raw19904step0Labels = raw19904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19904 raw19904Labels permutation520 hz
    mixedMoment B raw19904step0 raw19904step0Labels = mixedMoment B raw19904step1 raw19904step1Labels := by
      have hz : ∀ j, raw19904step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19904step1 = (fun i j => raw19904step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19904step1 raw19904step0; decide +kernel
      have hl : raw19904step1Labels = raw19904step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19904step0 raw19904step0Labels permutation56 hz
    _ = mixedMoment B node4350 node4350Labels := by rfl

def raw19905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19905step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19905step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19905step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19905step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19905 raw19905Labels = mixedMoment B node4350 node4350Labels := by
  calc
    mixedMoment B raw19905 raw19905Labels = mixedMoment B raw19905step0 raw19905step0Labels := by
      have hz : ∀ j, raw19905 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19905step0 = (fun i j => raw19905 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19905step0 raw19905; decide +kernel
      have hl : raw19905step0Labels = raw19905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19905 raw19905Labels permutation346 hz
    mixedMoment B raw19905step0 raw19905step0Labels = mixedMoment B raw19905step1 raw19905step1Labels := by
      have hz : ∀ j, raw19905step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19905step1 = (fun i j => raw19905step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19905step1 raw19905step0; decide +kernel
      have hl : raw19905step1Labels = raw19905step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19905step0 raw19905step0Labels permutation56 hz
    mixedMoment B raw19905step1 raw19905step1Labels = mixedMoment B raw19905step2 raw19905step2Labels := by
      have ha : raw19905step2 = (fun i j => raw19905step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19905step2 raw19905step1; decide +kernel
      have hl : raw19905step2Labels = raw19905step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19905step1 raw19905step1Labels permutation10 permutation2
    _ = mixedMoment B node4350 node4350Labels := by rfl

def raw19906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw19906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw19906step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19906step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19906step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19906 raw19906Labels = mixedMoment B node4501 node4501Labels := by
  calc
    mixedMoment B raw19906 raw19906Labels = mixedMoment B raw19906step0 raw19906step0Labels := by
      have hz : ∀ j, raw19906 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19906step0 = (fun i j => raw19906 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19906step0 raw19906; decide +kernel
      have hl : raw19906step0Labels = raw19906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19906 raw19906Labels permutation520 hz
    mixedMoment B raw19906step0 raw19906step0Labels = mixedMoment B raw19906step1 raw19906step1Labels := by
      have hz : ∀ j, raw19906step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19906step1 = (fun i j => raw19906step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19906step1 raw19906step0; decide +kernel
      have hl : raw19906step1Labels = raw19906step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19906step0 raw19906step0Labels permutation80 hz
    mixedMoment B raw19906step1 raw19906step1Labels = mixedMoment B raw19906step2 raw19906step2Labels := by
      have hz : ∀ j, raw19906step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19906step2 = (fun i j => raw19906step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19906step2 raw19906step1; decide +kernel
      have hl : raw19906step2Labels = raw19906step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19906step1 raw19906step1Labels permutation14 hz
    _ = mixedMoment B node4501 node4501Labels := by rfl

def raw19907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19907step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19907step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19907step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19907step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19907step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19907 raw19907Labels = mixedMoment B node4181 node4181Labels := by
  calc
    mixedMoment B raw19907 raw19907Labels = mixedMoment B raw19907step0 raw19907step0Labels := by
      have hz : ∀ j, raw19907 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19907step0 = (fun i j => raw19907 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19907step0 raw19907; decide +kernel
      have hl : raw19907step0Labels = raw19907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19907 raw19907Labels permutation434 hz
    mixedMoment B raw19907step0 raw19907step0Labels = mixedMoment B raw19907step1 raw19907step1Labels := by
      have hz : ∀ j, raw19907step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19907step1 = (fun i j => raw19907step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19907step1 raw19907step0; decide +kernel
      have hl : raw19907step1Labels = raw19907step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19907step0 raw19907step0Labels permutation80 hz
    mixedMoment B raw19907step1 raw19907step1Labels = mixedMoment B raw19907step2 raw19907step2Labels := by
      have hz : ∀ j, raw19907step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19907step2 = (fun i j => raw19907step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19907step2 raw19907step1; decide +kernel
      have hl : raw19907step2Labels = raw19907step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19907step1 raw19907step1Labels permutation14 hz
    _ = mixedMoment B node4181 node4181Labels := by rfl

def raw19908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19908step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19908step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19908step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19908 raw19908Labels = mixedMoment B node4350 node4350Labels := by
  calc
    mixedMoment B raw19908 raw19908Labels = mixedMoment B raw19908step0 raw19908step0Labels := by
      have hz : ∀ j, raw19908 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19908step0 = (fun i j => raw19908 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19908step0 raw19908; decide +kernel
      have hl : raw19908step0Labels = raw19908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19908 raw19908Labels permutation434 hz
    mixedMoment B raw19908step0 raw19908step0Labels = mixedMoment B raw19908step1 raw19908step1Labels := by
      have hz : ∀ j, raw19908step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19908step1 = (fun i j => raw19908step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19908step1 raw19908step0; decide +kernel
      have hl : raw19908step1Labels = raw19908step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19908step0 raw19908step0Labels permutation80 hz
    _ = mixedMoment B node4350 node4350Labels := by rfl

def raw19909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19909Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19909step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19909step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19909 raw19909Labels = mixedMoment B node4350 node4350Labels := by
  calc
    mixedMoment B raw19909 raw19909Labels = mixedMoment B raw19909step0 raw19909step0Labels := by
      have hz : ∀ j, raw19909 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19909step0 = (fun i j => raw19909 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19909step0 raw19909; decide +kernel
      have hl : raw19909step0Labels = raw19909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19909 raw19909Labels permutation434 hz
    mixedMoment B raw19909step0 raw19909step0Labels = mixedMoment B raw19909step1 raw19909step1Labels := by
      have hz : ∀ j, raw19909step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19909step1 = (fun i j => raw19909step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19909step1 raw19909step0; decide +kernel
      have hl : raw19909step1Labels = raw19909step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19909step0 raw19909step0Labels permutation56 hz
    _ = mixedMoment B node4350 node4350Labels := by rfl

def raw19910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19910Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19910step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19910step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19910step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19910 raw19910Labels = mixedMoment B node4350 node4350Labels := by
  calc
    mixedMoment B raw19910 raw19910Labels = mixedMoment B raw19910step0 raw19910step0Labels := by
      have hz : ∀ j, raw19910 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19910step0 = (fun i j => raw19910 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19910step0 raw19910; decide +kernel
      have hl : raw19910step0Labels = raw19910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19910 raw19910Labels permutation346 hz
    mixedMoment B raw19910step0 raw19910step0Labels = mixedMoment B raw19910step1 raw19910step1Labels := by
      have hz : ∀ j, raw19910step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19910step1 = (fun i j => raw19910step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19910step1 raw19910step0; decide +kernel
      have hl : raw19910step1Labels = raw19910step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19910step0 raw19910step0Labels permutation56 hz
    _ = mixedMoment B node4350 node4350Labels := by rfl

def raw19911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw19911Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw19911step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19911step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw19911step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19911step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19911step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19911 raw19911Labels = mixedMoment B node4501 node4501Labels := by
  calc
    mixedMoment B raw19911 raw19911Labels = mixedMoment B raw19911step0 raw19911step0Labels := by
      have hz : ∀ j, raw19911 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19911step0 = (fun i j => raw19911 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19911step0 raw19911; decide +kernel
      have hl : raw19911step0Labels = raw19911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19911 raw19911Labels permutation434 hz
    mixedMoment B raw19911step0 raw19911step0Labels = mixedMoment B raw19911step1 raw19911step1Labels := by
      have hz : ∀ j, raw19911step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19911step1 = (fun i j => raw19911step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19911step1 raw19911step0; decide +kernel
      have hl : raw19911step1Labels = raw19911step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19911step0 raw19911step0Labels permutation80 hz
    mixedMoment B raw19911step1 raw19911step1Labels = mixedMoment B raw19911step2 raw19911step2Labels := by
      have hz : ∀ j, raw19911step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19911step2 = (fun i j => raw19911step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19911step2 raw19911step1; decide +kernel
      have hl : raw19911step2Labels = raw19911step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19911step1 raw19911step1Labels permutation14 hz
    _ = mixedMoment B node4501 node4501Labels := by rfl

def raw19912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19912Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19912step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19912step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19912step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![5, -2, -3]]
def raw19912step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19912step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def raw19912step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19912 raw19912Labels = mixedMoment B node4194 node4194Labels := by
  calc
    mixedMoment B raw19912 raw19912Labels = mixedMoment B raw19912step0 raw19912step0Labels := by
      have hz : ∀ j, raw19912 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19912step0 = (fun i j => raw19912 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19912step0 raw19912; decide +kernel
      have hl : raw19912step0Labels = raw19912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19912 raw19912Labels permutation520 hz
    mixedMoment B raw19912step0 raw19912step0Labels = mixedMoment B raw19912step1 raw19912step1Labels := by
      have hz : ∀ j, raw19912step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19912step1 = (fun i j => raw19912step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19912step1 raw19912step0; decide +kernel
      have hl : raw19912step1Labels = raw19912step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19912step0 raw19912step0Labels permutation104 hz
    mixedMoment B raw19912step1 raw19912step1Labels = mixedMoment B raw19912step2 raw19912step2Labels := by
      have hz : ∀ j, raw19912step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19912step2 = (fun i j => raw19912step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19912step2 raw19912step1; decide +kernel
      have hl : raw19912step2Labels = raw19912step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19912step1 raw19912step1Labels permutation20 hz
    mixedMoment B raw19912step2 raw19912step2Labels = mixedMoment B raw19912step3 raw19912step3Labels := by
      have hz : ∀ j, raw19912step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19912step3 = (fun i j => raw19912step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19912step3 raw19912step2; decide +kernel
      have hl : raw19912step3Labels = raw19912step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19912step2 raw19912step2Labels permutation4 hz
    _ = mixedMoment B node4194 node4194Labels := by rfl

def raw19913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19913Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19913step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19913step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19913step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![5, -2, -3]]
def raw19913step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19913step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-4, 1, 3]]
def raw19913step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19913step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19913step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19913 raw19913Labels = mixedMoment B node4181 node4181Labels := by
  calc
    mixedMoment B raw19913 raw19913Labels = mixedMoment B raw19913step0 raw19913step0Labels := by
      have hz : ∀ j, raw19913 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19913step0 = (fun i j => raw19913 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19913step0 raw19913; decide +kernel
      have hl : raw19913step0Labels = raw19913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19913 raw19913Labels permutation520 hz
    mixedMoment B raw19913step0 raw19913step0Labels = mixedMoment B raw19913step1 raw19913step1Labels := by
      have hz : ∀ j, raw19913step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19913step1 = (fun i j => raw19913step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19913step1 raw19913step0; decide +kernel
      have hl : raw19913step1Labels = raw19913step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19913step0 raw19913step0Labels permutation104 hz
    mixedMoment B raw19913step1 raw19913step1Labels = mixedMoment B raw19913step2 raw19913step2Labels := by
      have hz : ∀ j, raw19913step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19913step2 = (fun i j => raw19913step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19913step2 raw19913step1; decide +kernel
      have hl : raw19913step2Labels = raw19913step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19913step1 raw19913step1Labels permutation20 hz
    mixedMoment B raw19913step2 raw19913step2Labels = mixedMoment B raw19913step3 raw19913step3Labels := by
      have ha : raw19913step3 = (fun i j => raw19913step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19913step3 raw19913step2; decide +kernel
      have hl : raw19913step3Labels = raw19913step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19913step2 raw19913step2Labels permutation7 permutation2
    mixedMoment B raw19913step3 raw19913step3Labels = mixedMoment B raw19913step4 raw19913step4Labels := by
      have ha : raw19913step4 = -raw19913step3 := by apply Matrix.ext; change ∀ i j, raw19913step4 i j = -(raw19913step3 i j); unfold raw19913step4 raw19913step3; decide +kernel
      have hl : raw19913step4Labels = raw19913step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4181 node4181Labels := by rfl

def raw19914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19914step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![5, -2, -3]]
def raw19914step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19914step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![5, -2, -3]]
def raw19914step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19914step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-4, 1, 3]]
def raw19914step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19914step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19914step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19914 raw19914Labels = mixedMoment B node4181 node4181Labels := by
  calc
    mixedMoment B raw19914 raw19914Labels = mixedMoment B raw19914step0 raw19914step0Labels := by
      have hz : ∀ j, raw19914 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19914step0 = (fun i j => raw19914 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19914step0 raw19914; decide +kernel
      have hl : raw19914step0Labels = raw19914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19914 raw19914Labels permutation520 hz
    mixedMoment B raw19914step0 raw19914step0Labels = mixedMoment B raw19914step1 raw19914step1Labels := by
      have hz : ∀ j, raw19914step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19914step1 = (fun i j => raw19914step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19914step1 raw19914step0; decide +kernel
      have hl : raw19914step1Labels = raw19914step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19914step0 raw19914step0Labels permutation104 hz
    mixedMoment B raw19914step1 raw19914step1Labels = mixedMoment B raw19914step2 raw19914step2Labels := by
      have hz : ∀ j, raw19914step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19914step2 = (fun i j => raw19914step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19914step2 raw19914step1; decide +kernel
      have hl : raw19914step2Labels = raw19914step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19914step1 raw19914step1Labels permutation14 hz
    mixedMoment B raw19914step2 raw19914step2Labels = mixedMoment B raw19914step3 raw19914step3Labels := by
      have ha : raw19914step3 = (fun i j => raw19914step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19914step3 raw19914step2; decide +kernel
      have hl : raw19914step3Labels = raw19914step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19914step2 raw19914step2Labels permutation7 permutation2
    mixedMoment B raw19914step3 raw19914step3Labels = mixedMoment B raw19914step4 raw19914step4Labels := by
      have ha : raw19914step4 = -raw19914step3 := by apply Matrix.ext; change ∀ i j, raw19914step4 i j = -(raw19914step3 i j); unfold raw19914step4 raw19914step3; decide +kernel
      have hl : raw19914step4Labels = raw19914step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4181 node4181Labels := by rfl

def raw19915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19915Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -2, -3]]
def raw19915step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![5, -2, -3]]
def raw19915step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19915step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![5, -2, -3]]
def raw19915step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19915step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-4, 1, 3]]
def raw19915step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19915step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19915step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19915 raw19915Labels = mixedMoment B node4181 node4181Labels := by
  calc
    mixedMoment B raw19915 raw19915Labels = mixedMoment B raw19915step0 raw19915step0Labels := by
      have hz : ∀ j, raw19915 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19915step0 = (fun i j => raw19915 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19915step0 raw19915; decide +kernel
      have hl : raw19915step0Labels = raw19915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19915 raw19915Labels permutation520 hz
    mixedMoment B raw19915step0 raw19915step0Labels = mixedMoment B raw19915step1 raw19915step1Labels := by
      have hz : ∀ j, raw19915step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19915step1 = (fun i j => raw19915step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19915step1 raw19915step0; decide +kernel
      have hl : raw19915step1Labels = raw19915step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19915step0 raw19915step0Labels permutation80 hz
    mixedMoment B raw19915step1 raw19915step1Labels = mixedMoment B raw19915step2 raw19915step2Labels := by
      have hz : ∀ j, raw19915step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19915step2 = (fun i j => raw19915step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19915step2 raw19915step1; decide +kernel
      have hl : raw19915step2Labels = raw19915step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19915step1 raw19915step1Labels permutation14 hz
    mixedMoment B raw19915step2 raw19915step2Labels = mixedMoment B raw19915step3 raw19915step3Labels := by
      have ha : raw19915step3 = (fun i j => raw19915step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19915step3 raw19915step2; decide +kernel
      have hl : raw19915step3Labels = raw19915step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19915step2 raw19915step2Labels permutation7 permutation2
    mixedMoment B raw19915step3 raw19915step3Labels = mixedMoment B raw19915step4 raw19915step4Labels := by
      have ha : raw19915step4 = -raw19915step3 := by apply Matrix.ext; change ∀ i j, raw19915step4 i j = -(raw19915step3 i j); unfold raw19915step4 raw19915step3; decide +kernel
      have hl : raw19915step4Labels = raw19915step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4181 node4181Labels := by rfl

def raw19916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -2, -3]]
def raw19916Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -2, -3]]
def raw19916step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19916step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![5, -2, -3]]
def raw19916step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19916step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![5, -2, -3]]
def raw19916step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19916step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -2, -3], ![-1, 1, 0], ![-4, 1, 3]]
def raw19916step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19916step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19916step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19916 raw19916Labels = mixedMoment B node4181 node4181Labels := by
  calc
    mixedMoment B raw19916 raw19916Labels = mixedMoment B raw19916step0 raw19916step0Labels := by
      have hz : ∀ j, raw19916 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19916step0 = (fun i j => raw19916 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19916step0 raw19916; decide +kernel
      have hl : raw19916step0Labels = raw19916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19916 raw19916Labels permutation434 hz
    mixedMoment B raw19916step0 raw19916step0Labels = mixedMoment B raw19916step1 raw19916step1Labels := by
      have hz : ∀ j, raw19916step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19916step1 = (fun i j => raw19916step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19916step1 raw19916step0; decide +kernel
      have hl : raw19916step1Labels = raw19916step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19916step0 raw19916step0Labels permutation80 hz
    mixedMoment B raw19916step1 raw19916step1Labels = mixedMoment B raw19916step2 raw19916step2Labels := by
      have hz : ∀ j, raw19916step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19916step2 = (fun i j => raw19916step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19916step2 raw19916step1; decide +kernel
      have hl : raw19916step2Labels = raw19916step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19916step1 raw19916step1Labels permutation14 hz
    mixedMoment B raw19916step2 raw19916step2Labels = mixedMoment B raw19916step3 raw19916step3Labels := by
      have ha : raw19916step3 = (fun i j => raw19916step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19916step3 raw19916step2; decide +kernel
      have hl : raw19916step3Labels = raw19916step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19916step2 raw19916step2Labels permutation7 permutation2
    mixedMoment B raw19916step3 raw19916step3Labels = mixedMoment B raw19916step4 raw19916step4Labels := by
      have ha : raw19916step4 = -raw19916step3 := by apply Matrix.ext; change ∀ i j, raw19916step4 i j = -(raw19916step3 i j); unfold raw19916step4 raw19916step3; decide +kernel
      have hl : raw19916step4Labels = raw19916step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4181 node4181Labels := by rfl

def raw19917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19917Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19917step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19917step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19917step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![4, -1, -3]]
def raw19917step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19917step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19917step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19917step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19917step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19917 raw19917Labels = mixedMoment B node1730 node1730Labels := by
  calc
    mixedMoment B raw19917 raw19917Labels = mixedMoment B raw19917step0 raw19917step0Labels := by
      have hz : ∀ j, raw19917 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19917step0 = (fun i j => raw19917 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19917step0 raw19917; decide +kernel
      have hl : raw19917step0Labels = raw19917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19917 raw19917Labels permutation520 hz
    mixedMoment B raw19917step0 raw19917step0Labels = mixedMoment B raw19917step1 raw19917step1Labels := by
      have hz : ∀ j, raw19917step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19917step1 = (fun i j => raw19917step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19917step1 raw19917step0; decide +kernel
      have hl : raw19917step1Labels = raw19917step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19917step0 raw19917step0Labels permutation104 hz
    mixedMoment B raw19917step1 raw19917step1Labels = mixedMoment B raw19917step2 raw19917step2Labels := by
      have hz : ∀ j, raw19917step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19917step2 = (fun i j => raw19917step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19917step2 raw19917step1; decide +kernel
      have hl : raw19917step2Labels = raw19917step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19917step1 raw19917step1Labels permutation20 hz
    mixedMoment B raw19917step2 raw19917step2Labels = mixedMoment B raw19917step3 raw19917step3Labels := by
      have ha : raw19917step3 = (fun i j => raw19917step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19917step3 raw19917step2; decide +kernel
      have hl : raw19917step3Labels = raw19917step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19917step2 raw19917step2Labels permutation7 permutation7
    mixedMoment B raw19917step3 raw19917step3Labels = mixedMoment B raw19917step4 raw19917step4Labels := by
      have ha : raw19917step4 = raw19917step3 := by apply Matrix.ext; unfold raw19917step4 raw19917step3; decide +kernel
      have hl : raw19917step3Labels = labelEmbedding1 ∘ raw19917step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19917step3 raw19917step3Labels raw19917step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1730 node1730Labels := by rfl

def raw19918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19918Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19918step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19918step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19918step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19918step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![4, -1, -3]]
def raw19918step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19918step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19918step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19918step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19918step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19918 raw19918Labels = mixedMoment B node1730 node1730Labels := by
  calc
    mixedMoment B raw19918 raw19918Labels = mixedMoment B raw19918step0 raw19918step0Labels := by
      have hz : ∀ j, raw19918 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19918step0 = (fun i j => raw19918 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19918step0 raw19918; decide +kernel
      have hl : raw19918step0Labels = raw19918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19918 raw19918Labels permutation520 hz
    mixedMoment B raw19918step0 raw19918step0Labels = mixedMoment B raw19918step1 raw19918step1Labels := by
      have hz : ∀ j, raw19918step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19918step1 = (fun i j => raw19918step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19918step1 raw19918step0; decide +kernel
      have hl : raw19918step1Labels = raw19918step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19918step0 raw19918step0Labels permutation104 hz
    mixedMoment B raw19918step1 raw19918step1Labels = mixedMoment B raw19918step2 raw19918step2Labels := by
      have hz : ∀ j, raw19918step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19918step2 = (fun i j => raw19918step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19918step2 raw19918step1; decide +kernel
      have hl : raw19918step2Labels = raw19918step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19918step1 raw19918step1Labels permutation14 hz
    mixedMoment B raw19918step2 raw19918step2Labels = mixedMoment B raw19918step3 raw19918step3Labels := by
      have ha : raw19918step3 = (fun i j => raw19918step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19918step3 raw19918step2; decide +kernel
      have hl : raw19918step3Labels = raw19918step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19918step2 raw19918step2Labels permutation7 permutation7
    mixedMoment B raw19918step3 raw19918step3Labels = mixedMoment B raw19918step4 raw19918step4Labels := by
      have ha : raw19918step4 = raw19918step3 := by apply Matrix.ext; unfold raw19918step4 raw19918step3; decide +kernel
      have hl : raw19918step3Labels = labelEmbedding1 ∘ raw19918step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19918step3 raw19918step3Labels raw19918step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1730 node1730Labels := by rfl

def raw19919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19919Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19919step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19919step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19919step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19919step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![4, -1, -3]]
def raw19919step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19919step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19919step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19919step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19919step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19919 raw19919Labels = mixedMoment B node1730 node1730Labels := by
  calc
    mixedMoment B raw19919 raw19919Labels = mixedMoment B raw19919step0 raw19919step0Labels := by
      have hz : ∀ j, raw19919 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19919step0 = (fun i j => raw19919 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19919step0 raw19919; decide +kernel
      have hl : raw19919step0Labels = raw19919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19919 raw19919Labels permutation520 hz
    mixedMoment B raw19919step0 raw19919step0Labels = mixedMoment B raw19919step1 raw19919step1Labels := by
      have hz : ∀ j, raw19919step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19919step1 = (fun i j => raw19919step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19919step1 raw19919step0; decide +kernel
      have hl : raw19919step1Labels = raw19919step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19919step0 raw19919step0Labels permutation80 hz
    mixedMoment B raw19919step1 raw19919step1Labels = mixedMoment B raw19919step2 raw19919step2Labels := by
      have hz : ∀ j, raw19919step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19919step2 = (fun i j => raw19919step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19919step2 raw19919step1; decide +kernel
      have hl : raw19919step2Labels = raw19919step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19919step1 raw19919step1Labels permutation14 hz
    mixedMoment B raw19919step2 raw19919step2Labels = mixedMoment B raw19919step3 raw19919step3Labels := by
      have ha : raw19919step3 = (fun i j => raw19919step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19919step3 raw19919step2; decide +kernel
      have hl : raw19919step3Labels = raw19919step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19919step2 raw19919step2Labels permutation7 permutation7
    mixedMoment B raw19919step3 raw19919step3Labels = mixedMoment B raw19919step4 raw19919step4Labels := by
      have ha : raw19919step4 = raw19919step3 := by apply Matrix.ext; unfold raw19919step4 raw19919step3; decide +kernel
      have hl : raw19919step3Labels = labelEmbedding1 ∘ raw19919step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19919step3 raw19919step3Labels raw19919step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1730 node1730Labels := by rfl

def raw19920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19920Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19920step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19920step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19920step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![4, -1, -3]]
def raw19920step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19920step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19920step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19920step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19920step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19920 raw19920Labels = mixedMoment B node1730 node1730Labels := by
  calc
    mixedMoment B raw19920 raw19920Labels = mixedMoment B raw19920step0 raw19920step0Labels := by
      have hz : ∀ j, raw19920 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19920step0 = (fun i j => raw19920 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19920step0 raw19920; decide +kernel
      have hl : raw19920step0Labels = raw19920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19920 raw19920Labels permutation434 hz
    mixedMoment B raw19920step0 raw19920step0Labels = mixedMoment B raw19920step1 raw19920step1Labels := by
      have hz : ∀ j, raw19920step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19920step1 = (fun i j => raw19920step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19920step1 raw19920step0; decide +kernel
      have hl : raw19920step1Labels = raw19920step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19920step0 raw19920step0Labels permutation80 hz
    mixedMoment B raw19920step1 raw19920step1Labels = mixedMoment B raw19920step2 raw19920step2Labels := by
      have hz : ∀ j, raw19920step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19920step2 = (fun i j => raw19920step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19920step2 raw19920step1; decide +kernel
      have hl : raw19920step2Labels = raw19920step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19920step1 raw19920step1Labels permutation14 hz
    mixedMoment B raw19920step2 raw19920step2Labels = mixedMoment B raw19920step3 raw19920step3Labels := by
      have ha : raw19920step3 = (fun i j => raw19920step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19920step3 raw19920step2; decide +kernel
      have hl : raw19920step3Labels = raw19920step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19920step2 raw19920step2Labels permutation7 permutation7
    mixedMoment B raw19920step3 raw19920step3Labels = mixedMoment B raw19920step4 raw19920step4Labels := by
      have ha : raw19920step4 = raw19920step3 := by apply Matrix.ext; unfold raw19920step4 raw19920step3; decide +kernel
      have hl : raw19920step3Labels = labelEmbedding1 ∘ raw19920step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19920step3 raw19920step3Labels raw19920step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1730 node1730Labels := by rfl

def raw19921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19921Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19921step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19921step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19921step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![3, 0, -3]]
def raw19921step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19921step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 0, 3], ![3, 0, -3]]
def raw19921step3Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19921step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw19921step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19921 raw19921Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw19921 raw19921Labels = mixedMoment B raw19921step0 raw19921step0Labels := by
      have hz : ∀ j, raw19921 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19921step0 = (fun i j => raw19921 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19921step0 raw19921; decide +kernel
      have hl : raw19921step0Labels = raw19921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19921 raw19921Labels permutation520 hz
    mixedMoment B raw19921step0 raw19921step0Labels = mixedMoment B raw19921step1 raw19921step1Labels := by
      have hz : ∀ j, raw19921step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19921step1 = (fun i j => raw19921step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19921step1 raw19921step0; decide +kernel
      have hl : raw19921step1Labels = raw19921step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19921step0 raw19921step0Labels permutation104 hz
    mixedMoment B raw19921step1 raw19921step1Labels = mixedMoment B raw19921step2 raw19921step2Labels := by
      have hz : ∀ j, raw19921step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19921step2 = (fun i j => raw19921step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19921step2 raw19921step1; decide +kernel
      have hl : raw19921step2Labels = raw19921step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19921step1 raw19921step1Labels permutation20 hz
    mixedMoment B raw19921step2 raw19921step2Labels = mixedMoment B raw19921step3 raw19921step3Labels := by
      have hz : ∀ j, raw19921step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19921step3 = (fun i j => raw19921step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19921step3 raw19921step2; decide +kernel
      have hl : raw19921step3Labels = raw19921step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19921step2 raw19921step2Labels permutation4 hz
    mixedMoment B raw19921step3 raw19921step3Labels = mixedMoment B raw19921step4 raw19921step4Labels := by
      have hz : ∀ i, raw19921step3 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw19921step4 = (fun i j => raw19921step3 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw19921step4 raw19921step3; decide +kernel
      have hl : raw19921step4Labels = (fun j => raw19921step3Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19921step3 raw19921step3Labels permutation4 hz
    _ = mixedMoment B node4085 node4085Labels := by rfl

def raw19922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19922Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19922step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19922step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19922step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19922step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19922step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19922step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-3, -1, 4]]
def raw19922step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19922step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19922step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19922step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19922step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19922 raw19922Labels = mixedMoment B node1521 node1521Labels := by
  calc
    mixedMoment B raw19922 raw19922Labels = mixedMoment B raw19922step0 raw19922step0Labels := by
      have hz : ∀ j, raw19922 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19922step0 = (fun i j => raw19922 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19922step0 raw19922; decide +kernel
      have hl : raw19922step0Labels = raw19922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19922 raw19922Labels permutation520 hz
    mixedMoment B raw19922step0 raw19922step0Labels = mixedMoment B raw19922step1 raw19922step1Labels := by
      have hz : ∀ j, raw19922step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19922step1 = (fun i j => raw19922step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19922step1 raw19922step0; decide +kernel
      have hl : raw19922step1Labels = raw19922step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19922step0 raw19922step0Labels permutation104 hz
    mixedMoment B raw19922step1 raw19922step1Labels = mixedMoment B raw19922step2 raw19922step2Labels := by
      have hz : ∀ j, raw19922step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19922step2 = (fun i j => raw19922step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19922step2 raw19922step1; decide +kernel
      have hl : raw19922step2Labels = raw19922step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19922step1 raw19922step1Labels permutation20 hz
    mixedMoment B raw19922step2 raw19922step2Labels = mixedMoment B raw19922step3 raw19922step3Labels := by
      have ha : raw19922step3 = (fun i j => raw19922step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19922step3 raw19922step2; decide +kernel
      have hl : raw19922step3Labels = raw19922step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19922step2 raw19922step2Labels permutation2 permutation7
    mixedMoment B raw19922step3 raw19922step3Labels = mixedMoment B raw19922step4 raw19922step4Labels := by
      have ha : raw19922step4 = -raw19922step3 := by apply Matrix.ext; change ∀ i j, raw19922step4 i j = -(raw19922step3 i j); unfold raw19922step4 raw19922step3; decide +kernel
      have hl : raw19922step4Labels = raw19922step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19922step4 raw19922step4Labels = mixedMoment B raw19922step5 raw19922step5Labels := by
      have ha : raw19922step5 = raw19922step4 := by apply Matrix.ext; unfold raw19922step5 raw19922step4; decide +kernel
      have hl : raw19922step4Labels = labelEmbedding1 ∘ raw19922step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19922step4 raw19922step4Labels raw19922step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1521 node1521Labels := by rfl

def raw19923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19923Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19923step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19923step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19923step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19923step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19923step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19923step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19923step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19923 raw19923Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19923 raw19923Labels = mixedMoment B raw19923step0 raw19923step0Labels := by
      have hz : ∀ j, raw19923 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19923step0 = (fun i j => raw19923 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19923step0 raw19923; decide +kernel
      have hl : raw19923step0Labels = raw19923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19923 raw19923Labels permutation520 hz
    mixedMoment B raw19923step0 raw19923step0Labels = mixedMoment B raw19923step1 raw19923step1Labels := by
      have hz : ∀ j, raw19923step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19923step1 = (fun i j => raw19923step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19923step1 raw19923step0; decide +kernel
      have hl : raw19923step1Labels = raw19923step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19923step0 raw19923step0Labels permutation104 hz
    mixedMoment B raw19923step1 raw19923step1Labels = mixedMoment B raw19923step2 raw19923step2Labels := by
      have ha : raw19923step2 = (fun i j => raw19923step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19923step2 raw19923step1; decide +kernel
      have hl : raw19923step2Labels = raw19923step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19923step1 raw19923step1Labels permutation29 permutation7
    mixedMoment B raw19923step2 raw19923step2Labels = mixedMoment B raw19923step3 raw19923step3Labels := by
      have ha : raw19923step3 = raw19923step2 := by apply Matrix.ext; unfold raw19923step3 raw19923step2; decide +kernel
      have hl : raw19923step2Labels = labelEmbedding1 ∘ raw19923step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19923step2 raw19923step2Labels raw19923step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

def raw19924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19924Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19924step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19924step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19924step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19924step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19924step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19924step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19924step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19924 raw19924Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19924 raw19924Labels = mixedMoment B raw19924step0 raw19924step0Labels := by
      have hz : ∀ j, raw19924 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19924step0 = (fun i j => raw19924 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19924step0 raw19924; decide +kernel
      have hl : raw19924step0Labels = raw19924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19924 raw19924Labels permutation520 hz
    mixedMoment B raw19924step0 raw19924step0Labels = mixedMoment B raw19924step1 raw19924step1Labels := by
      have hz : ∀ j, raw19924step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19924step1 = (fun i j => raw19924step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19924step1 raw19924step0; decide +kernel
      have hl : raw19924step1Labels = raw19924step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19924step0 raw19924step0Labels permutation80 hz
    mixedMoment B raw19924step1 raw19924step1Labels = mixedMoment B raw19924step2 raw19924step2Labels := by
      have ha : raw19924step2 = (fun i j => raw19924step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19924step2 raw19924step1; decide +kernel
      have hl : raw19924step2Labels = raw19924step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19924step1 raw19924step1Labels permutation29 permutation7
    mixedMoment B raw19924step2 raw19924step2Labels = mixedMoment B raw19924step3 raw19924step3Labels := by
      have ha : raw19924step3 = raw19924step2 := by apply Matrix.ext; unfold raw19924step3 raw19924step2; decide +kernel
      have hl : raw19924step2Labels = labelEmbedding1 ∘ raw19924step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19924step2 raw19924step2Labels raw19924step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

def raw19925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19925Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19925step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19925step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19925step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19925step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19925step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19925step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19925step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19925 raw19925Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19925 raw19925Labels = mixedMoment B raw19925step0 raw19925step0Labels := by
      have hz : ∀ j, raw19925 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19925step0 = (fun i j => raw19925 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19925step0 raw19925; decide +kernel
      have hl : raw19925step0Labels = raw19925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19925 raw19925Labels permutation434 hz
    mixedMoment B raw19925step0 raw19925step0Labels = mixedMoment B raw19925step1 raw19925step1Labels := by
      have hz : ∀ j, raw19925step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19925step1 = (fun i j => raw19925step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19925step1 raw19925step0; decide +kernel
      have hl : raw19925step1Labels = raw19925step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19925step0 raw19925step0Labels permutation80 hz
    mixedMoment B raw19925step1 raw19925step1Labels = mixedMoment B raw19925step2 raw19925step2Labels := by
      have ha : raw19925step2 = (fun i j => raw19925step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19925step2 raw19925step1; decide +kernel
      have hl : raw19925step2Labels = raw19925step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19925step1 raw19925step1Labels permutation29 permutation7
    mixedMoment B raw19925step2 raw19925step2Labels = mixedMoment B raw19925step3 raw19925step3Labels := by
      have ha : raw19925step3 = raw19925step2 := by apply Matrix.ext; unfold raw19925step3 raw19925step2; decide +kernel
      have hl : raw19925step2Labels = labelEmbedding1 ∘ raw19925step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19925step2 raw19925step2Labels raw19925step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

def raw19926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19926Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19926step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19926step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19926step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19926step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19926step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19926step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-3, 0, 3]]
def raw19926step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19926step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19926step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19926step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19926step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19926 raw19926Labels = mixedMoment B node1730 node1730Labels := by
  calc
    mixedMoment B raw19926 raw19926Labels = mixedMoment B raw19926step0 raw19926step0Labels := by
      have hz : ∀ j, raw19926 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19926step0 = (fun i j => raw19926 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19926step0 raw19926; decide +kernel
      have hl : raw19926step0Labels = raw19926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19926 raw19926Labels permutation520 hz
    mixedMoment B raw19926step0 raw19926step0Labels = mixedMoment B raw19926step1 raw19926step1Labels := by
      have hz : ∀ j, raw19926step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19926step1 = (fun i j => raw19926step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19926step1 raw19926step0; decide +kernel
      have hl : raw19926step1Labels = raw19926step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19926step0 raw19926step0Labels permutation104 hz
    mixedMoment B raw19926step1 raw19926step1Labels = mixedMoment B raw19926step2 raw19926step2Labels := by
      have hz : ∀ j, raw19926step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19926step2 = (fun i j => raw19926step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19926step2 raw19926step1; decide +kernel
      have hl : raw19926step2Labels = raw19926step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19926step1 raw19926step1Labels permutation20 hz
    mixedMoment B raw19926step2 raw19926step2Labels = mixedMoment B raw19926step3 raw19926step3Labels := by
      have ha : raw19926step3 = (fun i j => raw19926step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19926step3 raw19926step2; decide +kernel
      have hl : raw19926step3Labels = raw19926step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19926step2 raw19926step2Labels permutation2 permutation7
    mixedMoment B raw19926step3 raw19926step3Labels = mixedMoment B raw19926step4 raw19926step4Labels := by
      have ha : raw19926step4 = -raw19926step3 := by apply Matrix.ext; change ∀ i j, raw19926step4 i j = -(raw19926step3 i j); unfold raw19926step4 raw19926step3; decide +kernel
      have hl : raw19926step4Labels = raw19926step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19926step4 raw19926step4Labels = mixedMoment B raw19926step5 raw19926step5Labels := by
      have ha : raw19926step5 = raw19926step4 := by apply Matrix.ext; unfold raw19926step5 raw19926step4; decide +kernel
      have hl : raw19926step4Labels = labelEmbedding1 ∘ raw19926step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19926step4 raw19926step4Labels raw19926step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1730 node1730Labels := by rfl

def raw19927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19927Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19927step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19927step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19927step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19927step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19927step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19927step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-3, -1, 4]]
def raw19927step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19927step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19927step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19927step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19927step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19927 raw19927Labels = mixedMoment B node1521 node1521Labels := by
  calc
    mixedMoment B raw19927 raw19927Labels = mixedMoment B raw19927step0 raw19927step0Labels := by
      have hz : ∀ j, raw19927 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19927step0 = (fun i j => raw19927 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19927step0 raw19927; decide +kernel
      have hl : raw19927step0Labels = raw19927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19927 raw19927Labels permutation520 hz
    mixedMoment B raw19927step0 raw19927step0Labels = mixedMoment B raw19927step1 raw19927step1Labels := by
      have hz : ∀ j, raw19927step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19927step1 = (fun i j => raw19927step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19927step1 raw19927step0; decide +kernel
      have hl : raw19927step1Labels = raw19927step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19927step0 raw19927step0Labels permutation104 hz
    mixedMoment B raw19927step1 raw19927step1Labels = mixedMoment B raw19927step2 raw19927step2Labels := by
      have hz : ∀ j, raw19927step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19927step2 = (fun i j => raw19927step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19927step2 raw19927step1; decide +kernel
      have hl : raw19927step2Labels = raw19927step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19927step1 raw19927step1Labels permutation14 hz
    mixedMoment B raw19927step2 raw19927step2Labels = mixedMoment B raw19927step3 raw19927step3Labels := by
      have ha : raw19927step3 = (fun i j => raw19927step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19927step3 raw19927step2; decide +kernel
      have hl : raw19927step3Labels = raw19927step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19927step2 raw19927step2Labels permutation2 permutation7
    mixedMoment B raw19927step3 raw19927step3Labels = mixedMoment B raw19927step4 raw19927step4Labels := by
      have ha : raw19927step4 = -raw19927step3 := by apply Matrix.ext; change ∀ i j, raw19927step4 i j = -(raw19927step3 i j); unfold raw19927step4 raw19927step3; decide +kernel
      have hl : raw19927step4Labels = raw19927step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19927step4 raw19927step4Labels = mixedMoment B raw19927step5 raw19927step5Labels := by
      have ha : raw19927step5 = raw19927step4 := by apply Matrix.ext; unfold raw19927step5 raw19927step4; decide +kernel
      have hl : raw19927step4Labels = labelEmbedding1 ∘ raw19927step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19927step4 raw19927step4Labels raw19927step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1521 node1521Labels := by rfl

def raw19928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19928Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19928step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19928step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19928step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19928step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19928step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19928step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19928 raw19928Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19928 raw19928Labels = mixedMoment B raw19928step0 raw19928step0Labels := by
      have hz : ∀ j, raw19928 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19928step0 = (fun i j => raw19928 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19928step0 raw19928; decide +kernel
      have hl : raw19928step0Labels = raw19928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19928 raw19928Labels permutation520 hz
    mixedMoment B raw19928step0 raw19928step0Labels = mixedMoment B raw19928step1 raw19928step1Labels := by
      have hz : ∀ j, raw19928step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19928step1 = (fun i j => raw19928step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19928step1 raw19928step0; decide +kernel
      have hl : raw19928step1Labels = raw19928step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19928step0 raw19928step0Labels permutation104 hz
    mixedMoment B raw19928step1 raw19928step1Labels = mixedMoment B raw19928step2 raw19928step2Labels := by
      have ha : raw19928step2 = (fun i j => raw19928step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19928step2 raw19928step1; decide +kernel
      have hl : raw19928step2Labels = raw19928step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19928step1 raw19928step1Labels permutation31 permutation7
    mixedMoment B raw19928step2 raw19928step2Labels = mixedMoment B raw19928step3 raw19928step3Labels := by
      have ha : raw19928step3 = raw19928step2 := by apply Matrix.ext; unfold raw19928step3 raw19928step2; decide +kernel
      have hl : raw19928step2Labels = labelEmbedding1 ∘ raw19928step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19928step2 raw19928step2Labels raw19928step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

def raw19929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19929Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19929step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19929step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19929step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19929step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19929step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19929step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19929step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19929 raw19929Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19929 raw19929Labels = mixedMoment B raw19929step0 raw19929step0Labels := by
      have hz : ∀ j, raw19929 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19929step0 = (fun i j => raw19929 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19929step0 raw19929; decide +kernel
      have hl : raw19929step0Labels = raw19929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19929 raw19929Labels permutation520 hz
    mixedMoment B raw19929step0 raw19929step0Labels = mixedMoment B raw19929step1 raw19929step1Labels := by
      have hz : ∀ j, raw19929step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19929step1 = (fun i j => raw19929step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19929step1 raw19929step0; decide +kernel
      have hl : raw19929step1Labels = raw19929step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19929step0 raw19929step0Labels permutation56 hz
    mixedMoment B raw19929step1 raw19929step1Labels = mixedMoment B raw19929step2 raw19929step2Labels := by
      have ha : raw19929step2 = (fun i j => raw19929step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19929step2 raw19929step1; decide +kernel
      have hl : raw19929step2Labels = raw19929step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19929step1 raw19929step1Labels permutation29 permutation7
    mixedMoment B raw19929step2 raw19929step2Labels = mixedMoment B raw19929step3 raw19929step3Labels := by
      have ha : raw19929step3 = raw19929step2 := by apply Matrix.ext; unfold raw19929step3 raw19929step2; decide +kernel
      have hl : raw19929step2Labels = labelEmbedding1 ∘ raw19929step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19929step2 raw19929step2Labels raw19929step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

def raw19930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19930Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19930step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19930step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19930step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19930step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19930step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19930step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19930 raw19930Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19930 raw19930Labels = mixedMoment B raw19930step0 raw19930step0Labels := by
      have hz : ∀ j, raw19930 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19930step0 = (fun i j => raw19930 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19930step0 raw19930; decide +kernel
      have hl : raw19930step0Labels = raw19930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19930 raw19930Labels permutation434 hz
    mixedMoment B raw19930step0 raw19930step0Labels = mixedMoment B raw19930step1 raw19930step1Labels := by
      have hz : ∀ j, raw19930step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19930step1 = (fun i j => raw19930step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19930step1 raw19930step0; decide +kernel
      have hl : raw19930step1Labels = raw19930step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19930step0 raw19930step0Labels permutation56 hz
    mixedMoment B raw19930step1 raw19930step1Labels = mixedMoment B raw19930step2 raw19930step2Labels := by
      have ha : raw19930step2 = (fun i j => raw19930step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19930step2 raw19930step1; decide +kernel
      have hl : raw19930step2Labels = raw19930step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19930step1 raw19930step1Labels permutation29 permutation7
    mixedMoment B raw19930step2 raw19930step2Labels = mixedMoment B raw19930step3 raw19930step3Labels := by
      have ha : raw19930step3 = raw19930step2 := by apply Matrix.ext; unfold raw19930step3 raw19930step2; decide +kernel
      have hl : raw19930step2Labels = labelEmbedding1 ∘ raw19930step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19930step2 raw19930step2Labels raw19930step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

def raw19931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19931Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19931step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19931step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw19931step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19931step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19931step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19931step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-3, 0, 3]]
def raw19931step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19931step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19931step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19931step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19931step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19931 raw19931Labels = mixedMoment B node1730 node1730Labels := by
  calc
    mixedMoment B raw19931 raw19931Labels = mixedMoment B raw19931step0 raw19931step0Labels := by
      have hz : ∀ j, raw19931 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19931step0 = (fun i j => raw19931 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19931step0 raw19931; decide +kernel
      have hl : raw19931step0Labels = raw19931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19931 raw19931Labels permutation520 hz
    mixedMoment B raw19931step0 raw19931step0Labels = mixedMoment B raw19931step1 raw19931step1Labels := by
      have hz : ∀ j, raw19931step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19931step1 = (fun i j => raw19931step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19931step1 raw19931step0; decide +kernel
      have hl : raw19931step1Labels = raw19931step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19931step0 raw19931step0Labels permutation104 hz
    mixedMoment B raw19931step1 raw19931step1Labels = mixedMoment B raw19931step2 raw19931step2Labels := by
      have hz : ∀ j, raw19931step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19931step2 = (fun i j => raw19931step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19931step2 raw19931step1; decide +kernel
      have hl : raw19931step2Labels = raw19931step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19931step1 raw19931step1Labels permutation14 hz
    mixedMoment B raw19931step2 raw19931step2Labels = mixedMoment B raw19931step3 raw19931step3Labels := by
      have ha : raw19931step3 = (fun i j => raw19931step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19931step3 raw19931step2; decide +kernel
      have hl : raw19931step3Labels = raw19931step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19931step2 raw19931step2Labels permutation2 permutation7
    mixedMoment B raw19931step3 raw19931step3Labels = mixedMoment B raw19931step4 raw19931step4Labels := by
      have ha : raw19931step4 = -raw19931step3 := by apply Matrix.ext; change ∀ i j, raw19931step4 i j = -(raw19931step3 i j); unfold raw19931step4 raw19931step3; decide +kernel
      have hl : raw19931step4Labels = raw19931step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19931step4 raw19931step4Labels = mixedMoment B raw19931step5 raw19931step5Labels := by
      have ha : raw19931step5 = raw19931step4 := by apply Matrix.ext; unfold raw19931step5 raw19931step4; decide +kernel
      have hl : raw19931step4Labels = labelEmbedding1 ∘ raw19931step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19931step4 raw19931step4Labels raw19931step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1730 node1730Labels := by rfl

def raw19932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19932Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19932step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19932step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19932step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19932step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19932step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-3, -1, 4]]
def raw19932step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19932step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19932step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19932step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19932step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19932 raw19932Labels = mixedMoment B node1521 node1521Labels := by
  calc
    mixedMoment B raw19932 raw19932Labels = mixedMoment B raw19932step0 raw19932step0Labels := by
      have hz : ∀ j, raw19932 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19932step0 = (fun i j => raw19932 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19932step0 raw19932; decide +kernel
      have hl : raw19932step0Labels = raw19932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19932 raw19932Labels permutation520 hz
    mixedMoment B raw19932step0 raw19932step0Labels = mixedMoment B raw19932step1 raw19932step1Labels := by
      have hz : ∀ j, raw19932step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19932step1 = (fun i j => raw19932step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19932step1 raw19932step0; decide +kernel
      have hl : raw19932step1Labels = raw19932step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19932step0 raw19932step0Labels permutation80 hz
    mixedMoment B raw19932step1 raw19932step1Labels = mixedMoment B raw19932step2 raw19932step2Labels := by
      have hz : ∀ j, raw19932step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19932step2 = (fun i j => raw19932step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19932step2 raw19932step1; decide +kernel
      have hl : raw19932step2Labels = raw19932step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19932step1 raw19932step1Labels permutation14 hz
    mixedMoment B raw19932step2 raw19932step2Labels = mixedMoment B raw19932step3 raw19932step3Labels := by
      have ha : raw19932step3 = (fun i j => raw19932step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19932step3 raw19932step2; decide +kernel
      have hl : raw19932step3Labels = raw19932step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19932step2 raw19932step2Labels permutation2 permutation7
    mixedMoment B raw19932step3 raw19932step3Labels = mixedMoment B raw19932step4 raw19932step4Labels := by
      have ha : raw19932step4 = -raw19932step3 := by apply Matrix.ext; change ∀ i j, raw19932step4 i j = -(raw19932step3 i j); unfold raw19932step4 raw19932step3; decide +kernel
      have hl : raw19932step4Labels = raw19932step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19932step4 raw19932step4Labels = mixedMoment B raw19932step5 raw19932step5Labels := by
      have ha : raw19932step5 = raw19932step4 := by apply Matrix.ext; unfold raw19932step5 raw19932step4; decide +kernel
      have hl : raw19932step4Labels = labelEmbedding1 ∘ raw19932step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19932step4 raw19932step4Labels raw19932step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1521 node1521Labels := by rfl

def raw19933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19933Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19933step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19933step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19933step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19933step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19933step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19933step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19933 raw19933Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19933 raw19933Labels = mixedMoment B raw19933step0 raw19933step0Labels := by
      have hz : ∀ j, raw19933 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19933step0 = (fun i j => raw19933 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19933step0 raw19933; decide +kernel
      have hl : raw19933step0Labels = raw19933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19933 raw19933Labels permutation520 hz
    mixedMoment B raw19933step0 raw19933step0Labels = mixedMoment B raw19933step1 raw19933step1Labels := by
      have hz : ∀ j, raw19933step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19933step1 = (fun i j => raw19933step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19933step1 raw19933step0; decide +kernel
      have hl : raw19933step1Labels = raw19933step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19933step0 raw19933step0Labels permutation80 hz
    mixedMoment B raw19933step1 raw19933step1Labels = mixedMoment B raw19933step2 raw19933step2Labels := by
      have ha : raw19933step2 = (fun i j => raw19933step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19933step2 raw19933step1; decide +kernel
      have hl : raw19933step2Labels = raw19933step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19933step1 raw19933step1Labels permutation31 permutation7
    mixedMoment B raw19933step2 raw19933step2Labels = mixedMoment B raw19933step3 raw19933step3Labels := by
      have ha : raw19933step3 = raw19933step2 := by apply Matrix.ext; unfold raw19933step3 raw19933step2; decide +kernel
      have hl : raw19933step2Labels = labelEmbedding1 ∘ raw19933step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19933step2 raw19933step2Labels raw19933step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

def raw19934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19934Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19934step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19934step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19934step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19934step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19934step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19934 raw19934Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19934 raw19934Labels = mixedMoment B raw19934step0 raw19934step0Labels := by
      have hz : ∀ j, raw19934 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19934step0 = (fun i j => raw19934 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19934step0 raw19934; decide +kernel
      have hl : raw19934step0Labels = raw19934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19934 raw19934Labels permutation520 hz
    mixedMoment B raw19934step0 raw19934step0Labels = mixedMoment B raw19934step1 raw19934step1Labels := by
      have hz : ∀ j, raw19934step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19934step1 = (fun i j => raw19934step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19934step1 raw19934step0; decide +kernel
      have hl : raw19934step1Labels = raw19934step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19934step0 raw19934step0Labels permutation56 hz
    mixedMoment B raw19934step1 raw19934step1Labels = mixedMoment B raw19934step2 raw19934step2Labels := by
      have ha : raw19934step2 = (fun i j => raw19934step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19934step2 raw19934step1; decide +kernel
      have hl : raw19934step2Labels = raw19934step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19934step1 raw19934step1Labels permutation31 permutation7
    mixedMoment B raw19934step2 raw19934step2Labels = mixedMoment B raw19934step3 raw19934step3Labels := by
      have ha : raw19934step3 = raw19934step2 := by apply Matrix.ext; unfold raw19934step3 raw19934step2; decide +kernel
      have hl : raw19934step2Labels = labelEmbedding1 ∘ raw19934step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19934step2 raw19934step2Labels raw19934step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

def raw19935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19935Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19935step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19935step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![4, -1, -3]]
def raw19935step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19935step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19935step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19935step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19935step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19935 raw19935Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19935 raw19935Labels = mixedMoment B raw19935step0 raw19935step0Labels := by
      have hz : ∀ j, raw19935 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19935step0 = (fun i j => raw19935 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19935step0 raw19935; decide +kernel
      have hl : raw19935step0Labels = raw19935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19935 raw19935Labels permutation346 hz
    mixedMoment B raw19935step0 raw19935step0Labels = mixedMoment B raw19935step1 raw19935step1Labels := by
      have hz : ∀ j, raw19935step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19935step1 = (fun i j => raw19935step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19935step1 raw19935step0; decide +kernel
      have hl : raw19935step1Labels = raw19935step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19935step0 raw19935step0Labels permutation56 hz
    mixedMoment B raw19935step1 raw19935step1Labels = mixedMoment B raw19935step2 raw19935step2Labels := by
      have ha : raw19935step2 = (fun i j => raw19935step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19935step2 raw19935step1; decide +kernel
      have hl : raw19935step2Labels = raw19935step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19935step1 raw19935step1Labels permutation29 permutation7
    mixedMoment B raw19935step2 raw19935step2Labels = mixedMoment B raw19935step3 raw19935step3Labels := by
      have ha : raw19935step3 = raw19935step2 := by apply Matrix.ext; unfold raw19935step3 raw19935step2; decide +kernel
      have hl : raw19935step2Labels = labelEmbedding1 ∘ raw19935step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19935step2 raw19935step2Labels raw19935step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

def raw19936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw19936Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw19936step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw19936step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19936step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19936step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19936step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-3, 0, 3]]
def raw19936step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19936step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19936step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19936step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19936step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19936 raw19936Labels = mixedMoment B node1730 node1730Labels := by
  calc
    mixedMoment B raw19936 raw19936Labels = mixedMoment B raw19936step0 raw19936step0Labels := by
      have hz : ∀ j, raw19936 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19936step0 = (fun i j => raw19936 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19936step0 raw19936; decide +kernel
      have hl : raw19936step0Labels = raw19936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19936 raw19936Labels permutation520 hz
    mixedMoment B raw19936step0 raw19936step0Labels = mixedMoment B raw19936step1 raw19936step1Labels := by
      have hz : ∀ j, raw19936step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19936step1 = (fun i j => raw19936step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19936step1 raw19936step0; decide +kernel
      have hl : raw19936step1Labels = raw19936step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19936step0 raw19936step0Labels permutation80 hz
    mixedMoment B raw19936step1 raw19936step1Labels = mixedMoment B raw19936step2 raw19936step2Labels := by
      have hz : ∀ j, raw19936step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19936step2 = (fun i j => raw19936step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19936step2 raw19936step1; decide +kernel
      have hl : raw19936step2Labels = raw19936step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19936step1 raw19936step1Labels permutation14 hz
    mixedMoment B raw19936step2 raw19936step2Labels = mixedMoment B raw19936step3 raw19936step3Labels := by
      have ha : raw19936step3 = (fun i j => raw19936step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19936step3 raw19936step2; decide +kernel
      have hl : raw19936step3Labels = raw19936step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19936step2 raw19936step2Labels permutation2 permutation7
    mixedMoment B raw19936step3 raw19936step3Labels = mixedMoment B raw19936step4 raw19936step4Labels := by
      have ha : raw19936step4 = -raw19936step3 := by apply Matrix.ext; change ∀ i j, raw19936step4 i j = -(raw19936step3 i j); unfold raw19936step4 raw19936step3; decide +kernel
      have hl : raw19936step4Labels = raw19936step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19936step4 raw19936step4Labels = mixedMoment B raw19936step5 raw19936step5Labels := by
      have ha : raw19936step5 = raw19936step4 := by apply Matrix.ext; unfold raw19936step5 raw19936step4; decide +kernel
      have hl : raw19936step4Labels = labelEmbedding1 ∘ raw19936step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19936step4 raw19936step4Labels raw19936step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1730 node1730Labels := by rfl

def raw19937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19937Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19937step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19937step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19937step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19937step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19937step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-3, -1, 4]]
def raw19937step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19937step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19937step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19937step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19937step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19937 raw19937Labels = mixedMoment B node1521 node1521Labels := by
  calc
    mixedMoment B raw19937 raw19937Labels = mixedMoment B raw19937step0 raw19937step0Labels := by
      have hz : ∀ j, raw19937 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19937step0 = (fun i j => raw19937 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19937step0 raw19937; decide +kernel
      have hl : raw19937step0Labels = raw19937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19937 raw19937Labels permutation434 hz
    mixedMoment B raw19937step0 raw19937step0Labels = mixedMoment B raw19937step1 raw19937step1Labels := by
      have hz : ∀ j, raw19937step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19937step1 = (fun i j => raw19937step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19937step1 raw19937step0; decide +kernel
      have hl : raw19937step1Labels = raw19937step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19937step0 raw19937step0Labels permutation80 hz
    mixedMoment B raw19937step1 raw19937step1Labels = mixedMoment B raw19937step2 raw19937step2Labels := by
      have hz : ∀ j, raw19937step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19937step2 = (fun i j => raw19937step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19937step2 raw19937step1; decide +kernel
      have hl : raw19937step2Labels = raw19937step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19937step1 raw19937step1Labels permutation14 hz
    mixedMoment B raw19937step2 raw19937step2Labels = mixedMoment B raw19937step3 raw19937step3Labels := by
      have ha : raw19937step3 = (fun i j => raw19937step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19937step3 raw19937step2; decide +kernel
      have hl : raw19937step3Labels = raw19937step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19937step2 raw19937step2Labels permutation2 permutation7
    mixedMoment B raw19937step3 raw19937step3Labels = mixedMoment B raw19937step4 raw19937step4Labels := by
      have ha : raw19937step4 = -raw19937step3 := by apply Matrix.ext; change ∀ i j, raw19937step4 i j = -(raw19937step3 i j); unfold raw19937step4 raw19937step3; decide +kernel
      have hl : raw19937step4Labels = raw19937step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19937step4 raw19937step4Labels = mixedMoment B raw19937step5 raw19937step5Labels := by
      have ha : raw19937step5 = raw19937step4 := by apply Matrix.ext; unfold raw19937step5 raw19937step4; decide +kernel
      have hl : raw19937step4Labels = labelEmbedding1 ∘ raw19937step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19937step4 raw19937step4Labels raw19937step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1521 node1521Labels := by rfl

def raw19938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19938Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19938step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19938step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19938step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19938step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19938step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19938step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19938 raw19938Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19938 raw19938Labels = mixedMoment B raw19938step0 raw19938step0Labels := by
      have hz : ∀ j, raw19938 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19938step0 = (fun i j => raw19938 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19938step0 raw19938; decide +kernel
      have hl : raw19938step0Labels = raw19938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19938 raw19938Labels permutation434 hz
    mixedMoment B raw19938step0 raw19938step0Labels = mixedMoment B raw19938step1 raw19938step1Labels := by
      have hz : ∀ j, raw19938step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19938step1 = (fun i j => raw19938step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19938step1 raw19938step0; decide +kernel
      have hl : raw19938step1Labels = raw19938step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19938step0 raw19938step0Labels permutation80 hz
    mixedMoment B raw19938step1 raw19938step1Labels = mixedMoment B raw19938step2 raw19938step2Labels := by
      have ha : raw19938step2 = (fun i j => raw19938step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19938step2 raw19938step1; decide +kernel
      have hl : raw19938step2Labels = raw19938step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19938step1 raw19938step1Labels permutation31 permutation7
    mixedMoment B raw19938step2 raw19938step2Labels = mixedMoment B raw19938step3 raw19938step3Labels := by
      have ha : raw19938step3 = raw19938step2 := by apply Matrix.ext; unfold raw19938step3 raw19938step2; decide +kernel
      have hl : raw19938step2Labels = labelEmbedding1 ∘ raw19938step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19938step2 raw19938step2Labels raw19938step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

def raw19939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19939Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19939step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19939step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19939step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19939step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19939step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19939 raw19939Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19939 raw19939Labels = mixedMoment B raw19939step0 raw19939step0Labels := by
      have hz : ∀ j, raw19939 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19939step0 = (fun i j => raw19939 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19939step0 raw19939; decide +kernel
      have hl : raw19939step0Labels = raw19939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19939 raw19939Labels permutation434 hz
    mixedMoment B raw19939step0 raw19939step0Labels = mixedMoment B raw19939step1 raw19939step1Labels := by
      have hz : ∀ j, raw19939step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19939step1 = (fun i j => raw19939step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19939step1 raw19939step0; decide +kernel
      have hl : raw19939step1Labels = raw19939step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19939step0 raw19939step0Labels permutation56 hz
    mixedMoment B raw19939step1 raw19939step1Labels = mixedMoment B raw19939step2 raw19939step2Labels := by
      have ha : raw19939step2 = (fun i j => raw19939step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19939step2 raw19939step1; decide +kernel
      have hl : raw19939step2Labels = raw19939step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19939step1 raw19939step1Labels permutation31 permutation7
    mixedMoment B raw19939step2 raw19939step2Labels = mixedMoment B raw19939step3 raw19939step3Labels := by
      have ha : raw19939step3 = raw19939step2 := by apply Matrix.ext; unfold raw19939step3 raw19939step2; decide +kernel
      have hl : raw19939step2Labels = labelEmbedding1 ∘ raw19939step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19939step2 raw19939step2Labels raw19939step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

def raw19940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19940Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19940step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19940step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19940step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19940step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19940step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19940step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![3, 1, -4]]
def raw19940step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19940 raw19940Labels = mixedMoment B node1677 node1677Labels := by
  calc
    mixedMoment B raw19940 raw19940Labels = mixedMoment B raw19940step0 raw19940step0Labels := by
      have hz : ∀ j, raw19940 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19940step0 = (fun i j => raw19940 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19940step0 raw19940; decide +kernel
      have hl : raw19940step0Labels = raw19940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19940 raw19940Labels permutation346 hz
    mixedMoment B raw19940step0 raw19940step0Labels = mixedMoment B raw19940step1 raw19940step1Labels := by
      have hz : ∀ j, raw19940step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19940step1 = (fun i j => raw19940step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19940step1 raw19940step0; decide +kernel
      have hl : raw19940step1Labels = raw19940step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19940step0 raw19940step0Labels permutation56 hz
    mixedMoment B raw19940step1 raw19940step1Labels = mixedMoment B raw19940step2 raw19940step2Labels := by
      have ha : raw19940step2 = (fun i j => raw19940step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19940step2 raw19940step1; decide +kernel
      have hl : raw19940step2Labels = raw19940step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19940step1 raw19940step1Labels permutation31 permutation7
    mixedMoment B raw19940step2 raw19940step2Labels = mixedMoment B raw19940step3 raw19940step3Labels := by
      have ha : raw19940step3 = raw19940step2 := by apply Matrix.ext; unfold raw19940step3 raw19940step2; decide +kernel
      have hl : raw19940step2Labels = labelEmbedding1 ∘ raw19940step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19940step2 raw19940step2Labels raw19940step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1677 node1677Labels := by rfl

def raw19941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw19941Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw19941step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19941step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw19941step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19941step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19941step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19941step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-3, 0, 3]]
def raw19941step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19941step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19941step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19941step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![3, 0, -3]]
def raw19941step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19941 raw19941Labels = mixedMoment B node1730 node1730Labels := by
  calc
    mixedMoment B raw19941 raw19941Labels = mixedMoment B raw19941step0 raw19941step0Labels := by
      have hz : ∀ j, raw19941 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19941step0 = (fun i j => raw19941 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19941step0 raw19941; decide +kernel
      have hl : raw19941step0Labels = raw19941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19941 raw19941Labels permutation434 hz
    mixedMoment B raw19941step0 raw19941step0Labels = mixedMoment B raw19941step1 raw19941step1Labels := by
      have hz : ∀ j, raw19941step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19941step1 = (fun i j => raw19941step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19941step1 raw19941step0; decide +kernel
      have hl : raw19941step1Labels = raw19941step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19941step0 raw19941step0Labels permutation80 hz
    mixedMoment B raw19941step1 raw19941step1Labels = mixedMoment B raw19941step2 raw19941step2Labels := by
      have hz : ∀ j, raw19941step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19941step2 = (fun i j => raw19941step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19941step2 raw19941step1; decide +kernel
      have hl : raw19941step2Labels = raw19941step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19941step1 raw19941step1Labels permutation14 hz
    mixedMoment B raw19941step2 raw19941step2Labels = mixedMoment B raw19941step3 raw19941step3Labels := by
      have ha : raw19941step3 = (fun i j => raw19941step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19941step3 raw19941step2; decide +kernel
      have hl : raw19941step3Labels = raw19941step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19941step2 raw19941step2Labels permutation2 permutation7
    mixedMoment B raw19941step3 raw19941step3Labels = mixedMoment B raw19941step4 raw19941step4Labels := by
      have ha : raw19941step4 = -raw19941step3 := by apply Matrix.ext; change ∀ i j, raw19941step4 i j = -(raw19941step3 i j); unfold raw19941step4 raw19941step3; decide +kernel
      have hl : raw19941step4Labels = raw19941step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19941step4 raw19941step4Labels = mixedMoment B raw19941step5 raw19941step5Labels := by
      have ha : raw19941step5 = raw19941step4 := by apply Matrix.ext; unfold raw19941step5 raw19941step4; decide +kernel
      have hl : raw19941step4Labels = labelEmbedding1 ∘ raw19941step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19941step4 raw19941step4Labels raw19941step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1730 node1730Labels := by rfl

def raw19942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19942Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19942step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19942step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19942step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![5, -2, -3]]
def raw19942step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19942step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def raw19942step3Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19942step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -2, 5], ![3, 2, -5]]
def raw19942step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19942step5 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -2, 5], ![3, 2, -5]]
def raw19942step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19942 raw19942Labels = mixedMoment B node1541 node1541Labels := by
  calc
    mixedMoment B raw19942 raw19942Labels = mixedMoment B raw19942step0 raw19942step0Labels := by
      have hz : ∀ j, raw19942 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19942step0 = (fun i j => raw19942 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19942step0 raw19942; decide +kernel
      have hl : raw19942step0Labels = raw19942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19942 raw19942Labels permutation520 hz
    mixedMoment B raw19942step0 raw19942step0Labels = mixedMoment B raw19942step1 raw19942step1Labels := by
      have hz : ∀ j, raw19942step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19942step1 = (fun i j => raw19942step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19942step1 raw19942step0; decide +kernel
      have hl : raw19942step1Labels = raw19942step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19942step0 raw19942step0Labels permutation104 hz
    mixedMoment B raw19942step1 raw19942step1Labels = mixedMoment B raw19942step2 raw19942step2Labels := by
      have hz : ∀ j, raw19942step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19942step2 = (fun i j => raw19942step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19942step2 raw19942step1; decide +kernel
      have hl : raw19942step2Labels = raw19942step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19942step1 raw19942step1Labels permutation20 hz
    mixedMoment B raw19942step2 raw19942step2Labels = mixedMoment B raw19942step3 raw19942step3Labels := by
      have hz : ∀ j, raw19942step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19942step3 = (fun i j => raw19942step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19942step3 raw19942step2; decide +kernel
      have hl : raw19942step3Labels = raw19942step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19942step2 raw19942step2Labels permutation4 hz
    mixedMoment B raw19942step3 raw19942step3Labels = mixedMoment B raw19942step4 raw19942step4Labels := by
      have ha : raw19942step4 = (fun i j => raw19942step3 (permutation1 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19942step4 raw19942step3; decide +kernel
      have hl : raw19942step4Labels = raw19942step3Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19942step3 raw19942step3Labels permutation1 permutation7
    mixedMoment B raw19942step4 raw19942step4Labels = mixedMoment B raw19942step5 raw19942step5Labels := by
      have ha : raw19942step5 = raw19942step4 := by apply Matrix.ext; unfold raw19942step5 raw19942step4; decide +kernel
      have hl : raw19942step4Labels = labelEmbedding1 ∘ raw19942step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19942step4 raw19942step4Labels raw19942step5Labels labelEmbedding1 hl
    _ = mixedMoment B node1541 node1541Labels := by rfl

def raw19943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19943Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19943step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19943step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19943step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![5, -2, -3]]
def raw19943step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19943step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19943step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19943step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19943step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19943 raw19943Labels = mixedMoment B node1521 node1521Labels := by
  calc
    mixedMoment B raw19943 raw19943Labels = mixedMoment B raw19943step0 raw19943step0Labels := by
      have hz : ∀ j, raw19943 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19943step0 = (fun i j => raw19943 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19943step0 raw19943; decide +kernel
      have hl : raw19943step0Labels = raw19943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19943 raw19943Labels permutation520 hz
    mixedMoment B raw19943step0 raw19943step0Labels = mixedMoment B raw19943step1 raw19943step1Labels := by
      have hz : ∀ j, raw19943step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19943step1 = (fun i j => raw19943step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19943step1 raw19943step0; decide +kernel
      have hl : raw19943step1Labels = raw19943step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19943step0 raw19943step0Labels permutation104 hz
    mixedMoment B raw19943step1 raw19943step1Labels = mixedMoment B raw19943step2 raw19943step2Labels := by
      have hz : ∀ j, raw19943step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19943step2 = (fun i j => raw19943step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19943step2 raw19943step1; decide +kernel
      have hl : raw19943step2Labels = raw19943step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19943step1 raw19943step1Labels permutation20 hz
    mixedMoment B raw19943step2 raw19943step2Labels = mixedMoment B raw19943step3 raw19943step3Labels := by
      have ha : raw19943step3 = (fun i j => raw19943step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19943step3 raw19943step2; decide +kernel
      have hl : raw19943step3Labels = raw19943step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19943step2 raw19943step2Labels permutation7 permutation7
    mixedMoment B raw19943step3 raw19943step3Labels = mixedMoment B raw19943step4 raw19943step4Labels := by
      have ha : raw19943step4 = raw19943step3 := by apply Matrix.ext; unfold raw19943step4 raw19943step3; decide +kernel
      have hl : raw19943step3Labels = labelEmbedding1 ∘ raw19943step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19943step3 raw19943step3Labels raw19943step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1521 node1521Labels := by rfl

def raw19944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19944Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19944step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19944step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![5, -2, -3]]
def raw19944step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19944step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![5, -2, -3]]
def raw19944step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19944step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19944step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19944step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19944step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19944 raw19944Labels = mixedMoment B node1521 node1521Labels := by
  calc
    mixedMoment B raw19944 raw19944Labels = mixedMoment B raw19944step0 raw19944step0Labels := by
      have hz : ∀ j, raw19944 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19944step0 = (fun i j => raw19944 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19944step0 raw19944; decide +kernel
      have hl : raw19944step0Labels = raw19944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19944 raw19944Labels permutation520 hz
    mixedMoment B raw19944step0 raw19944step0Labels = mixedMoment B raw19944step1 raw19944step1Labels := by
      have hz : ∀ j, raw19944step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19944step1 = (fun i j => raw19944step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19944step1 raw19944step0; decide +kernel
      have hl : raw19944step1Labels = raw19944step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19944step0 raw19944step0Labels permutation104 hz
    mixedMoment B raw19944step1 raw19944step1Labels = mixedMoment B raw19944step2 raw19944step2Labels := by
      have hz : ∀ j, raw19944step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19944step2 = (fun i j => raw19944step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19944step2 raw19944step1; decide +kernel
      have hl : raw19944step2Labels = raw19944step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19944step1 raw19944step1Labels permutation14 hz
    mixedMoment B raw19944step2 raw19944step2Labels = mixedMoment B raw19944step3 raw19944step3Labels := by
      have ha : raw19944step3 = (fun i j => raw19944step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19944step3 raw19944step2; decide +kernel
      have hl : raw19944step3Labels = raw19944step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19944step2 raw19944step2Labels permutation7 permutation7
    mixedMoment B raw19944step3 raw19944step3Labels = mixedMoment B raw19944step4 raw19944step4Labels := by
      have ha : raw19944step4 = raw19944step3 := by apply Matrix.ext; unfold raw19944step4 raw19944step3; decide +kernel
      have hl : raw19944step3Labels = labelEmbedding1 ∘ raw19944step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19944step3 raw19944step3Labels raw19944step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1521 node1521Labels := by rfl

def raw19945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19945Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -2, -3]]
def raw19945step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19945step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![5, -2, -3]]
def raw19945step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19945step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![5, -2, -3]]
def raw19945step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19945step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19945step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19945step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19945step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19945 raw19945Labels = mixedMoment B node1521 node1521Labels := by
  calc
    mixedMoment B raw19945 raw19945Labels = mixedMoment B raw19945step0 raw19945step0Labels := by
      have hz : ∀ j, raw19945 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19945step0 = (fun i j => raw19945 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19945step0 raw19945; decide +kernel
      have hl : raw19945step0Labels = raw19945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19945 raw19945Labels permutation520 hz
    mixedMoment B raw19945step0 raw19945step0Labels = mixedMoment B raw19945step1 raw19945step1Labels := by
      have hz : ∀ j, raw19945step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19945step1 = (fun i j => raw19945step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19945step1 raw19945step0; decide +kernel
      have hl : raw19945step1Labels = raw19945step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19945step0 raw19945step0Labels permutation80 hz
    mixedMoment B raw19945step1 raw19945step1Labels = mixedMoment B raw19945step2 raw19945step2Labels := by
      have hz : ∀ j, raw19945step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19945step2 = (fun i j => raw19945step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19945step2 raw19945step1; decide +kernel
      have hl : raw19945step2Labels = raw19945step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19945step1 raw19945step1Labels permutation14 hz
    mixedMoment B raw19945step2 raw19945step2Labels = mixedMoment B raw19945step3 raw19945step3Labels := by
      have ha : raw19945step3 = (fun i j => raw19945step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19945step3 raw19945step2; decide +kernel
      have hl : raw19945step3Labels = raw19945step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19945step2 raw19945step2Labels permutation7 permutation7
    mixedMoment B raw19945step3 raw19945step3Labels = mixedMoment B raw19945step4 raw19945step4Labels := by
      have ha : raw19945step4 = raw19945step3 := by apply Matrix.ext; unfold raw19945step4 raw19945step3; decide +kernel
      have hl : raw19945step3Labels = labelEmbedding1 ∘ raw19945step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19945step3 raw19945step3Labels raw19945step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1521 node1521Labels := by rfl

def raw19946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -2, -3]]
def raw19946Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -2, -3]]
def raw19946step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![5, -2, -3]]
def raw19946step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19946step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![5, -2, -3]]
def raw19946step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19946step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19946step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19946step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![3, 1, -4]]
def raw19946step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19946 raw19946Labels = mixedMoment B node1521 node1521Labels := by
  calc
    mixedMoment B raw19946 raw19946Labels = mixedMoment B raw19946step0 raw19946step0Labels := by
      have hz : ∀ j, raw19946 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19946step0 = (fun i j => raw19946 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19946step0 raw19946; decide +kernel
      have hl : raw19946step0Labels = raw19946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19946 raw19946Labels permutation434 hz
    mixedMoment B raw19946step0 raw19946step0Labels = mixedMoment B raw19946step1 raw19946step1Labels := by
      have hz : ∀ j, raw19946step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19946step1 = (fun i j => raw19946step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19946step1 raw19946step0; decide +kernel
      have hl : raw19946step1Labels = raw19946step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19946step0 raw19946step0Labels permutation80 hz
    mixedMoment B raw19946step1 raw19946step1Labels = mixedMoment B raw19946step2 raw19946step2Labels := by
      have hz : ∀ j, raw19946step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19946step2 = (fun i j => raw19946step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19946step2 raw19946step1; decide +kernel
      have hl : raw19946step2Labels = raw19946step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19946step1 raw19946step1Labels permutation14 hz
    mixedMoment B raw19946step2 raw19946step2Labels = mixedMoment B raw19946step3 raw19946step3Labels := by
      have ha : raw19946step3 = (fun i j => raw19946step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19946step3 raw19946step2; decide +kernel
      have hl : raw19946step3Labels = raw19946step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19946step2 raw19946step2Labels permutation7 permutation7
    mixedMoment B raw19946step3 raw19946step3Labels = mixedMoment B raw19946step4 raw19946step4Labels := by
      have ha : raw19946step4 = raw19946step3 := by apply Matrix.ext; unfold raw19946step4 raw19946step3; decide +kernel
      have hl : raw19946step3Labels = labelEmbedding1 ∘ raw19946step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19946step3 raw19946step3Labels raw19946step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1521 node1521Labels := by rfl

def raw19947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19947Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19947step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19947step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19947step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![4, -1, -3]]
def raw19947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19947step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 1, 3], ![4, -1, -3]]
def raw19947step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19947 raw19947Labels = mixedMoment B node1096 node1096Labels := by
  calc
    mixedMoment B raw19947 raw19947Labels = mixedMoment B raw19947step0 raw19947step0Labels := by
      have hz : ∀ j, raw19947 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19947step0 = (fun i j => raw19947 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19947step0 raw19947; decide +kernel
      have hl : raw19947step0Labels = raw19947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19947 raw19947Labels permutation520 hz
    mixedMoment B raw19947step0 raw19947step0Labels = mixedMoment B raw19947step1 raw19947step1Labels := by
      have hz : ∀ j, raw19947step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19947step1 = (fun i j => raw19947step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19947step1 raw19947step0; decide +kernel
      have hl : raw19947step1Labels = raw19947step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19947step0 raw19947step0Labels permutation104 hz
    mixedMoment B raw19947step1 raw19947step1Labels = mixedMoment B raw19947step2 raw19947step2Labels := by
      have hz : ∀ j, raw19947step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19947step2 = (fun i j => raw19947step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19947step2 raw19947step1; decide +kernel
      have hl : raw19947step2Labels = raw19947step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19947step1 raw19947step1Labels permutation20 hz
    mixedMoment B raw19947step2 raw19947step2Labels = mixedMoment B raw19947step3 raw19947step3Labels := by
      have hz : ∀ j, raw19947step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19947step3 = (fun i j => raw19947step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19947step3 raw19947step2; decide +kernel
      have hl : raw19947step3Labels = raw19947step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19947step2 raw19947step2Labels permutation4 hz
    _ = mixedMoment B node1096 node1096Labels := by rfl

def raw19948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19948Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19948step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19948step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19948step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19948step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19948 raw19948Labels = mixedMoment B node609 node609Labels := by
  calc
    mixedMoment B raw19948 raw19948Labels = mixedMoment B raw19948step0 raw19948step0Labels := by
      have hz : ∀ j, raw19948 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19948step0 = (fun i j => raw19948 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19948step0 raw19948; decide +kernel
      have hl : raw19948step0Labels = raw19948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19948 raw19948Labels permutation520 hz
    mixedMoment B raw19948step0 raw19948step0Labels = mixedMoment B raw19948step1 raw19948step1Labels := by
      have hz : ∀ j, raw19948step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19948step1 = (fun i j => raw19948step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19948step1 raw19948step0; decide +kernel
      have hl : raw19948step1Labels = raw19948step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19948step0 raw19948step0Labels permutation104 hz
    mixedMoment B raw19948step1 raw19948step1Labels = mixedMoment B raw19948step2 raw19948step2Labels := by
      have hz : ∀ j, raw19948step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19948step2 = (fun i j => raw19948step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19948step2 raw19948step1; decide +kernel
      have hl : raw19948step2Labels = raw19948step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19948step1 raw19948step1Labels permutation20 hz
    _ = mixedMoment B node609 node609Labels := by rfl

def raw19949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19949Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19949step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19949step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19949step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19949step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19949step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19949 raw19949Labels = mixedMoment B node609 node609Labels := by
  calc
    mixedMoment B raw19949 raw19949Labels = mixedMoment B raw19949step0 raw19949step0Labels := by
      have hz : ∀ j, raw19949 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19949step0 = (fun i j => raw19949 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19949step0 raw19949; decide +kernel
      have hl : raw19949step0Labels = raw19949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19949 raw19949Labels permutation520 hz
    mixedMoment B raw19949step0 raw19949step0Labels = mixedMoment B raw19949step1 raw19949step1Labels := by
      have hz : ∀ j, raw19949step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19949step1 = (fun i j => raw19949step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19949step1 raw19949step0; decide +kernel
      have hl : raw19949step1Labels = raw19949step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19949step0 raw19949step0Labels permutation104 hz
    mixedMoment B raw19949step1 raw19949step1Labels = mixedMoment B raw19949step2 raw19949step2Labels := by
      have hz : ∀ j, raw19949step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19949step2 = (fun i j => raw19949step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19949step2 raw19949step1; decide +kernel
      have hl : raw19949step2Labels = raw19949step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19949step1 raw19949step1Labels permutation14 hz
    _ = mixedMoment B node609 node609Labels := by rfl

def raw19950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -1, -3]]
def raw19950Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19950step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19950step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19950step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19950 raw19950Labels = mixedMoment B node609 node609Labels := by
  calc
    mixedMoment B raw19950 raw19950Labels = mixedMoment B raw19950step0 raw19950step0Labels := by
      have hz : ∀ j, raw19950 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19950step0 = (fun i j => raw19950 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19950step0 raw19950; decide +kernel
      have hl : raw19950step0Labels = raw19950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19950 raw19950Labels permutation520 hz
    mixedMoment B raw19950step0 raw19950step0Labels = mixedMoment B raw19950step1 raw19950step1Labels := by
      have hz : ∀ j, raw19950step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19950step1 = (fun i j => raw19950step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19950step1 raw19950step0; decide +kernel
      have hl : raw19950step1Labels = raw19950step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19950step0 raw19950step0Labels permutation80 hz
    mixedMoment B raw19950step1 raw19950step1Labels = mixedMoment B raw19950step2 raw19950step2Labels := by
      have hz : ∀ j, raw19950step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19950step2 = (fun i j => raw19950step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19950step2 raw19950step1; decide +kernel
      have hl : raw19950step2Labels = raw19950step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19950step1 raw19950step1Labels permutation14 hz
    _ = mixedMoment B node609 node609Labels := by rfl

def raw19951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19951Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19951step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw19951step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19951step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![4, -1, -3]]
def raw19951step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19951 raw19951Labels = mixedMoment B node609 node609Labels := by
  calc
    mixedMoment B raw19951 raw19951Labels = mixedMoment B raw19951step0 raw19951step0Labels := by
      have hz : ∀ j, raw19951 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19951step0 = (fun i j => raw19951 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19951step0 raw19951; decide +kernel
      have hl : raw19951step0Labels = raw19951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19951 raw19951Labels permutation434 hz
    mixedMoment B raw19951step0 raw19951step0Labels = mixedMoment B raw19951step1 raw19951step1Labels := by
      have hz : ∀ j, raw19951step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19951step1 = (fun i j => raw19951step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19951step1 raw19951step0; decide +kernel
      have hl : raw19951step1Labels = raw19951step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19951step0 raw19951step0Labels permutation80 hz
    mixedMoment B raw19951step1 raw19951step1Labels = mixedMoment B raw19951step2 raw19951step2Labels := by
      have hz : ∀ j, raw19951step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19951step2 = (fun i j => raw19951step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19951step2 raw19951step1; decide +kernel
      have hl : raw19951step2Labels = raw19951step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19951step1 raw19951step1Labels permutation14 hz
    _ = mixedMoment B node609 node609Labels := by rfl

def raw19952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19952Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19952step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![5, -2, -3]]
def raw19952step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19952step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![5, -2, -3]]
def raw19952step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19952step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def raw19952step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19952 raw19952Labels = mixedMoment B node622 node622Labels := by
  calc
    mixedMoment B raw19952 raw19952Labels = mixedMoment B raw19952step0 raw19952step0Labels := by
      have hz : ∀ j, raw19952 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19952step0 = (fun i j => raw19952 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19952step0 raw19952; decide +kernel
      have hl : raw19952step0Labels = raw19952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19952 raw19952Labels permutation520 hz
    mixedMoment B raw19952step0 raw19952step0Labels = mixedMoment B raw19952step1 raw19952step1Labels := by
      have hz : ∀ j, raw19952step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19952step1 = (fun i j => raw19952step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19952step1 raw19952step0; decide +kernel
      have hl : raw19952step1Labels = raw19952step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19952step0 raw19952step0Labels permutation104 hz
    mixedMoment B raw19952step1 raw19952step1Labels = mixedMoment B raw19952step2 raw19952step2Labels := by
      have hz : ∀ j, raw19952step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19952step2 = (fun i j => raw19952step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19952step2 raw19952step1; decide +kernel
      have hl : raw19952step2Labels = raw19952step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19952step1 raw19952step1Labels permutation20 hz
    mixedMoment B raw19952step2 raw19952step2Labels = mixedMoment B raw19952step3 raw19952step3Labels := by
      have hz : ∀ j, raw19952step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19952step3 = (fun i j => raw19952step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19952step3 raw19952step2; decide +kernel
      have hl : raw19952step3Labels = raw19952step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19952step2 raw19952step2Labels permutation4 hz
    _ = mixedMoment B node622 node622Labels := by rfl

def raw19953 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![3, -3]]
def raw19953Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19953step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![0, 0], ![3, -3]]
def raw19953step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19953step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![3, -3]]
def raw19953step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19953step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![3, -3]]
def raw19953step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw19953step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw19953step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19953 raw19953Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw19953 raw19953Labels = mixedMoment B raw19953step0 raw19953step0Labels := by
      have hz : ∀ j, raw19953 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19953step0 = (fun i j => raw19953 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19953step0 raw19953; decide +kernel
      have hl : raw19953step0Labels = raw19953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19953 raw19953Labels permutation520 hz
    mixedMoment B raw19953step0 raw19953step0Labels = mixedMoment B raw19953step1 raw19953step1Labels := by
      have hz : ∀ j, raw19953step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19953step1 = (fun i j => raw19953step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19953step1 raw19953step0; decide +kernel
      have hl : raw19953step1Labels = raw19953step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19953step0 raw19953step0Labels permutation104 hz
    mixedMoment B raw19953step1 raw19953step1Labels = mixedMoment B raw19953step2 raw19953step2Labels := by
      have hz : ∀ j, raw19953step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19953step2 = (fun i j => raw19953step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19953step2 raw19953step1; decide +kernel
      have hl : raw19953step2Labels = raw19953step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19953step1 raw19953step1Labels permutation20 hz
    mixedMoment B raw19953step2 raw19953step2Labels = mixedMoment B raw19953step3 raw19953step3Labels := by
      have hz : ∀ j, raw19953step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19953step3 = (fun i j => raw19953step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19953step3 raw19953step2; decide +kernel
      have hl : raw19953step3Labels = raw19953step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19953step2 raw19953step2Labels permutation4 hz
    _ = mixedMoment B node4085 node4085Labels := by rfl

def raw19954 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19954step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19954step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19954step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19954step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, -3, 4]]
def raw19954step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19954step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19954step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19954step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19954step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19954 raw19954Labels = mixedMoment B node4274 node4274Labels := by
  calc
    mixedMoment B raw19954 raw19954Labels = mixedMoment B raw19954step0 raw19954step0Labels := by
      have hz : ∀ j, raw19954 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19954step0 = (fun i j => raw19954 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19954step0 raw19954; decide +kernel
      have hl : raw19954step0Labels = raw19954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19954 raw19954Labels permutation520 hz
    mixedMoment B raw19954step0 raw19954step0Labels = mixedMoment B raw19954step1 raw19954step1Labels := by
      have hz : ∀ j, raw19954step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19954step1 = (fun i j => raw19954step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19954step1 raw19954step0; decide +kernel
      have hl : raw19954step1Labels = raw19954step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19954step0 raw19954step0Labels permutation104 hz
    mixedMoment B raw19954step1 raw19954step1Labels = mixedMoment B raw19954step2 raw19954step2Labels := by
      have hz : ∀ j, raw19954step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19954step2 = (fun i j => raw19954step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19954step2 raw19954step1; decide +kernel
      have hl : raw19954step2Labels = raw19954step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19954step1 raw19954step1Labels permutation20 hz
    mixedMoment B raw19954step2 raw19954step2Labels = mixedMoment B raw19954step3 raw19954step3Labels := by
      have ha : raw19954step3 = (fun i j => raw19954step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19954step3 raw19954step2; decide +kernel
      have hl : raw19954step3Labels = raw19954step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19954step2 raw19954step2Labels permutation2 permutation6
    mixedMoment B raw19954step3 raw19954step3Labels = mixedMoment B raw19954step4 raw19954step4Labels := by
      have ha : raw19954step4 = raw19954step3 := by apply Matrix.ext; unfold raw19954step4 raw19954step3; decide +kernel
      have hl : raw19954step3Labels = labelEmbedding9 ∘ raw19954step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19954step3 raw19954step3Labels raw19954step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4274 node4274Labels := by rfl

def raw19955 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19955Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19955step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19955step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19955step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19955step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19955step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19955step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19955step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19955 raw19955Labels = mixedMoment B node4405 node4405Labels := by
  calc
    mixedMoment B raw19955 raw19955Labels = mixedMoment B raw19955step0 raw19955step0Labels := by
      have hz : ∀ j, raw19955 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19955step0 = (fun i j => raw19955 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19955step0 raw19955; decide +kernel
      have hl : raw19955step0Labels = raw19955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19955 raw19955Labels permutation520 hz
    mixedMoment B raw19955step0 raw19955step0Labels = mixedMoment B raw19955step1 raw19955step1Labels := by
      have hz : ∀ j, raw19955step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19955step1 = (fun i j => raw19955step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19955step1 raw19955step0; decide +kernel
      have hl : raw19955step1Labels = raw19955step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19955step0 raw19955step0Labels permutation104 hz
    mixedMoment B raw19955step1 raw19955step1Labels = mixedMoment B raw19955step2 raw19955step2Labels := by
      have ha : raw19955step2 = (fun i j => raw19955step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19955step2 raw19955step1; decide +kernel
      have hl : raw19955step2Labels = raw19955step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19955step1 raw19955step1Labels permutation10 permutation6
    mixedMoment B raw19955step2 raw19955step2Labels = mixedMoment B raw19955step3 raw19955step3Labels := by
      have ha : raw19955step3 = raw19955step2 := by apply Matrix.ext; unfold raw19955step3 raw19955step2; decide +kernel
      have hl : raw19955step2Labels = labelEmbedding9 ∘ raw19955step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19955step2 raw19955step2Labels raw19955step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4405 node4405Labels := by rfl

def raw19956 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19956step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19956step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19956step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19956step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19956step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19956step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19956step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19956 raw19956Labels = mixedMoment B node4405 node4405Labels := by
  calc
    mixedMoment B raw19956 raw19956Labels = mixedMoment B raw19956step0 raw19956step0Labels := by
      have hz : ∀ j, raw19956 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19956step0 = (fun i j => raw19956 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19956step0 raw19956; decide +kernel
      have hl : raw19956step0Labels = raw19956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19956 raw19956Labels permutation520 hz
    mixedMoment B raw19956step0 raw19956step0Labels = mixedMoment B raw19956step1 raw19956step1Labels := by
      have hz : ∀ j, raw19956step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19956step1 = (fun i j => raw19956step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19956step1 raw19956step0; decide +kernel
      have hl : raw19956step1Labels = raw19956step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19956step0 raw19956step0Labels permutation80 hz
    mixedMoment B raw19956step1 raw19956step1Labels = mixedMoment B raw19956step2 raw19956step2Labels := by
      have ha : raw19956step2 = (fun i j => raw19956step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19956step2 raw19956step1; decide +kernel
      have hl : raw19956step2Labels = raw19956step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19956step1 raw19956step1Labels permutation10 permutation6
    mixedMoment B raw19956step2 raw19956step2Labels = mixedMoment B raw19956step3 raw19956step3Labels := by
      have ha : raw19956step3 = raw19956step2 := by apply Matrix.ext; unfold raw19956step3 raw19956step2; decide +kernel
      have hl : raw19956step2Labels = labelEmbedding9 ∘ raw19956step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19956step2 raw19956step2Labels raw19956step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4405 node4405Labels := by rfl

def raw19957 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19957Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19957step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19957step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19957step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19957step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, -3, 4]]
def raw19957step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19957step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19957step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19957step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19957step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19957 raw19957Labels = mixedMoment B node4274 node4274Labels := by
  calc
    mixedMoment B raw19957 raw19957Labels = mixedMoment B raw19957step0 raw19957step0Labels := by
      have hz : ∀ j, raw19957 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19957step0 = (fun i j => raw19957 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19957step0 raw19957; decide +kernel
      have hl : raw19957step0Labels = raw19957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19957 raw19957Labels permutation520 hz
    mixedMoment B raw19957step0 raw19957step0Labels = mixedMoment B raw19957step1 raw19957step1Labels := by
      have hz : ∀ j, raw19957step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19957step1 = (fun i j => raw19957step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19957step1 raw19957step0; decide +kernel
      have hl : raw19957step1Labels = raw19957step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19957step0 raw19957step0Labels permutation104 hz
    mixedMoment B raw19957step1 raw19957step1Labels = mixedMoment B raw19957step2 raw19957step2Labels := by
      have hz : ∀ j, raw19957step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19957step2 = (fun i j => raw19957step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19957step2 raw19957step1; decide +kernel
      have hl : raw19957step2Labels = raw19957step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19957step1 raw19957step1Labels permutation14 hz
    mixedMoment B raw19957step2 raw19957step2Labels = mixedMoment B raw19957step3 raw19957step3Labels := by
      have ha : raw19957step3 = (fun i j => raw19957step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19957step3 raw19957step2; decide +kernel
      have hl : raw19957step3Labels = raw19957step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19957step2 raw19957step2Labels permutation2 permutation6
    mixedMoment B raw19957step3 raw19957step3Labels = mixedMoment B raw19957step4 raw19957step4Labels := by
      have ha : raw19957step4 = raw19957step3 := by apply Matrix.ext; unfold raw19957step4 raw19957step3; decide +kernel
      have hl : raw19957step3Labels = labelEmbedding9 ∘ raw19957step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19957step3 raw19957step3Labels raw19957step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4274 node4274Labels := by rfl

def raw19958 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19958Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19958step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19958step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19958step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19958step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19958step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19958step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19958step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19958 raw19958Labels = mixedMoment B node4405 node4405Labels := by
  calc
    mixedMoment B raw19958 raw19958Labels = mixedMoment B raw19958step0 raw19958step0Labels := by
      have hz : ∀ j, raw19958 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19958step0 = (fun i j => raw19958 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19958step0 raw19958; decide +kernel
      have hl : raw19958step0Labels = raw19958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19958 raw19958Labels permutation520 hz
    mixedMoment B raw19958step0 raw19958step0Labels = mixedMoment B raw19958step1 raw19958step1Labels := by
      have hz : ∀ j, raw19958step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19958step1 = (fun i j => raw19958step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19958step1 raw19958step0; decide +kernel
      have hl : raw19958step1Labels = raw19958step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19958step0 raw19958step0Labels permutation104 hz
    mixedMoment B raw19958step1 raw19958step1Labels = mixedMoment B raw19958step2 raw19958step2Labels := by
      have ha : raw19958step2 = (fun i j => raw19958step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19958step2 raw19958step1; decide +kernel
      have hl : raw19958step2Labels = raw19958step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19958step1 raw19958step1Labels permutation8 permutation6
    mixedMoment B raw19958step2 raw19958step2Labels = mixedMoment B raw19958step3 raw19958step3Labels := by
      have ha : raw19958step3 = raw19958step2 := by apply Matrix.ext; unfold raw19958step3 raw19958step2; decide +kernel
      have hl : raw19958step2Labels = labelEmbedding9 ∘ raw19958step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19958step2 raw19958step2Labels raw19958step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4405 node4405Labels := by rfl

def raw19959 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19959Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19959step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19959step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -3, 4]]
def raw19959step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19959step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19959step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19959step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19959step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19959 raw19959Labels = mixedMoment B node4405 node4405Labels := by
  calc
    mixedMoment B raw19959 raw19959Labels = mixedMoment B raw19959step0 raw19959step0Labels := by
      have hz : ∀ j, raw19959 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19959step0 = (fun i j => raw19959 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19959step0 raw19959; decide +kernel
      have hl : raw19959step0Labels = raw19959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19959 raw19959Labels permutation520 hz
    mixedMoment B raw19959step0 raw19959step0Labels = mixedMoment B raw19959step1 raw19959step1Labels := by
      have hz : ∀ j, raw19959step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19959step1 = (fun i j => raw19959step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19959step1 raw19959step0; decide +kernel
      have hl : raw19959step1Labels = raw19959step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19959step0 raw19959step0Labels permutation56 hz
    mixedMoment B raw19959step1 raw19959step1Labels = mixedMoment B raw19959step2 raw19959step2Labels := by
      have ha : raw19959step2 = (fun i j => raw19959step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19959step2 raw19959step1; decide +kernel
      have hl : raw19959step2Labels = raw19959step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19959step1 raw19959step1Labels permutation10 permutation6
    mixedMoment B raw19959step2 raw19959step2Labels = mixedMoment B raw19959step3 raw19959step3Labels := by
      have ha : raw19959step3 = raw19959step2 := by apply Matrix.ext; unfold raw19959step3 raw19959step2; decide +kernel
      have hl : raw19959step2Labels = labelEmbedding9 ∘ raw19959step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19959step2 raw19959step2Labels raw19959step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4405 node4405Labels := by rfl

def raw19960 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19960Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19960step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19960step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19960step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19960step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, -3, 4]]
def raw19960step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19960step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19960step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19960step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19960step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19960 raw19960Labels = mixedMoment B node4274 node4274Labels := by
  calc
    mixedMoment B raw19960 raw19960Labels = mixedMoment B raw19960step0 raw19960step0Labels := by
      have hz : ∀ j, raw19960 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19960step0 = (fun i j => raw19960 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19960step0 raw19960; decide +kernel
      have hl : raw19960step0Labels = raw19960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19960 raw19960Labels permutation520 hz
    mixedMoment B raw19960step0 raw19960step0Labels = mixedMoment B raw19960step1 raw19960step1Labels := by
      have hz : ∀ j, raw19960step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19960step1 = (fun i j => raw19960step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19960step1 raw19960step0; decide +kernel
      have hl : raw19960step1Labels = raw19960step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19960step0 raw19960step0Labels permutation80 hz
    mixedMoment B raw19960step1 raw19960step1Labels = mixedMoment B raw19960step2 raw19960step2Labels := by
      have hz : ∀ j, raw19960step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19960step2 = (fun i j => raw19960step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19960step2 raw19960step1; decide +kernel
      have hl : raw19960step2Labels = raw19960step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19960step1 raw19960step1Labels permutation14 hz
    mixedMoment B raw19960step2 raw19960step2Labels = mixedMoment B raw19960step3 raw19960step3Labels := by
      have ha : raw19960step3 = (fun i j => raw19960step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19960step3 raw19960step2; decide +kernel
      have hl : raw19960step3Labels = raw19960step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19960step2 raw19960step2Labels permutation2 permutation6
    mixedMoment B raw19960step3 raw19960step3Labels = mixedMoment B raw19960step4 raw19960step4Labels := by
      have ha : raw19960step4 = raw19960step3 := by apply Matrix.ext; unfold raw19960step4 raw19960step3; decide +kernel
      have hl : raw19960step3Labels = labelEmbedding9 ∘ raw19960step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19960step3 raw19960step3Labels raw19960step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4274 node4274Labels := by rfl

def raw19961 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19961Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19961step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19961step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19961step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19961step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19961step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19961step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19961 raw19961Labels = mixedMoment B node4405 node4405Labels := by
  calc
    mixedMoment B raw19961 raw19961Labels = mixedMoment B raw19961step0 raw19961step0Labels := by
      have hz : ∀ j, raw19961 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19961step0 = (fun i j => raw19961 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19961step0 raw19961; decide +kernel
      have hl : raw19961step0Labels = raw19961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19961 raw19961Labels permutation520 hz
    mixedMoment B raw19961step0 raw19961step0Labels = mixedMoment B raw19961step1 raw19961step1Labels := by
      have hz : ∀ j, raw19961step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19961step1 = (fun i j => raw19961step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19961step1 raw19961step0; decide +kernel
      have hl : raw19961step1Labels = raw19961step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19961step0 raw19961step0Labels permutation80 hz
    mixedMoment B raw19961step1 raw19961step1Labels = mixedMoment B raw19961step2 raw19961step2Labels := by
      have ha : raw19961step2 = (fun i j => raw19961step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19961step2 raw19961step1; decide +kernel
      have hl : raw19961step2Labels = raw19961step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19961step1 raw19961step1Labels permutation8 permutation6
    mixedMoment B raw19961step2 raw19961step2Labels = mixedMoment B raw19961step3 raw19961step3Labels := by
      have ha : raw19961step3 = raw19961step2 := by apply Matrix.ext; unfold raw19961step3 raw19961step2; decide +kernel
      have hl : raw19961step2Labels = labelEmbedding9 ∘ raw19961step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19961step2 raw19961step2Labels raw19961step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4405 node4405Labels := by rfl

def raw19962 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -3, 4]]
def raw19962Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19962step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19962step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19962step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19962step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19962step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19962step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19962 raw19962Labels = mixedMoment B node4405 node4405Labels := by
  calc
    mixedMoment B raw19962 raw19962Labels = mixedMoment B raw19962step0 raw19962step0Labels := by
      have hz : ∀ j, raw19962 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19962step0 = (fun i j => raw19962 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19962step0 raw19962; decide +kernel
      have hl : raw19962step0Labels = raw19962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19962 raw19962Labels permutation520 hz
    mixedMoment B raw19962step0 raw19962step0Labels = mixedMoment B raw19962step1 raw19962step1Labels := by
      have hz : ∀ j, raw19962step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19962step1 = (fun i j => raw19962step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19962step1 raw19962step0; decide +kernel
      have hl : raw19962step1Labels = raw19962step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19962step0 raw19962step0Labels permutation56 hz
    mixedMoment B raw19962step1 raw19962step1Labels = mixedMoment B raw19962step2 raw19962step2Labels := by
      have ha : raw19962step2 = (fun i j => raw19962step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19962step2 raw19962step1; decide +kernel
      have hl : raw19962step2Labels = raw19962step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19962step1 raw19962step1Labels permutation8 permutation6
    mixedMoment B raw19962step2 raw19962step2Labels = mixedMoment B raw19962step3 raw19962step3Labels := by
      have ha : raw19962step3 = raw19962step2 := by apply Matrix.ext; unfold raw19962step3 raw19962step2; decide +kernel
      have hl : raw19962step2Labels = labelEmbedding9 ∘ raw19962step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19962step2 raw19962step2Labels raw19962step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4405 node4405Labels := by rfl

def raw19963 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19963Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19963step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19963step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19963step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, -3, 4]]
def raw19963step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19963step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19963step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19963step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19963step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19963 raw19963Labels = mixedMoment B node4274 node4274Labels := by
  calc
    mixedMoment B raw19963 raw19963Labels = mixedMoment B raw19963step0 raw19963step0Labels := by
      have hz : ∀ j, raw19963 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19963step0 = (fun i j => raw19963 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19963step0 raw19963; decide +kernel
      have hl : raw19963step0Labels = raw19963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19963 raw19963Labels permutation434 hz
    mixedMoment B raw19963step0 raw19963step0Labels = mixedMoment B raw19963step1 raw19963step1Labels := by
      have hz : ∀ j, raw19963step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19963step1 = (fun i j => raw19963step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19963step1 raw19963step0; decide +kernel
      have hl : raw19963step1Labels = raw19963step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19963step0 raw19963step0Labels permutation80 hz
    mixedMoment B raw19963step1 raw19963step1Labels = mixedMoment B raw19963step2 raw19963step2Labels := by
      have hz : ∀ j, raw19963step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19963step2 = (fun i j => raw19963step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19963step2 raw19963step1; decide +kernel
      have hl : raw19963step2Labels = raw19963step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19963step1 raw19963step1Labels permutation14 hz
    mixedMoment B raw19963step2 raw19963step2Labels = mixedMoment B raw19963step3 raw19963step3Labels := by
      have ha : raw19963step3 = (fun i j => raw19963step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19963step3 raw19963step2; decide +kernel
      have hl : raw19963step3Labels = raw19963step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19963step2 raw19963step2Labels permutation2 permutation6
    mixedMoment B raw19963step3 raw19963step3Labels = mixedMoment B raw19963step4 raw19963step4Labels := by
      have ha : raw19963step4 = raw19963step3 := by apply Matrix.ext; unfold raw19963step4 raw19963step3; decide +kernel
      have hl : raw19963step3Labels = labelEmbedding9 ∘ raw19963step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19963step3 raw19963step3Labels raw19963step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4274 node4274Labels := by rfl

def raw19964 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19964Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19964step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19964step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19964step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19964step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19964step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19964step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19964step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19964 raw19964Labels = mixedMoment B node4405 node4405Labels := by
  calc
    mixedMoment B raw19964 raw19964Labels = mixedMoment B raw19964step0 raw19964step0Labels := by
      have hz : ∀ j, raw19964 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19964step0 = (fun i j => raw19964 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19964step0 raw19964; decide +kernel
      have hl : raw19964step0Labels = raw19964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19964 raw19964Labels permutation434 hz
    mixedMoment B raw19964step0 raw19964step0Labels = mixedMoment B raw19964step1 raw19964step1Labels := by
      have hz : ∀ j, raw19964step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19964step1 = (fun i j => raw19964step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19964step1 raw19964step0; decide +kernel
      have hl : raw19964step1Labels = raw19964step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19964step0 raw19964step0Labels permutation80 hz
    mixedMoment B raw19964step1 raw19964step1Labels = mixedMoment B raw19964step2 raw19964step2Labels := by
      have ha : raw19964step2 = (fun i j => raw19964step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19964step2 raw19964step1; decide +kernel
      have hl : raw19964step2Labels = raw19964step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19964step1 raw19964step1Labels permutation8 permutation6
    mixedMoment B raw19964step2 raw19964step2Labels = mixedMoment B raw19964step3 raw19964step3Labels := by
      have ha : raw19964step3 = raw19964step2 := by apply Matrix.ext; unfold raw19964step3 raw19964step2; decide +kernel
      have hl : raw19964step2Labels = labelEmbedding9 ∘ raw19964step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19964step2 raw19964step2Labels raw19964step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4405 node4405Labels := by rfl

def raw19965 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19965Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19965step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19965step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19965step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19965step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19965step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19965step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19965step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19965 raw19965Labels = mixedMoment B node4405 node4405Labels := by
  calc
    mixedMoment B raw19965 raw19965Labels = mixedMoment B raw19965step0 raw19965step0Labels := by
      have hz : ∀ j, raw19965 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19965step0 = (fun i j => raw19965 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19965step0 raw19965; decide +kernel
      have hl : raw19965step0Labels = raw19965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19965 raw19965Labels permutation434 hz
    mixedMoment B raw19965step0 raw19965step0Labels = mixedMoment B raw19965step1 raw19965step1Labels := by
      have hz : ∀ j, raw19965step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19965step1 = (fun i j => raw19965step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19965step1 raw19965step0; decide +kernel
      have hl : raw19965step1Labels = raw19965step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19965step0 raw19965step0Labels permutation56 hz
    mixedMoment B raw19965step1 raw19965step1Labels = mixedMoment B raw19965step2 raw19965step2Labels := by
      have ha : raw19965step2 = (fun i j => raw19965step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19965step2 raw19965step1; decide +kernel
      have hl : raw19965step2Labels = raw19965step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19965step1 raw19965step1Labels permutation8 permutation6
    mixedMoment B raw19965step2 raw19965step2Labels = mixedMoment B raw19965step3 raw19965step3Labels := by
      have ha : raw19965step3 = raw19965step2 := by apply Matrix.ext; unfold raw19965step3 raw19965step2; decide +kernel
      have hl : raw19965step2Labels = labelEmbedding9 ∘ raw19965step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19965step2 raw19965step2Labels raw19965step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4405 node4405Labels := by rfl

def raw19966 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19966Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19966step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, -3, 4]]
def raw19966step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19966step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19966step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19966step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw19966step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19966 raw19966Labels = mixedMoment B node4405 node4405Labels := by
  calc
    mixedMoment B raw19966 raw19966Labels = mixedMoment B raw19966step0 raw19966step0Labels := by
      have hz : ∀ j, raw19966 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19966step0 = (fun i j => raw19966 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19966step0 raw19966; decide +kernel
      have hl : raw19966step0Labels = raw19966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19966 raw19966Labels permutation346 hz
    mixedMoment B raw19966step0 raw19966step0Labels = mixedMoment B raw19966step1 raw19966step1Labels := by
      have hz : ∀ j, raw19966step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19966step1 = (fun i j => raw19966step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19966step1 raw19966step0; decide +kernel
      have hl : raw19966step1Labels = raw19966step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19966step0 raw19966step0Labels permutation56 hz
    mixedMoment B raw19966step1 raw19966step1Labels = mixedMoment B raw19966step2 raw19966step2Labels := by
      have ha : raw19966step2 = (fun i j => raw19966step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19966step2 raw19966step1; decide +kernel
      have hl : raw19966step2Labels = raw19966step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19966step1 raw19966step1Labels permutation8 permutation6
    mixedMoment B raw19966step2 raw19966step2Labels = mixedMoment B raw19966step3 raw19966step3Labels := by
      have ha : raw19966step3 = raw19966step2 := by apply Matrix.ext; unfold raw19966step3 raw19966step2; decide +kernel
      have hl : raw19966step2Labels = labelEmbedding9 ∘ raw19966step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19966step2 raw19966step2Labels raw19966step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4405 node4405Labels := by rfl

def raw19967 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -4, 4]]
def raw19967Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -4, 4]]
def raw19967step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19967step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, -4, 4]]
def raw19967step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19967step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, -4, 4]]
def raw19967step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19967step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, 4, -4], ![0, -4, 4]]
def raw19967step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19967step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![4, -4], ![-4, 4]]
def raw19967step4Labels : Fin 2 → Fin 3 := ![1, 2]

def raw19967step5 : Matrix (Fin 2) (Fin 2) ℤ := ![![-4, 4], ![4, -4]]
def raw19967step5Labels : Fin 2 → Fin 3 := ![1, 2]

def raw19967step6 : Matrix (Fin 2) (Fin 2) ℤ := ![![-4, 4], ![4, -4]]
def raw19967step6Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19967 raw19967Labels = mixedMoment B node4072 node4072Labels := by
  calc
    mixedMoment B raw19967 raw19967Labels = mixedMoment B raw19967step0 raw19967step0Labels := by
      have hz : ∀ j, raw19967 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19967step0 = (fun i j => raw19967 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19967step0 raw19967; decide +kernel
      have hl : raw19967step0Labels = raw19967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19967 raw19967Labels permutation520 hz
    mixedMoment B raw19967step0 raw19967step0Labels = mixedMoment B raw19967step1 raw19967step1Labels := by
      have hz : ∀ j, raw19967step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19967step1 = (fun i j => raw19967step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19967step1 raw19967step0; decide +kernel
      have hl : raw19967step1Labels = raw19967step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19967step0 raw19967step0Labels permutation104 hz
    mixedMoment B raw19967step1 raw19967step1Labels = mixedMoment B raw19967step2 raw19967step2Labels := by
      have hz : ∀ j, raw19967step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19967step2 = (fun i j => raw19967step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19967step2 raw19967step1; decide +kernel
      have hl : raw19967step2Labels = raw19967step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19967step1 raw19967step1Labels permutation20 hz
    mixedMoment B raw19967step2 raw19967step2Labels = mixedMoment B raw19967step3 raw19967step3Labels := by
      have hz : ∀ j, raw19967step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw19967step3 = (fun i j => raw19967step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw19967step3 raw19967step2; decide +kernel
      have hl : raw19967step3Labels = raw19967step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19967step2 raw19967step2Labels permutation4 hz
    mixedMoment B raw19967step3 raw19967step3Labels = mixedMoment B raw19967step4 raw19967step4Labels := by
      have hz : ∀ i, raw19967step3 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw19967step4 = (fun i j => raw19967step3 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw19967step4 raw19967step3; decide +kernel
      have hl : raw19967step4Labels = (fun j => raw19967step3Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19967step3 raw19967step3Labels permutation2 hz
    mixedMoment B raw19967step4 raw19967step4Labels = mixedMoment B raw19967step5 raw19967step5Labels := by
      have ha : raw19967step5 = (fun i j => raw19967step4 (permutation1 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19967step5 raw19967step4; decide +kernel
      have hl : raw19967step5Labels = raw19967step4Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19967step4 raw19967step4Labels permutation1 permutation0
    mixedMoment B raw19967step5 raw19967step5Labels = mixedMoment B raw19967step6 raw19967step6Labels := by
      have ha : raw19967step6 = raw19967step5 := by apply Matrix.ext; unfold raw19967step6 raw19967step5; decide +kernel
      have hl : raw19967step5Labels = labelEmbedding3 ∘ raw19967step6Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19967step5 raw19967step5Labels raw19967step6Labels labelEmbedding3 hl
    _ = mixedMoment B node4072 node4072Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
