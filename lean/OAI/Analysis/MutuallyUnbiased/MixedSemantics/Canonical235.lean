import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw30080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30080 raw30080Labels = mixedMoment B node4955 node4955Labels := by
  calc
    mixedMoment B raw30080 raw30080Labels = mixedMoment B raw30080step0 raw30080step0Labels := by
      have ha : raw30080step0 = (fun i j => raw30080 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30080step0 raw30080; decide +kernel
      have hl : raw30080step0Labels = raw30080Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30080 raw30080Labels permutation159 permutation2
    _ = mixedMoment B node4955 node4955Labels := by rfl

def raw30081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30081step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30081 raw30081Labels = mixedMoment B node5036 node5036Labels := by
  calc
    mixedMoment B raw30081 raw30081Labels = mixedMoment B raw30081step0 raw30081step0Labels := by
      have ha : raw30081step0 = (fun i j => raw30081 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30081step0 raw30081; decide +kernel
      have hl : raw30081step0Labels = raw30081Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30081 raw30081Labels permutation201 permutation2
    _ = mixedMoment B node5036 node5036Labels := by rfl

def raw30082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30082step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30082 raw30082Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw30082 raw30082Labels = mixedMoment B raw30082step0 raw30082step0Labels := by
      have ha : raw30082step0 = (fun i j => raw30082 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30082step0 raw30082; decide +kernel
      have hl : raw30082step0Labels = raw30082Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30082 raw30082Labels permutation159 permutation2
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw30083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30083step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30083step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30083 raw30083Labels = mixedMoment B node4966 node4966Labels := by
  calc
    mixedMoment B raw30083 raw30083Labels = mixedMoment B raw30083step0 raw30083step0Labels := by
      have hz : ∀ j, raw30083 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30083step0 = (fun i j => raw30083 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30083step0 raw30083; decide +kernel
      have hl : raw30083step0Labels = raw30083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30083 raw30083Labels permutation346 hz
    mixedMoment B raw30083step0 raw30083step0Labels = mixedMoment B raw30083step1 raw30083step1Labels := by
      have ha : raw30083step1 = (fun i j => raw30083step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30083step1 raw30083step0; decide +kernel
      have hl : raw30083step1Labels = raw30083step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30083step0 raw30083step0Labels permutation33 permutation2
    _ = mixedMoment B node4966 node4966Labels := by rfl

def raw30084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30084step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30084 raw30084Labels = mixedMoment B node5112 node5112Labels := by
  calc
    mixedMoment B raw30084 raw30084Labels = mixedMoment B raw30084step0 raw30084step0Labels := by
      have ha : raw30084step0 = (fun i j => raw30084 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30084step0 raw30084; decide +kernel
      have hl : raw30084step0Labels = raw30084Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30084 raw30084Labels permutation153 permutation2
    _ = mixedMoment B node5112 node5112Labels := by rfl

def raw30085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30085step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30085 raw30085Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw30085 raw30085Labels = mixedMoment B raw30085step0 raw30085step0Labels := by
      have hz : ∀ j, raw30085 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30085step0 = (fun i j => raw30085 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30085step0 raw30085; decide +kernel
      have hl : raw30085step0Labels = raw30085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30085 raw30085Labels permutation346 hz
    mixedMoment B raw30085step0 raw30085step0Labels = mixedMoment B raw30085step1 raw30085step1Labels := by
      have ha : raw30085step1 = (fun i j => raw30085step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30085step1 raw30085step0; decide +kernel
      have hl : raw30085step1Labels = raw30085step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30085step0 raw30085step0Labels permutation33 permutation2
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw30086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30086step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw30086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30086step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw30086step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30086 raw30086Labels = mixedMoment B node4934 node4934Labels := by
  calc
    mixedMoment B raw30086 raw30086Labels = mixedMoment B raw30086step0 raw30086step0Labels := by
      have hz : ∀ j, raw30086 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30086step0 = (fun i j => raw30086 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30086step0 raw30086; decide +kernel
      have hl : raw30086step0Labels = raw30086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30086 raw30086Labels permutation346 hz
    mixedMoment B raw30086step0 raw30086step0Labels = mixedMoment B raw30086step1 raw30086step1Labels := by
      have ha : raw30086step1 = (fun i j => raw30086step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30086step1 raw30086step0; decide +kernel
      have hl : raw30086step1Labels = raw30086step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30086step0 raw30086step0Labels permutation127 permutation2
    mixedMoment B raw30086step1 raw30086step1Labels = mixedMoment B raw30086step2 raw30086step2Labels := by
      have ha : raw30086step2 = -raw30086step1 := by apply Matrix.ext; change ∀ i j, raw30086step2 i j = -(raw30086step1 i j); unfold raw30086step2 raw30086step1; decide +kernel
      have hl : raw30086step2Labels = raw30086step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4934 node4934Labels := by rfl

def raw30087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw30087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw30087step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30087 raw30087Labels = mixedMoment B node4929 node4929Labels := by
  calc
    mixedMoment B raw30087 raw30087Labels = mixedMoment B raw30087step0 raw30087step0Labels := by
      have ha : raw30087step0 = (fun i j => raw30087 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30087step0 raw30087; decide +kernel
      have hl : raw30087step0Labels = raw30087Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30087 raw30087Labels permutation587 permutation2
    mixedMoment B raw30087step0 raw30087step0Labels = mixedMoment B raw30087step1 raw30087step1Labels := by
      have ha : raw30087step1 = -raw30087step0 := by apply Matrix.ext; change ∀ i j, raw30087step1 i j = -(raw30087step0 i j); unfold raw30087step1 raw30087step0; decide +kernel
      have hl : raw30087step1Labels = raw30087step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4929 node4929Labels := by rfl

def raw30088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30088step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30088step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30088 raw30088Labels = mixedMoment B node4943 node4943Labels := by
  calc
    mixedMoment B raw30088 raw30088Labels = mixedMoment B raw30088step0 raw30088step0Labels := by
      have hz : ∀ j, raw30088 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30088step0 = (fun i j => raw30088 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30088step0 raw30088; decide +kernel
      have hl : raw30088step0Labels = raw30088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30088 raw30088Labels permutation346 hz
    mixedMoment B raw30088step0 raw30088step0Labels = mixedMoment B raw30088step1 raw30088step1Labels := by
      have ha : raw30088step1 = (fun i j => raw30088step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30088step1 raw30088step0; decide +kernel
      have hl : raw30088step1Labels = raw30088step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30088step0 raw30088step0Labels permutation125 permutation2
    mixedMoment B raw30088step1 raw30088step1Labels = mixedMoment B raw30088step2 raw30088step2Labels := by
      have ha : raw30088step2 = -raw30088step1 := by apply Matrix.ext; change ∀ i j, raw30088step2 i j = -(raw30088step1 i j); unfold raw30088step2 raw30088step1; decide +kernel
      have hl : raw30088step2Labels = raw30088step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4943 node4943Labels := by rfl

def raw30089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw30089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw30089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw30089step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30089step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw30089step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30089 raw30089Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw30089 raw30089Labels = mixedMoment B raw30089step0 raw30089step0Labels := by
      have hz : ∀ j, raw30089 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30089step0 = (fun i j => raw30089 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30089step0 raw30089; decide +kernel
      have hl : raw30089step0Labels = raw30089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30089 raw30089Labels permutation346 hz
    mixedMoment B raw30089step0 raw30089step0Labels = mixedMoment B raw30089step1 raw30089step1Labels := by
      have ha : raw30089step1 = (fun i j => raw30089step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30089step1 raw30089step0; decide +kernel
      have hl : raw30089step1Labels = raw30089step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30089step0 raw30089step0Labels permutation127 permutation2
    mixedMoment B raw30089step1 raw30089step1Labels = mixedMoment B raw30089step2 raw30089step2Labels := by
      have ha : raw30089step2 = -raw30089step1 := by apply Matrix.ext; change ∀ i j, raw30089step2 i j = -(raw30089step1 i j); unfold raw30089step2 raw30089step1; decide +kernel
      have hl : raw30089step2Labels = raw30089step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw30090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30090 raw30090Labels = mixedMoment B node4959 node4959Labels := by
  calc
    mixedMoment B raw30090 raw30090Labels = mixedMoment B raw30090step0 raw30090step0Labels := by
      have hz : ∀ j, raw30090 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30090step0 = (fun i j => raw30090 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30090step0 raw30090; decide +kernel
      have hl : raw30090step0Labels = raw30090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30090 raw30090Labels permutation346 hz
    _ = mixedMoment B node4959 node4959Labels := by rfl

def raw30091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw30091step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30091step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw30091step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30091step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw30091step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30091 raw30091Labels = mixedMoment B node4956 node4956Labels := by
  calc
    mixedMoment B raw30091 raw30091Labels = mixedMoment B raw30091step0 raw30091step0Labels := by
      have ha : raw30091step0 = (fun i j => raw30091 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30091step0 raw30091; decide +kernel
      have hl : raw30091step0Labels = raw30091Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30091 raw30091Labels permutation686 permutation3
    mixedMoment B raw30091step0 raw30091step0Labels = mixedMoment B raw30091step1 raw30091step1Labels := by
      have ha : raw30091step1 = -raw30091step0 := by apply Matrix.ext; change ∀ i j, raw30091step1 i j = -(raw30091step0 i j); unfold raw30091step1 raw30091step0; decide +kernel
      have hl : raw30091step1Labels = raw30091step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30091step1 raw30091step1Labels = mixedMoment B raw30091step2 raw30091step2Labels := by
      have ha : raw30091step2 = raw30091step1 := by apply Matrix.ext; unfold raw30091step2 raw30091step1; decide +kernel
      have hl : raw30091step1Labels = labelEmbedding6 ∘ raw30091step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30091step1 raw30091step1Labels raw30091step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4956 node4956Labels := by rfl

def raw30092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw30092step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30092step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30092step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30092step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30092step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30092 raw30092Labels = mixedMoment B node4972 node4972Labels := by
  calc
    mixedMoment B raw30092 raw30092Labels = mixedMoment B raw30092step0 raw30092step0Labels := by
      have hz : ∀ j, raw30092 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30092step0 = (fun i j => raw30092 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30092step0 raw30092; decide +kernel
      have hl : raw30092step0Labels = raw30092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30092 raw30092Labels permutation346 hz
    mixedMoment B raw30092step0 raw30092step0Labels = mixedMoment B raw30092step1 raw30092step1Labels := by
      have ha : raw30092step1 = (fun i j => raw30092step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30092step1 raw30092step0; decide +kernel
      have hl : raw30092step1Labels = raw30092step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30092step0 raw30092step0Labels permutation151 permutation3
    mixedMoment B raw30092step1 raw30092step1Labels = mixedMoment B raw30092step2 raw30092step2Labels := by
      have ha : raw30092step2 = -raw30092step1 := by apply Matrix.ext; change ∀ i j, raw30092step2 i j = -(raw30092step1 i j); unfold raw30092step2 raw30092step1; decide +kernel
      have hl : raw30092step2Labels = raw30092step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30092step2 raw30092step2Labels = mixedMoment B raw30092step3 raw30092step3Labels := by
      have ha : raw30092step3 = raw30092step2 := by apply Matrix.ext; unfold raw30092step3 raw30092step2; decide +kernel
      have hl : raw30092step2Labels = labelEmbedding6 ∘ raw30092step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30092step2 raw30092step2Labels raw30092step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4972 node4972Labels := by rfl

def raw30093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30093Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30093step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30093step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30093 raw30093Labels = mixedMoment B node3728 node3728Labels := by
  calc
    mixedMoment B raw30093 raw30093Labels = mixedMoment B raw30093step0 raw30093step0Labels := by
      have hz : ∀ j, raw30093 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30093step0 = (fun i j => raw30093 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30093step0 raw30093; decide +kernel
      have hl : raw30093step0Labels = raw30093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30093 raw30093Labels permutation346 hz
    mixedMoment B raw30093step0 raw30093step0Labels = mixedMoment B raw30093step1 raw30093step1Labels := by
      have ha : raw30093step1 = (fun i j => raw30093step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30093step1 raw30093step0; decide +kernel
      have hl : raw30093step1Labels = raw30093step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30093step0 raw30093step0Labels permutation56 permutation3
    _ = mixedMoment B node3728 node3728Labels := by rfl

def raw30094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30094Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw30094step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30094step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw30094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30094 raw30094Labels = mixedMoment B node3937 node3937Labels := by
  calc
    mixedMoment B raw30094 raw30094Labels = mixedMoment B raw30094step0 raw30094step0Labels := by
      have ha : raw30094step0 = (fun i j => raw30094 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30094step0 raw30094; decide +kernel
      have hl : raw30094step0Labels = raw30094Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30094 raw30094Labels permutation686 permutation3
    mixedMoment B raw30094step0 raw30094step0Labels = mixedMoment B raw30094step1 raw30094step1Labels := by
      have ha : raw30094step1 = -raw30094step0 := by apply Matrix.ext; change ∀ i j, raw30094step1 i j = -(raw30094step0 i j); unfold raw30094step1 raw30094step0; decide +kernel
      have hl : raw30094step1Labels = raw30094step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3937 node3937Labels := by rfl

def raw30095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30095Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30095step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw30095step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30095step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw30095step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30095 raw30095Labels = mixedMoment B node3941 node3941Labels := by
  calc
    mixedMoment B raw30095 raw30095Labels = mixedMoment B raw30095step0 raw30095step0Labels := by
      have hz : ∀ j, raw30095 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30095step0 = (fun i j => raw30095 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30095step0 raw30095; decide +kernel
      have hl : raw30095step0Labels = raw30095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30095 raw30095Labels permutation346 hz
    mixedMoment B raw30095step0 raw30095step0Labels = mixedMoment B raw30095step1 raw30095step1Labels := by
      have ha : raw30095step1 = (fun i j => raw30095step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30095step1 raw30095step0; decide +kernel
      have hl : raw30095step1Labels = raw30095step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30095step0 raw30095step0Labels permutation151 permutation3
    mixedMoment B raw30095step1 raw30095step1Labels = mixedMoment B raw30095step2 raw30095step2Labels := by
      have ha : raw30095step2 = -raw30095step1 := by apply Matrix.ext; change ∀ i j, raw30095step2 i j = -(raw30095step1 i j); unfold raw30095step2 raw30095step1; decide +kernel
      have hl : raw30095step2Labels = raw30095step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3941 node3941Labels := by rfl

def raw30096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30096Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30096step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw30096step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30096 raw30096Labels = mixedMoment B node4035 node4035Labels := by
  calc
    mixedMoment B raw30096 raw30096Labels = mixedMoment B raw30096step0 raw30096step0Labels := by
      have hz : ∀ j, raw30096 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30096step0 = (fun i j => raw30096 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30096step0 raw30096; decide +kernel
      have hl : raw30096step0Labels = raw30096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30096 raw30096Labels permutation346 hz
    mixedMoment B raw30096step0 raw30096step0Labels = mixedMoment B raw30096step1 raw30096step1Labels := by
      have ha : raw30096step1 = (fun i j => raw30096step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30096step1 raw30096step0; decide +kernel
      have hl : raw30096step1Labels = raw30096step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30096step0 raw30096step0Labels permutation33 permutation3
    _ = mixedMoment B node4035 node4035Labels := by rfl

def raw30097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30097Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30097step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30097 raw30097Labels = mixedMoment B node2801 node2801Labels := by
  calc
    mixedMoment B raw30097 raw30097Labels = mixedMoment B raw30097step0 raw30097step0Labels := by
      have ha : raw30097step0 = (fun i j => raw30097 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30097step0 raw30097; decide +kernel
      have hl : raw30097step0Labels = raw30097Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30097 raw30097Labels permutation158 permutation3
    _ = mixedMoment B node2801 node2801Labels := by rfl

def raw30098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30098Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30098step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30098 raw30098Labels = mixedMoment B node2903 node2903Labels := by
  calc
    mixedMoment B raw30098 raw30098Labels = mixedMoment B raw30098step0 raw30098step0Labels := by
      have ha : raw30098step0 = (fun i j => raw30098 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30098step0 raw30098; decide +kernel
      have hl : raw30098step0Labels = raw30098Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30098 raw30098Labels permutation158 permutation3
    _ = mixedMoment B node2903 node2903Labels := by rfl

def raw30099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30099Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30099step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw30099step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30099 raw30099Labels = mixedMoment B node2937 node2937Labels := by
  calc
    mixedMoment B raw30099 raw30099Labels = mixedMoment B raw30099step0 raw30099step0Labels := by
      have ha : raw30099step0 = (fun i j => raw30099 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30099step0 raw30099; decide +kernel
      have hl : raw30099step0Labels = raw30099Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30099 raw30099Labels permutation162 permutation3
    _ = mixedMoment B node2937 node2937Labels := by rfl

def raw30100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30100Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30100step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw30100step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30100 raw30100Labels = mixedMoment B node2819 node2819Labels := by
  calc
    mixedMoment B raw30100 raw30100Labels = mixedMoment B raw30100step0 raw30100step0Labels := by
      have hz : ∀ j, raw30100 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30100step0 = (fun i j => raw30100 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30100step0 raw30100; decide +kernel
      have hl : raw30100step0Labels = raw30100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30100 raw30100Labels permutation346 hz
    mixedMoment B raw30100step0 raw30100step0Labels = mixedMoment B raw30100step1 raw30100step1Labels := by
      have ha : raw30100step1 = (fun i j => raw30100step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30100step1 raw30100step0; decide +kernel
      have hl : raw30100step1Labels = raw30100step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30100step0 raw30100step0Labels permutation32 permutation3
    _ = mixedMoment B node2819 node2819Labels := by rfl

def raw30101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30101Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw30101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30101 raw30101Labels = mixedMoment B node2898 node2898Labels := by
  calc
    mixedMoment B raw30101 raw30101Labels = mixedMoment B raw30101step0 raw30101step0Labels := by
      have ha : raw30101step0 = (fun i j => raw30101 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30101step0 raw30101; decide +kernel
      have hl : raw30101step0Labels = raw30101Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30101 raw30101Labels permutation152 permutation3
    _ = mixedMoment B node2898 node2898Labels := by rfl

def raw30102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30102Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30102step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30102step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30102 raw30102Labels = mixedMoment B node2961 node2961Labels := by
  calc
    mixedMoment B raw30102 raw30102Labels = mixedMoment B raw30102step0 raw30102step0Labels := by
      have hz : ∀ j, raw30102 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30102step0 = (fun i j => raw30102 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30102step0 raw30102; decide +kernel
      have hl : raw30102step0Labels = raw30102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30102 raw30102Labels permutation346 hz
    mixedMoment B raw30102step0 raw30102step0Labels = mixedMoment B raw30102step1 raw30102step1Labels := by
      have ha : raw30102step1 = (fun i j => raw30102step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30102step1 raw30102step0; decide +kernel
      have hl : raw30102step1Labels = raw30102step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30102step0 raw30102step0Labels permutation36 permutation3
    _ = mixedMoment B node2961 node2961Labels := by rfl

def raw30103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30103Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30103step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30103step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30103 raw30103Labels = mixedMoment B node2802 node2802Labels := by
  calc
    mixedMoment B raw30103 raw30103Labels = mixedMoment B raw30103step0 raw30103step0Labels := by
      have hz : ∀ j, raw30103 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30103step0 = (fun i j => raw30103 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30103step0 raw30103; decide +kernel
      have hl : raw30103step0Labels = raw30103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30103 raw30103Labels permutation346 hz
    mixedMoment B raw30103step0 raw30103step0Labels = mixedMoment B raw30103step1 raw30103step1Labels := by
      have ha : raw30103step1 = (fun i j => raw30103step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30103step1 raw30103step0; decide +kernel
      have hl : raw30103step1Labels = raw30103step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30103step0 raw30103step0Labels permutation33 permutation3
    _ = mixedMoment B node2802 node2802Labels := by rfl

def raw30104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30104Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw30104step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw30104step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30104 raw30104Labels = mixedMoment B node2823 node2823Labels := by
  calc
    mixedMoment B raw30104 raw30104Labels = mixedMoment B raw30104step0 raw30104step0Labels := by
      have ha : raw30104step0 = (fun i j => raw30104 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30104step0 raw30104; decide +kernel
      have hl : raw30104step0Labels = raw30104Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30104 raw30104Labels permutation587 permutation3
    mixedMoment B raw30104step0 raw30104step0Labels = mixedMoment B raw30104step1 raw30104step1Labels := by
      have ha : raw30104step1 = -raw30104step0 := by apply Matrix.ext; change ∀ i j, raw30104step1 i j = -(raw30104step0 i j); unfold raw30104step1 raw30104step0; decide +kernel
      have hl : raw30104step1Labels = raw30104step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2823 node2823Labels := by rfl

def raw30105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30105Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30105step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw30105step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30105step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30105step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30105 raw30105Labels = mixedMoment B node2828 node2828Labels := by
  calc
    mixedMoment B raw30105 raw30105Labels = mixedMoment B raw30105step0 raw30105step0Labels := by
      have hz : ∀ j, raw30105 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30105step0 = (fun i j => raw30105 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30105step0 raw30105; decide +kernel
      have hl : raw30105step0Labels = raw30105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30105 raw30105Labels permutation346 hz
    mixedMoment B raw30105step0 raw30105step0Labels = mixedMoment B raw30105step1 raw30105step1Labels := by
      have ha : raw30105step1 = (fun i j => raw30105step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30105step1 raw30105step0; decide +kernel
      have hl : raw30105step1Labels = raw30105step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30105step0 raw30105step0Labels permutation127 permutation3
    mixedMoment B raw30105step1 raw30105step1Labels = mixedMoment B raw30105step2 raw30105step2Labels := by
      have ha : raw30105step2 = -raw30105step1 := by apply Matrix.ext; change ∀ i j, raw30105step2 i j = -(raw30105step1 i j); unfold raw30105step2 raw30105step1; decide +kernel
      have hl : raw30105step2Labels = raw30105step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2828 node2828Labels := by rfl

def raw30106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw30106Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw30106step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw30106step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30106 raw30106Labels = mixedMoment B node2939 node2939Labels := by
  calc
    mixedMoment B raw30106 raw30106Labels = mixedMoment B raw30106step0 raw30106step0Labels := by
      have hz : ∀ j, raw30106 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30106step0 = (fun i j => raw30106 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30106step0 raw30106; decide +kernel
      have hl : raw30106step0Labels = raw30106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30106 raw30106Labels permutation346 hz
    mixedMoment B raw30106step0 raw30106step0Labels = mixedMoment B raw30106step1 raw30106step1Labels := by
      have ha : raw30106step1 = (fun i j => raw30106step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30106step1 raw30106step0; decide +kernel
      have hl : raw30106step1Labels = raw30106step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30106step0 raw30106step0Labels permutation33 permutation3
    _ = mixedMoment B node2939 node2939Labels := by rfl

def raw30107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30107Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30107step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw30107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30107step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30107step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30107 raw30107Labels = mixedMoment B node2352 node2352Labels := by
  calc
    mixedMoment B raw30107 raw30107Labels = mixedMoment B raw30107step0 raw30107step0Labels := by
      have hz : ∀ j, raw30107 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30107step0 = (fun i j => raw30107 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30107step0 raw30107; decide +kernel
      have hl : raw30107step0Labels = raw30107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30107 raw30107Labels permutation346 hz
    mixedMoment B raw30107step0 raw30107step0Labels = mixedMoment B raw30107step1 raw30107step1Labels := by
      have ha : raw30107step1 = (fun i j => raw30107step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30107step1 raw30107step0; decide +kernel
      have hl : raw30107step1Labels = raw30107step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30107step0 raw30107step0Labels permutation151 permutation3
    mixedMoment B raw30107step1 raw30107step1Labels = mixedMoment B raw30107step2 raw30107step2Labels := by
      have ha : raw30107step2 = -raw30107step1 := by apply Matrix.ext; change ∀ i j, raw30107step2 i j = -(raw30107step1 i j); unfold raw30107step2 raw30107step1; decide +kernel
      have hl : raw30107step2Labels = raw30107step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2352 node2352Labels := by rfl

def raw30108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30108Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw30108step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30108step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw30108step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30108 raw30108Labels = mixedMoment B node2349 node2349Labels := by
  calc
    mixedMoment B raw30108 raw30108Labels = mixedMoment B raw30108step0 raw30108step0Labels := by
      have ha : raw30108step0 = (fun i j => raw30108 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30108step0 raw30108; decide +kernel
      have hl : raw30108step0Labels = raw30108Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30108 raw30108Labels permutation686 permutation3
    mixedMoment B raw30108step0 raw30108step0Labels = mixedMoment B raw30108step1 raw30108step1Labels := by
      have ha : raw30108step1 = -raw30108step0 := by apply Matrix.ext; change ∀ i j, raw30108step1 i j = -(raw30108step0 i j); unfold raw30108step1 raw30108step0; decide +kernel
      have hl : raw30108step1Labels = raw30108step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2349 node2349Labels := by rfl

def raw30109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30109Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30109step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw30109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30109step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30109step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30109 raw30109Labels = mixedMoment B node2358 node2358Labels := by
  calc
    mixedMoment B raw30109 raw30109Labels = mixedMoment B raw30109step0 raw30109step0Labels := by
      have hz : ∀ j, raw30109 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30109step0 = (fun i j => raw30109 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30109step0 raw30109; decide +kernel
      have hl : raw30109step0Labels = raw30109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30109 raw30109Labels permutation346 hz
    mixedMoment B raw30109step0 raw30109step0Labels = mixedMoment B raw30109step1 raw30109step1Labels := by
      have ha : raw30109step1 = (fun i j => raw30109step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30109step1 raw30109step0; decide +kernel
      have hl : raw30109step1Labels = raw30109step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30109step0 raw30109step0Labels permutation151 permutation3
    mixedMoment B raw30109step1 raw30109step1Labels = mixedMoment B raw30109step2 raw30109step2Labels := by
      have ha : raw30109step2 = -raw30109step1 := by apply Matrix.ext; change ∀ i j, raw30109step2 i j = -(raw30109step1 i j); unfold raw30109step2 raw30109step1; decide +kernel
      have hl : raw30109step2Labels = raw30109step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2358 node2358Labels := by rfl

def raw30110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30110Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30110step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30110step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30110step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30110step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30110 raw30110Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw30110 raw30110Labels = mixedMoment B raw30110step0 raw30110step0Labels := by
      have hz : ∀ j, raw30110 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30110step0 = (fun i j => raw30110 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30110step0 raw30110; decide +kernel
      have hl : raw30110step0Labels = raw30110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30110 raw30110Labels permutation346 hz
    mixedMoment B raw30110step0 raw30110step0Labels = mixedMoment B raw30110step1 raw30110step1Labels := by
      have ha : raw30110step1 = (fun i j => raw30110step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30110step1 raw30110step0; decide +kernel
      have hl : raw30110step1Labels = raw30110step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30110step0 raw30110step0Labels permutation125 permutation7
    mixedMoment B raw30110step1 raw30110step1Labels = mixedMoment B raw30110step2 raw30110step2Labels := by
      have ha : raw30110step2 = raw30110step1 := by apply Matrix.ext; unfold raw30110step2 raw30110step1; decide +kernel
      have hl : raw30110step1Labels = labelEmbedding1 ∘ raw30110step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30110step1 raw30110step1Labels raw30110step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3770 node3770Labels := by rfl

def raw30111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30111Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30111step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30111step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30111step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30111step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30111 raw30111Labels = mixedMoment B node3757 node3757Labels := by
  calc
    mixedMoment B raw30111 raw30111Labels = mixedMoment B raw30111step0 raw30111step0Labels := by
      have ha : raw30111step0 = (fun i j => raw30111 (permutation577 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30111step0 raw30111; decide +kernel
      have hl : raw30111step0Labels = raw30111Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30111 raw30111Labels permutation577 permutation7
    mixedMoment B raw30111step0 raw30111step0Labels = mixedMoment B raw30111step1 raw30111step1Labels := by
      have ha : raw30111step1 = raw30111step0 := by apply Matrix.ext; unfold raw30111step1 raw30111step0; decide +kernel
      have hl : raw30111step0Labels = labelEmbedding1 ∘ raw30111step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30111step0 raw30111step0Labels raw30111step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3757 node3757Labels := by rfl

def raw30112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30112Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30112step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30112step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30112 raw30112Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw30112 raw30112Labels = mixedMoment B raw30112step0 raw30112step0Labels := by
      have hz : ∀ j, raw30112 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30112step0 = (fun i j => raw30112 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30112step0 raw30112; decide +kernel
      have hl : raw30112step0Labels = raw30112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30112 raw30112Labels permutation346 hz
    mixedMoment B raw30112step0 raw30112step0Labels = mixedMoment B raw30112step1 raw30112step1Labels := by
      have ha : raw30112step1 = (fun i j => raw30112step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30112step1 raw30112step0; decide +kernel
      have hl : raw30112step1Labels = raw30112step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30112step0 raw30112step0Labels permutation125 permutation7
    mixedMoment B raw30112step1 raw30112step1Labels = mixedMoment B raw30112step2 raw30112step2Labels := by
      have ha : raw30112step2 = raw30112step1 := by apply Matrix.ext; unfold raw30112step2 raw30112step1; decide +kernel
      have hl : raw30112step1Labels = labelEmbedding1 ∘ raw30112step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30112step1 raw30112step1Labels raw30112step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

def raw30113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30113Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30113step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30113step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30113step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30113 raw30113Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw30113 raw30113Labels = mixedMoment B raw30113step0 raw30113step0Labels := by
      have hz : ∀ j, raw30113 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30113step0 = (fun i j => raw30113 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30113step0 raw30113; decide +kernel
      have hl : raw30113step0Labels = raw30113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30113 raw30113Labels permutation346 hz
    mixedMoment B raw30113step0 raw30113step0Labels = mixedMoment B raw30113step1 raw30113step1Labels := by
      have ha : raw30113step1 = (fun i j => raw30113step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30113step1 raw30113step0; decide +kernel
      have hl : raw30113step1Labels = raw30113step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30113step0 raw30113step0Labels permutation125 permutation7
    mixedMoment B raw30113step1 raw30113step1Labels = mixedMoment B raw30113step2 raw30113step2Labels := by
      have ha : raw30113step2 = raw30113step1 := by apply Matrix.ext; unfold raw30113step2 raw30113step1; decide +kernel
      have hl : raw30113step1Labels = labelEmbedding1 ∘ raw30113step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30113step1 raw30113step1Labels raw30113step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

def raw30114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30114Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30114step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30114step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30114step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30114step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30114step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30114 raw30114Labels = mixedMoment B node3508 node3508Labels := by
  calc
    mixedMoment B raw30114 raw30114Labels = mixedMoment B raw30114step0 raw30114step0Labels := by
      have ha : raw30114step0 = (fun i j => raw30114 (permutation201 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30114step0 raw30114; decide +kernel
      have hl : raw30114step0Labels = raw30114Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30114 raw30114Labels permutation201 permutation7
    mixedMoment B raw30114step0 raw30114step0Labels = mixedMoment B raw30114step1 raw30114step1Labels := by
      have ha : raw30114step1 = -raw30114step0 := by apply Matrix.ext; change ∀ i j, raw30114step1 i j = -(raw30114step0 i j); unfold raw30114step1 raw30114step0; decide +kernel
      have hl : raw30114step1Labels = raw30114step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30114step1 raw30114step1Labels = mixedMoment B raw30114step2 raw30114step2Labels := by
      have ha : raw30114step2 = raw30114step1 := by apply Matrix.ext; unfold raw30114step2 raw30114step1; decide +kernel
      have hl : raw30114step1Labels = labelEmbedding1 ∘ raw30114step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30114step1 raw30114step1Labels raw30114step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3508 node3508Labels := by rfl

def raw30115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30115Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30115step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30115step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30115step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30115step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30115step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30115 raw30115Labels = mixedMoment B node3450 node3450Labels := by
  calc
    mixedMoment B raw30115 raw30115Labels = mixedMoment B raw30115step0 raw30115step0Labels := by
      have ha : raw30115step0 = (fun i j => raw30115 (permutation201 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30115step0 raw30115; decide +kernel
      have hl : raw30115step0Labels = raw30115Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30115 raw30115Labels permutation201 permutation7
    mixedMoment B raw30115step0 raw30115step0Labels = mixedMoment B raw30115step1 raw30115step1Labels := by
      have ha : raw30115step1 = -raw30115step0 := by apply Matrix.ext; change ∀ i j, raw30115step1 i j = -(raw30115step0 i j); unfold raw30115step1 raw30115step0; decide +kernel
      have hl : raw30115step1Labels = raw30115step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30115step1 raw30115step1Labels = mixedMoment B raw30115step2 raw30115step2Labels := by
      have ha : raw30115step2 = raw30115step1 := by apply Matrix.ext; unfold raw30115step2 raw30115step1; decide +kernel
      have hl : raw30115step1Labels = labelEmbedding1 ∘ raw30115step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30115step1 raw30115step1Labels raw30115step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3450 node3450Labels := by rfl

def raw30116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30116Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30116step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw30116step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30116step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30116step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30116step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30116step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30116 raw30116Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw30116 raw30116Labels = mixedMoment B raw30116step0 raw30116step0Labels := by
      have ha : raw30116step0 = (fun i j => raw30116 (permutation201 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30116step0 raw30116; decide +kernel
      have hl : raw30116step0Labels = raw30116Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30116 raw30116Labels permutation201 permutation7
    mixedMoment B raw30116step0 raw30116step0Labels = mixedMoment B raw30116step1 raw30116step1Labels := by
      have ha : raw30116step1 = -raw30116step0 := by apply Matrix.ext; change ∀ i j, raw30116step1 i j = -(raw30116step0 i j); unfold raw30116step1 raw30116step0; decide +kernel
      have hl : raw30116step1Labels = raw30116step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30116step1 raw30116step1Labels = mixedMoment B raw30116step2 raw30116step2Labels := by
      have ha : raw30116step2 = raw30116step1 := by apply Matrix.ext; unfold raw30116step2 raw30116step1; decide +kernel
      have hl : raw30116step1Labels = labelEmbedding1 ∘ raw30116step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30116step1 raw30116step1Labels raw30116step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

def raw30117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30117Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30117step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw30117step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30117step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30117step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30117step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30117step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30117 raw30117Labels = mixedMoment B node3555 node3555Labels := by
  calc
    mixedMoment B raw30117 raw30117Labels = mixedMoment B raw30117step0 raw30117step0Labels := by
      have hz : ∀ j, raw30117 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30117step0 = (fun i j => raw30117 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30117step0 raw30117; decide +kernel
      have hl : raw30117step0Labels = raw30117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30117 raw30117Labels permutation346 hz
    mixedMoment B raw30117step0 raw30117step0Labels = mixedMoment B raw30117step1 raw30117step1Labels := by
      have ha : raw30117step1 = (fun i j => raw30117step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30117step1 raw30117step0; decide +kernel
      have hl : raw30117step1Labels = raw30117step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30117step0 raw30117step0Labels permutation39 permutation7
    mixedMoment B raw30117step1 raw30117step1Labels = mixedMoment B raw30117step2 raw30117step2Labels := by
      have ha : raw30117step2 = -raw30117step1 := by apply Matrix.ext; change ∀ i j, raw30117step2 i j = -(raw30117step1 i j); unfold raw30117step2 raw30117step1; decide +kernel
      have hl : raw30117step2Labels = raw30117step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30117step2 raw30117step2Labels = mixedMoment B raw30117step3 raw30117step3Labels := by
      have ha : raw30117step3 = raw30117step2 := by apply Matrix.ext; unfold raw30117step3 raw30117step2; decide +kernel
      have hl : raw30117step2Labels = labelEmbedding1 ∘ raw30117step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30117step2 raw30117step2Labels raw30117step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3555 node3555Labels := by rfl

def raw30118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30118Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30118step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30118step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30118step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30118step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30118step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30118step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30118 raw30118Labels = mixedMoment B node3556 node3556Labels := by
  calc
    mixedMoment B raw30118 raw30118Labels = mixedMoment B raw30118step0 raw30118step0Labels := by
      have ha : raw30118step0 = (fun i j => raw30118 (permutation201 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30118step0 raw30118; decide +kernel
      have hl : raw30118step0Labels = raw30118Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30118 raw30118Labels permutation201 permutation7
    mixedMoment B raw30118step0 raw30118step0Labels = mixedMoment B raw30118step1 raw30118step1Labels := by
      have ha : raw30118step1 = -raw30118step0 := by apply Matrix.ext; change ∀ i j, raw30118step1 i j = -(raw30118step0 i j); unfold raw30118step1 raw30118step0; decide +kernel
      have hl : raw30118step1Labels = raw30118step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30118step1 raw30118step1Labels = mixedMoment B raw30118step2 raw30118step2Labels := by
      have ha : raw30118step2 = raw30118step1 := by apply Matrix.ext; unfold raw30118step2 raw30118step1; decide +kernel
      have hl : raw30118step1Labels = labelEmbedding1 ∘ raw30118step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30118step1 raw30118step1Labels raw30118step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3556 node3556Labels := by rfl

def raw30119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30119Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30119step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw30119step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30119step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30119step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30119step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30119step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30119 raw30119Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw30119 raw30119Labels = mixedMoment B raw30119step0 raw30119step0Labels := by
      have hz : ∀ j, raw30119 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30119step0 = (fun i j => raw30119 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30119step0 raw30119; decide +kernel
      have hl : raw30119step0Labels = raw30119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30119 raw30119Labels permutation346 hz
    mixedMoment B raw30119step0 raw30119step0Labels = mixedMoment B raw30119step1 raw30119step1Labels := by
      have ha : raw30119step1 = (fun i j => raw30119step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30119step1 raw30119step0; decide +kernel
      have hl : raw30119step1Labels = raw30119step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30119step0 raw30119step0Labels permutation39 permutation7
    mixedMoment B raw30119step1 raw30119step1Labels = mixedMoment B raw30119step2 raw30119step2Labels := by
      have ha : raw30119step2 = -raw30119step1 := by apply Matrix.ext; change ∀ i j, raw30119step2 i j = -(raw30119step1 i j); unfold raw30119step2 raw30119step1; decide +kernel
      have hl : raw30119step2Labels = raw30119step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30119step2 raw30119step2Labels = mixedMoment B raw30119step3 raw30119step3Labels := by
      have ha : raw30119step3 = raw30119step2 := by apply Matrix.ext; unfold raw30119step3 raw30119step2; decide +kernel
      have hl : raw30119step2Labels = labelEmbedding1 ∘ raw30119step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30119step2 raw30119step2Labels raw30119step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3564 node3564Labels := by rfl

def raw30120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30120Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30120step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw30120step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30120step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw30120step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30120 raw30120Labels = mixedMoment B node3415 node3415Labels := by
  calc
    mixedMoment B raw30120 raw30120Labels = mixedMoment B raw30120step0 raw30120step0Labels := by
      have hz : ∀ j, raw30120 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30120step0 = (fun i j => raw30120 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30120step0 raw30120; decide +kernel
      have hl : raw30120step0Labels = raw30120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30120 raw30120Labels permutation346 hz
    mixedMoment B raw30120step0 raw30120step0Labels = mixedMoment B raw30120step1 raw30120step1Labels := by
      have ha : raw30120step1 = (fun i j => raw30120step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30120step1 raw30120step0; decide +kernel
      have hl : raw30120step1Labels = raw30120step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30120step0 raw30120step0Labels permutation125 permutation7
    mixedMoment B raw30120step1 raw30120step1Labels = mixedMoment B raw30120step2 raw30120step2Labels := by
      have ha : raw30120step2 = raw30120step1 := by apply Matrix.ext; unfold raw30120step2 raw30120step1; decide +kernel
      have hl : raw30120step1Labels = labelEmbedding1 ∘ raw30120step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30120step1 raw30120step1Labels raw30120step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3415 node3415Labels := by rfl

def raw30121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30121Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30121step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw30121step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30121step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw30121step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30121 raw30121Labels = mixedMoment B node3403 node3403Labels := by
  calc
    mixedMoment B raw30121 raw30121Labels = mixedMoment B raw30121step0 raw30121step0Labels := by
      have ha : raw30121step0 = (fun i j => raw30121 (permutation577 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30121step0 raw30121; decide +kernel
      have hl : raw30121step0Labels = raw30121Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30121 raw30121Labels permutation577 permutation7
    mixedMoment B raw30121step0 raw30121step0Labels = mixedMoment B raw30121step1 raw30121step1Labels := by
      have ha : raw30121step1 = raw30121step0 := by apply Matrix.ext; unfold raw30121step1 raw30121step0; decide +kernel
      have hl : raw30121step0Labels = labelEmbedding1 ∘ raw30121step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30121step0 raw30121step0Labels raw30121step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3403 node3403Labels := by rfl

def raw30122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30122Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30122step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30122step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30122step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30122step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30122 raw30122Labels = mixedMoment B node3411 node3411Labels := by
  calc
    mixedMoment B raw30122 raw30122Labels = mixedMoment B raw30122step0 raw30122step0Labels := by
      have hz : ∀ j, raw30122 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30122step0 = (fun i j => raw30122 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30122step0 raw30122; decide +kernel
      have hl : raw30122step0Labels = raw30122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30122 raw30122Labels permutation346 hz
    mixedMoment B raw30122step0 raw30122step0Labels = mixedMoment B raw30122step1 raw30122step1Labels := by
      have ha : raw30122step1 = (fun i j => raw30122step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30122step1 raw30122step0; decide +kernel
      have hl : raw30122step1Labels = raw30122step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30122step0 raw30122step0Labels permutation125 permutation7
    mixedMoment B raw30122step1 raw30122step1Labels = mixedMoment B raw30122step2 raw30122step2Labels := by
      have ha : raw30122step2 = raw30122step1 := by apply Matrix.ext; unfold raw30122step2 raw30122step1; decide +kernel
      have hl : raw30122step1Labels = labelEmbedding1 ∘ raw30122step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30122step1 raw30122step1Labels raw30122step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3411 node3411Labels := by rfl

def raw30123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw30123Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw30123step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw30123step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw30123step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30123 raw30123Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw30123 raw30123Labels = mixedMoment B raw30123step0 raw30123step0Labels := by
      have hz : ∀ j, raw30123 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30123step0 = (fun i j => raw30123 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30123step0 raw30123; decide +kernel
      have hl : raw30123step0Labels = raw30123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30123 raw30123Labels permutation346 hz
    mixedMoment B raw30123step0 raw30123step0Labels = mixedMoment B raw30123step1 raw30123step1Labels := by
      have ha : raw30123step1 = (fun i j => raw30123step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30123step1 raw30123step0; decide +kernel
      have hl : raw30123step1Labels = raw30123step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30123step0 raw30123step0Labels permutation125 permutation7
    mixedMoment B raw30123step1 raw30123step1Labels = mixedMoment B raw30123step2 raw30123step2Labels := by
      have ha : raw30123step2 = raw30123step1 := by apply Matrix.ext; unfold raw30123step2 raw30123step1; decide +kernel
      have hl : raw30123step1Labels = labelEmbedding1 ∘ raw30123step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30123step1 raw30123step1Labels raw30123step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

def raw30124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30124Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30124step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw30124step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw30124step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30124 raw30124Labels = mixedMoment B node3512 node3512Labels := by
  calc
    mixedMoment B raw30124 raw30124Labels = mixedMoment B raw30124step0 raw30124step0Labels := by
      have hz : ∀ j, raw30124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30124step0 = (fun i j => raw30124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30124step0 raw30124; decide +kernel
      have hl : raw30124step0Labels = raw30124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30124 raw30124Labels permutation346 hz
    mixedMoment B raw30124step0 raw30124step0Labels = mixedMoment B raw30124step1 raw30124step1Labels := by
      have ha : raw30124step1 = (fun i j => raw30124step0 (permutation144 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30124step1 raw30124step0; decide +kernel
      have hl : raw30124step1Labels = raw30124step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30124step0 raw30124step0Labels permutation144 permutation5
    mixedMoment B raw30124step1 raw30124step1Labels = mixedMoment B raw30124step2 raw30124step2Labels := by
      have ha : raw30124step2 = raw30124step1 := by apply Matrix.ext; unfold raw30124step2 raw30124step1; decide +kernel
      have hl : raw30124step1Labels = labelEmbedding1 ∘ raw30124step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30124step1 raw30124step1Labels raw30124step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3512 node3512Labels := by rfl

def raw30125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30125Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw30125step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30125step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw30125step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30125 raw30125Labels = mixedMoment B node3510 node3510Labels := by
  calc
    mixedMoment B raw30125 raw30125Labels = mixedMoment B raw30125step0 raw30125step0Labels := by
      have ha : raw30125step0 = (fun i j => raw30125 (permutation662 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30125step0 raw30125; decide +kernel
      have hl : raw30125step0Labels = raw30125Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30125 raw30125Labels permutation662 permutation5
    mixedMoment B raw30125step0 raw30125step0Labels = mixedMoment B raw30125step1 raw30125step1Labels := by
      have ha : raw30125step1 = raw30125step0 := by apply Matrix.ext; unfold raw30125step1 raw30125step0; decide +kernel
      have hl : raw30125step0Labels = labelEmbedding1 ∘ raw30125step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30125step0 raw30125step0Labels raw30125step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3510 node3510Labels := by rfl

def raw30126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30126Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30126step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw30126step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw30126step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30126step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw30126step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30126 raw30126Labels = mixedMoment B node3457 node3457Labels := by
  calc
    mixedMoment B raw30126 raw30126Labels = mixedMoment B raw30126step0 raw30126step0Labels := by
      have hz : ∀ j, raw30126 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30126step0 = (fun i j => raw30126 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30126step0 raw30126; decide +kernel
      have hl : raw30126step0Labels = raw30126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30126 raw30126Labels permutation346 hz
    mixedMoment B raw30126step0 raw30126step0Labels = mixedMoment B raw30126step1 raw30126step1Labels := by
      have ha : raw30126step1 = (fun i j => raw30126step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30126step1 raw30126step0; decide +kernel
      have hl : raw30126step1Labels = raw30126step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30126step0 raw30126step0Labels permutation39 permutation7
    mixedMoment B raw30126step1 raw30126step1Labels = mixedMoment B raw30126step2 raw30126step2Labels := by
      have ha : raw30126step2 = -raw30126step1 := by apply Matrix.ext; change ∀ i j, raw30126step2 i j = -(raw30126step1 i j); unfold raw30126step2 raw30126step1; decide +kernel
      have hl : raw30126step2Labels = raw30126step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30126step2 raw30126step2Labels = mixedMoment B raw30126step3 raw30126step3Labels := by
      have ha : raw30126step3 = raw30126step2 := by apply Matrix.ext; unfold raw30126step3 raw30126step2; decide +kernel
      have hl : raw30126step2Labels = labelEmbedding1 ∘ raw30126step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30126step2 raw30126step2Labels raw30126step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3457 node3457Labels := by rfl

def raw30127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30127Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30127step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw30127step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30127step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30127 raw30127Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw30127 raw30127Labels = mixedMoment B raw30127step0 raw30127step0Labels := by
      have hz : ∀ j, raw30127 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30127step0 = (fun i j => raw30127 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30127step0 raw30127; decide +kernel
      have hl : raw30127step0Labels = raw30127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30127 raw30127Labels permutation346 hz
    mixedMoment B raw30127step0 raw30127step0Labels = mixedMoment B raw30127step1 raw30127step1Labels := by
      have ha : raw30127step1 = (fun i j => raw30127step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30127step1 raw30127step0; decide +kernel
      have hl : raw30127step1Labels = raw30127step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30127step0 raw30127step0Labels permutation127 permutation2
    mixedMoment B raw30127step1 raw30127step1Labels = mixedMoment B raw30127step2 raw30127step2Labels := by
      have ha : raw30127step2 = -raw30127step1 := by apply Matrix.ext; change ∀ i j, raw30127step2 i j = -(raw30127step1 i j); unfold raw30127step2 raw30127step1; decide +kernel
      have hl : raw30127step2Labels = raw30127step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3693 node3693Labels := by rfl

def raw30128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30128Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30128step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30128step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30128 raw30128Labels = mixedMoment B node2348 node2348Labels := by
  calc
    mixedMoment B raw30128 raw30128Labels = mixedMoment B raw30128step0 raw30128step0Labels := by
      have ha : raw30128step0 = (fun i j => raw30128 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30128step0 raw30128; decide +kernel
      have hl : raw30128step0Labels = raw30128Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30128 raw30128Labels permutation159 permutation2
    _ = mixedMoment B node2348 node2348Labels := by rfl

def raw30129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30129Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30129step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30129step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30129 raw30129Labels = mixedMoment B node2356 node2356Labels := by
  calc
    mixedMoment B raw30129 raw30129Labels = mixedMoment B raw30129step0 raw30129step0Labels := by
      have hz : ∀ j, raw30129 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30129step0 = (fun i j => raw30129 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30129step0 raw30129; decide +kernel
      have hl : raw30129step0Labels = raw30129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30129 raw30129Labels permutation346 hz
    mixedMoment B raw30129step0 raw30129step0Labels = mixedMoment B raw30129step1 raw30129step1Labels := by
      have ha : raw30129step1 = (fun i j => raw30129step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30129step1 raw30129step0; decide +kernel
      have hl : raw30129step1Labels = raw30129step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30129step0 raw30129step0Labels permutation33 permutation2
    _ = mixedMoment B node2356 node2356Labels := by rfl

def raw30130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30130Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30130step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw30130step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw30130step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30130 raw30130Labels = mixedMoment B node2325 node2325Labels := by
  calc
    mixedMoment B raw30130 raw30130Labels = mixedMoment B raw30130step0 raw30130step0Labels := by
      have hz : ∀ j, raw30130 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30130step0 = (fun i j => raw30130 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30130step0 raw30130; decide +kernel
      have hl : raw30130step0Labels = raw30130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30130 raw30130Labels permutation346 hz
    mixedMoment B raw30130step0 raw30130step0Labels = mixedMoment B raw30130step1 raw30130step1Labels := by
      have ha : raw30130step1 = (fun i j => raw30130step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30130step1 raw30130step0; decide +kernel
      have hl : raw30130step1Labels = raw30130step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30130step0 raw30130step0Labels permutation127 permutation2
    mixedMoment B raw30130step1 raw30130step1Labels = mixedMoment B raw30130step2 raw30130step2Labels := by
      have ha : raw30130step2 = -raw30130step1 := by apply Matrix.ext; change ∀ i j, raw30130step2 i j = -(raw30130step1 i j); unfold raw30130step2 raw30130step1; decide +kernel
      have hl : raw30130step2Labels = raw30130step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2325 node2325Labels := by rfl

def raw30131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30131Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30131step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30131 raw30131Labels = mixedMoment B node2352 node2352Labels := by
  calc
    mixedMoment B raw30131 raw30131Labels = mixedMoment B raw30131step0 raw30131step0Labels := by
      have hz : ∀ j, raw30131 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30131step0 = (fun i j => raw30131 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30131step0 raw30131; decide +kernel
      have hl : raw30131step0Labels = raw30131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30131 raw30131Labels permutation346 hz
    _ = mixedMoment B node2352 node2352Labels := by rfl

def raw30132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30132Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30132step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30132 raw30132Labels = mixedMoment B node2428 node2428Labels := by
  calc
    mixedMoment B raw30132 raw30132Labels = mixedMoment B raw30132step0 raw30132step0Labels := by
      have ha : raw30132step0 = (fun i j => raw30132 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30132step0 raw30132; decide +kernel
      have hl : raw30132step0Labels = raw30132Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30132 raw30132Labels permutation201 permutation2
    _ = mixedMoment B node2428 node2428Labels := by rfl

def raw30133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30133Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30133step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30133 raw30133Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw30133 raw30133Labels = mixedMoment B raw30133step0 raw30133step0Labels := by
      have ha : raw30133step0 = (fun i j => raw30133 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30133step0 raw30133; decide +kernel
      have hl : raw30133step0Labels = raw30133Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30133 raw30133Labels permutation159 permutation2
    _ = mixedMoment B node2553 node2553Labels := by rfl

def raw30134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30134Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw30134step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30134step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30134step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30134 raw30134Labels = mixedMoment B node3689 node3689Labels := by
  calc
    mixedMoment B raw30134 raw30134Labels = mixedMoment B raw30134step0 raw30134step0Labels := by
      have ha : raw30134step0 = (fun i j => raw30134 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30134step0 raw30134; decide +kernel
      have hl : raw30134step0Labels = raw30134Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30134 raw30134Labels permutation587 permutation2
    mixedMoment B raw30134step0 raw30134step0Labels = mixedMoment B raw30134step1 raw30134step1Labels := by
      have ha : raw30134step1 = -raw30134step0 := by apply Matrix.ext; change ∀ i j, raw30134step1 i j = -(raw30134step0 i j); unfold raw30134step1 raw30134step0; decide +kernel
      have hl : raw30134step1Labels = raw30134step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3689 node3689Labels := by rfl

def raw30135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30135Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30135step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30135step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30135 raw30135Labels = mixedMoment B node2525 node2525Labels := by
  calc
    mixedMoment B raw30135 raw30135Labels = mixedMoment B raw30135step0 raw30135step0Labels := by
      have ha : raw30135step0 = (fun i j => raw30135 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30135step0 raw30135; decide +kernel
      have hl : raw30135step0Labels = raw30135Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30135 raw30135Labels permutation153 permutation2
    _ = mixedMoment B node2525 node2525Labels := by rfl

def raw30136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30136Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw30136step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw30136step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30136 raw30136Labels = mixedMoment B node2319 node2319Labels := by
  calc
    mixedMoment B raw30136 raw30136Labels = mixedMoment B raw30136step0 raw30136step0Labels := by
      have ha : raw30136step0 = (fun i j => raw30136 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30136step0 raw30136; decide +kernel
      have hl : raw30136step0Labels = raw30136Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30136 raw30136Labels permutation587 permutation2
    mixedMoment B raw30136step0 raw30136step0Labels = mixedMoment B raw30136step1 raw30136step1Labels := by
      have ha : raw30136step1 = -raw30136step0 := by apply Matrix.ext; change ∀ i j, raw30136step1 i j = -(raw30136step0 i j); unfold raw30136step1 raw30136step0; decide +kernel
      have hl : raw30136step1Labels = raw30136step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2319 node2319Labels := by rfl

def raw30137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30137Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30137 raw30137Labels = mixedMoment B node2524 node2524Labels := by
  calc
    _ = mixedMoment B node2524 node2524Labels := by rfl

def raw30138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30138Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30138step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30138step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30138 raw30138Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw30138 raw30138Labels = mixedMoment B raw30138step0 raw30138step0Labels := by
      have hz : ∀ j, raw30138 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30138step0 = (fun i j => raw30138 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30138step0 raw30138; decide +kernel
      have hl : raw30138step0Labels = raw30138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30138 raw30138Labels permutation346 hz
    mixedMoment B raw30138step0 raw30138step0Labels = mixedMoment B raw30138step1 raw30138step1Labels := by
      have ha : raw30138step1 = (fun i j => raw30138step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30138step1 raw30138step0; decide +kernel
      have hl : raw30138step1Labels = raw30138step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30138step0 raw30138step0Labels permutation33 permutation2
    _ = mixedMoment B node2590 node2590Labels := by rfl

def raw30139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30139step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30139step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30139step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30139 raw30139Labels = mixedMoment B node4323 node4323Labels := by
  calc
    mixedMoment B raw30139 raw30139Labels = mixedMoment B raw30139step0 raw30139step0Labels := by
      have ha : raw30139step0 = (fun i j => raw30139 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30139step0 raw30139; decide +kernel
      have hl : raw30139step0Labels = raw30139Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30139 raw30139Labels permutation159 permutation3
    mixedMoment B raw30139step0 raw30139step0Labels = mixedMoment B raw30139step1 raw30139step1Labels := by
      have ha : raw30139step1 = raw30139step0 := by apply Matrix.ext; unfold raw30139step1 raw30139step0; decide +kernel
      have hl : raw30139step0Labels = labelEmbedding6 ∘ raw30139step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30139step0 raw30139step0Labels raw30139step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4323 node4323Labels := by rfl

def raw30140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30140step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30140step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30140step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30140 raw30140Labels = mixedMoment B node4928 node4928Labels := by
  calc
    mixedMoment B raw30140 raw30140Labels = mixedMoment B raw30140step0 raw30140step0Labels := by
      have ha : raw30140step0 = (fun i j => raw30140 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30140step0 raw30140; decide +kernel
      have hl : raw30140step0Labels = raw30140Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30140 raw30140Labels permutation159 permutation3
    mixedMoment B raw30140step0 raw30140step0Labels = mixedMoment B raw30140step1 raw30140step1Labels := by
      have ha : raw30140step1 = raw30140step0 := by apply Matrix.ext; unfold raw30140step1 raw30140step0; decide +kernel
      have hl : raw30140step0Labels = labelEmbedding6 ∘ raw30140step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30140step0 raw30140step0Labels raw30140step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4928 node4928Labels := by rfl

def raw30141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30141step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30141step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30141 raw30141Labels = mixedMoment B node4987 node4987Labels := by
  calc
    mixedMoment B raw30141 raw30141Labels = mixedMoment B raw30141step0 raw30141step0Labels := by
      have ha : raw30141step0 = (fun i j => raw30141 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30141step0 raw30141; decide +kernel
      have hl : raw30141step0Labels = raw30141Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30141 raw30141Labels permutation201 permutation3
    mixedMoment B raw30141step0 raw30141step0Labels = mixedMoment B raw30141step1 raw30141step1Labels := by
      have ha : raw30141step1 = raw30141step0 := by apply Matrix.ext; unfold raw30141step1 raw30141step0; decide +kernel
      have hl : raw30141step0Labels = labelEmbedding6 ∘ raw30141step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30141step0 raw30141step0Labels raw30141step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4987 node4987Labels := by rfl

def raw30142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw30142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30142step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30142step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30142step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30142step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30142 raw30142Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw30142 raw30142Labels = mixedMoment B raw30142step0 raw30142step0Labels := by
      have ha : raw30142step0 = (fun i j => raw30142 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30142step0 raw30142; decide +kernel
      have hl : raw30142step0Labels = raw30142Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30142 raw30142Labels permutation162 permutation3
    mixedMoment B raw30142step0 raw30142step0Labels = mixedMoment B raw30142step1 raw30142step1Labels := by
      have ha : raw30142step1 = raw30142step0 := by apply Matrix.ext; unfold raw30142step1 raw30142step0; decide +kernel
      have hl : raw30142step0Labels = labelEmbedding6 ∘ raw30142step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30142step0 raw30142step0Labels raw30142step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw30143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30143step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30143step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30143 raw30143Labels = mixedMoment B node4349 node4349Labels := by
  calc
    mixedMoment B raw30143 raw30143Labels = mixedMoment B raw30143step0 raw30143step0Labels := by
      have hz : ∀ j, raw30143 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30143step0 = (fun i j => raw30143 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30143step0 raw30143; decide +kernel
      have hl : raw30143step0Labels = raw30143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30143 raw30143Labels permutation346 hz
    mixedMoment B raw30143step0 raw30143step0Labels = mixedMoment B raw30143step1 raw30143step1Labels := by
      have ha : raw30143step1 = (fun i j => raw30143step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30143step1 raw30143step0; decide +kernel
      have hl : raw30143step1Labels = raw30143step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30143step0 raw30143step0Labels permutation33 permutation3
    mixedMoment B raw30143step1 raw30143step1Labels = mixedMoment B raw30143step2 raw30143step2Labels := by
      have ha : raw30143step2 = raw30143step1 := by apply Matrix.ext; unfold raw30143step2 raw30143step1; decide +kernel
      have hl : raw30143step1Labels = labelEmbedding6 ∘ raw30143step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30143step1 raw30143step1Labels raw30143step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4349 node4349Labels := by rfl

def raw30144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30144step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30144step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30144step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30144 raw30144Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw30144 raw30144Labels = mixedMoment B raw30144step0 raw30144step0Labels := by
      have hz : ∀ j, raw30144 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30144step0 = (fun i j => raw30144 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30144step0 raw30144; decide +kernel
      have hl : raw30144step0Labels = raw30144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30144 raw30144Labels permutation346 hz
    mixedMoment B raw30144step0 raw30144step0Labels = mixedMoment B raw30144step1 raw30144step1Labels := by
      have ha : raw30144step1 = (fun i j => raw30144step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30144step1 raw30144step0; decide +kernel
      have hl : raw30144step1Labels = raw30144step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30144step0 raw30144step0Labels permutation33 permutation3
    mixedMoment B raw30144step1 raw30144step1Labels = mixedMoment B raw30144step2 raw30144step2Labels := by
      have ha : raw30144step2 = raw30144step1 := by apply Matrix.ext; unfold raw30144step2 raw30144step1; decide +kernel
      have hl : raw30144step1Labels = labelEmbedding6 ∘ raw30144step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30144step1 raw30144step1Labels raw30144step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4946 node4946Labels := by rfl

def raw30145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30145step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30145step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30145step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30145step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30145 raw30145Labels = mixedMoment B node5036 node5036Labels := by
  calc
    mixedMoment B raw30145 raw30145Labels = mixedMoment B raw30145step0 raw30145step0Labels := by
      have ha : raw30145step0 = (fun i j => raw30145 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30145step0 raw30145; decide +kernel
      have hl : raw30145step0Labels = raw30145Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30145 raw30145Labels permutation177 permutation3
    mixedMoment B raw30145step0 raw30145step0Labels = mixedMoment B raw30145step1 raw30145step1Labels := by
      have ha : raw30145step1 = raw30145step0 := by apply Matrix.ext; unfold raw30145step1 raw30145step0; decide +kernel
      have hl : raw30145step0Labels = labelEmbedding6 ∘ raw30145step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30145step0 raw30145step0Labels raw30145step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5036 node5036Labels := by rfl

def raw30146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw30146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw30146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30146step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30146step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30146step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30146 raw30146Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw30146 raw30146Labels = mixedMoment B raw30146step0 raw30146step0Labels := by
      have hz : ∀ j, raw30146 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30146step0 = (fun i j => raw30146 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30146step0 raw30146; decide +kernel
      have hl : raw30146step0Labels = raw30146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30146 raw30146Labels permutation346 hz
    mixedMoment B raw30146step0 raw30146step0Labels = mixedMoment B raw30146step1 raw30146step1Labels := by
      have ha : raw30146step1 = (fun i j => raw30146step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30146step1 raw30146step0; decide +kernel
      have hl : raw30146step1Labels = raw30146step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30146step0 raw30146step0Labels permutation33 permutation3
    mixedMoment B raw30146step1 raw30146step1Labels = mixedMoment B raw30146step2 raw30146step2Labels := by
      have ha : raw30146step2 = raw30146step1 := by apply Matrix.ext; unfold raw30146step2 raw30146step1; decide +kernel
      have hl : raw30146step1Labels = labelEmbedding6 ∘ raw30146step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30146step1 raw30146step1Labels raw30146step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5168 node5168Labels := by rfl

def raw30147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw30147step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw30147step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30147 raw30147Labels = mixedMoment B node4324 node4324Labels := by
  calc
    mixedMoment B raw30147 raw30147Labels = mixedMoment B raw30147step0 raw30147step0Labels := by
      have hz : ∀ j, raw30147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30147step0 = (fun i j => raw30147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30147step0 raw30147; decide +kernel
      have hl : raw30147step0Labels = raw30147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30147 raw30147Labels permutation346 hz
    mixedMoment B raw30147step0 raw30147step0Labels = mixedMoment B raw30147step1 raw30147step1Labels := by
      have ha : raw30147step1 = (fun i j => raw30147step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30147step1 raw30147step0; decide +kernel
      have hl : raw30147step1Labels = raw30147step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30147step0 raw30147step0Labels permutation33 permutation3
    mixedMoment B raw30147step1 raw30147step1Labels = mixedMoment B raw30147step2 raw30147step2Labels := by
      have ha : raw30147step2 = raw30147step1 := by apply Matrix.ext; unfold raw30147step2 raw30147step1; decide +kernel
      have hl : raw30147step1Labels = labelEmbedding6 ∘ raw30147step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30147step1 raw30147step1Labels raw30147step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4324 node4324Labels := by rfl

def raw30148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw30148step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw30148step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30148step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw30148step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30148 raw30148Labels = mixedMoment B node4637 node4637Labels := by
  calc
    mixedMoment B raw30148 raw30148Labels = mixedMoment B raw30148step0 raw30148step0Labels := by
      have hz : ∀ j, raw30148 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30148step0 = (fun i j => raw30148 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30148step0 raw30148; decide +kernel
      have hl : raw30148step0Labels = raw30148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30148 raw30148Labels permutation346 hz
    mixedMoment B raw30148step0 raw30148step0Labels = mixedMoment B raw30148step1 raw30148step1Labels := by
      have ha : raw30148step1 = (fun i j => raw30148step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30148step1 raw30148step0; decide +kernel
      have hl : raw30148step1Labels = raw30148step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30148step0 raw30148step0Labels permutation127 permutation3
    mixedMoment B raw30148step1 raw30148step1Labels = mixedMoment B raw30148step2 raw30148step2Labels := by
      have ha : raw30148step2 = -raw30148step1 := by apply Matrix.ext; change ∀ i j, raw30148step2 i j = -(raw30148step1 i j); unfold raw30148step2 raw30148step1; decide +kernel
      have hl : raw30148step2Labels = raw30148step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30148step2 raw30148step2Labels = mixedMoment B raw30148step3 raw30148step3Labels := by
      have ha : raw30148step3 = raw30148step2 := by apply Matrix.ext; unfold raw30148step3 raw30148step2; decide +kernel
      have hl : raw30148step2Labels = labelEmbedding6 ∘ raw30148step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30148step2 raw30148step2Labels raw30148step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4637 node4637Labels := by rfl

def raw30149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30149step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30149step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30149step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30149step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30149step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30149 raw30149Labels = mixedMoment B node4631 node4631Labels := by
  calc
    mixedMoment B raw30149 raw30149Labels = mixedMoment B raw30149step0 raw30149step0Labels := by
      have ha : raw30149step0 = (fun i j => raw30149 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30149step0 raw30149; decide +kernel
      have hl : raw30149step0Labels = raw30149Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30149 raw30149Labels permutation587 permutation3
    mixedMoment B raw30149step0 raw30149step0Labels = mixedMoment B raw30149step1 raw30149step1Labels := by
      have ha : raw30149step1 = -raw30149step0 := by apply Matrix.ext; change ∀ i j, raw30149step1 i j = -(raw30149step0 i j); unfold raw30149step1 raw30149step0; decide +kernel
      have hl : raw30149step1Labels = raw30149step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30149step1 raw30149step1Labels = mixedMoment B raw30149step2 raw30149step2Labels := by
      have ha : raw30149step2 = raw30149step1 := by apply Matrix.ext; unfold raw30149step2 raw30149step1; decide +kernel
      have hl : raw30149step1Labels = labelEmbedding6 ∘ raw30149step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30149step1 raw30149step1Labels raw30149step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4631 node4631Labels := by rfl

def raw30150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw30150step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw30150step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30150step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw30150step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30150 raw30150Labels = mixedMoment B node4644 node4644Labels := by
  calc
    mixedMoment B raw30150 raw30150Labels = mixedMoment B raw30150step0 raw30150step0Labels := by
      have hz : ∀ j, raw30150 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30150step0 = (fun i j => raw30150 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30150step0 raw30150; decide +kernel
      have hl : raw30150step0Labels = raw30150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30150 raw30150Labels permutation346 hz
    mixedMoment B raw30150step0 raw30150step0Labels = mixedMoment B raw30150step1 raw30150step1Labels := by
      have ha : raw30150step1 = (fun i j => raw30150step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30150step1 raw30150step0; decide +kernel
      have hl : raw30150step1Labels = raw30150step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30150step0 raw30150step0Labels permutation125 permutation3
    mixedMoment B raw30150step1 raw30150step1Labels = mixedMoment B raw30150step2 raw30150step2Labels := by
      have ha : raw30150step2 = -raw30150step1 := by apply Matrix.ext; change ∀ i j, raw30150step2 i j = -(raw30150step1 i j); unfold raw30150step2 raw30150step1; decide +kernel
      have hl : raw30150step2Labels = raw30150step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30150step2 raw30150step2Labels = mixedMoment B raw30150step3 raw30150step3Labels := by
      have ha : raw30150step3 = raw30150step2 := by apply Matrix.ext; unfold raw30150step3 raw30150step2; decide +kernel
      have hl : raw30150step2Labels = labelEmbedding6 ∘ raw30150step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30150step2 raw30150step2Labels raw30150step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4644 node4644Labels := by rfl

def raw30151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw30151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw30151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw30151step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30151step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw30151step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30151step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw30151step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30151 raw30151Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw30151 raw30151Labels = mixedMoment B raw30151step0 raw30151step0Labels := by
      have hz : ∀ j, raw30151 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30151step0 = (fun i j => raw30151 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30151step0 raw30151; decide +kernel
      have hl : raw30151step0Labels = raw30151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30151 raw30151Labels permutation346 hz
    mixedMoment B raw30151step0 raw30151step0Labels = mixedMoment B raw30151step1 raw30151step1Labels := by
      have ha : raw30151step1 = (fun i j => raw30151step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30151step1 raw30151step0; decide +kernel
      have hl : raw30151step1Labels = raw30151step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30151step0 raw30151step0Labels permutation127 permutation3
    mixedMoment B raw30151step1 raw30151step1Labels = mixedMoment B raw30151step2 raw30151step2Labels := by
      have ha : raw30151step2 = -raw30151step1 := by apply Matrix.ext; change ∀ i j, raw30151step2 i j = -(raw30151step1 i j); unfold raw30151step2 raw30151step1; decide +kernel
      have hl : raw30151step2Labels = raw30151step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30151step2 raw30151step2Labels = mixedMoment B raw30151step3 raw30151step3Labels := by
      have ha : raw30151step3 = raw30151step2 := by apply Matrix.ext; unfold raw30151step3 raw30151step2; decide +kernel
      have hl : raw30151step2Labels = labelEmbedding6 ∘ raw30151step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30151step2 raw30151step2Labels raw30151step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw30152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30152Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30152step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30152step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30152 raw30152Labels = mixedMoment B node901 node901Labels := by
  calc
    mixedMoment B raw30152 raw30152Labels = mixedMoment B raw30152step0 raw30152step0Labels := by
      have ha : raw30152step0 = (fun i j => raw30152 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30152step0 raw30152; decide +kernel
      have hl : raw30152step0Labels = raw30152Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30152 raw30152Labels permutation159 permutation3
    _ = mixedMoment B node901 node901Labels := by rfl

def raw30153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30153Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30153step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30153step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30153 raw30153Labels = mixedMoment B node2318 node2318Labels := by
  calc
    mixedMoment B raw30153 raw30153Labels = mixedMoment B raw30153step0 raw30153step0Labels := by
      have ha : raw30153step0 = (fun i j => raw30153 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30153step0 raw30153; decide +kernel
      have hl : raw30153step0Labels = raw30153Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30153 raw30153Labels permutation159 permutation3
    _ = mixedMoment B node2318 node2318Labels := by rfl

def raw30154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30154Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30154step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30154 raw30154Labels = mixedMoment B node2372 node2372Labels := by
  calc
    mixedMoment B raw30154 raw30154Labels = mixedMoment B raw30154step0 raw30154step0Labels := by
      have ha : raw30154step0 = (fun i j => raw30154 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30154step0 raw30154; decide +kernel
      have hl : raw30154step0Labels = raw30154Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30154 raw30154Labels permutation201 permutation3
    _ = mixedMoment B node2372 node2372Labels := by rfl

def raw30155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw30155Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30155step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30155 raw30155Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw30155 raw30155Labels = mixedMoment B raw30155step0 raw30155step0Labels := by
      have ha : raw30155step0 = (fun i j => raw30155 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30155step0 raw30155; decide +kernel
      have hl : raw30155step0Labels = raw30155Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30155 raw30155Labels permutation162 permutation3
    _ = mixedMoment B node2553 node2553Labels := by rfl

def raw30156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30156Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30156step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30156step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30156 raw30156Labels = mixedMoment B node927 node927Labels := by
  calc
    mixedMoment B raw30156 raw30156Labels = mixedMoment B raw30156step0 raw30156step0Labels := by
      have hz : ∀ j, raw30156 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30156step0 = (fun i j => raw30156 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30156step0 raw30156; decide +kernel
      have hl : raw30156step0Labels = raw30156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30156 raw30156Labels permutation346 hz
    mixedMoment B raw30156step0 raw30156step0Labels = mixedMoment B raw30156step1 raw30156step1Labels := by
      have ha : raw30156step1 = (fun i j => raw30156step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30156step1 raw30156step0; decide +kernel
      have hl : raw30156step1Labels = raw30156step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30156step0 raw30156step0Labels permutation33 permutation3
    _ = mixedMoment B node927 node927Labels := by rfl

def raw30157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30157Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30157step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30157step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30157step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30157 raw30157Labels = mixedMoment B node2337 node2337Labels := by
  calc
    mixedMoment B raw30157 raw30157Labels = mixedMoment B raw30157step0 raw30157step0Labels := by
      have hz : ∀ j, raw30157 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30157step0 = (fun i j => raw30157 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30157step0 raw30157; decide +kernel
      have hl : raw30157step0Labels = raw30157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30157 raw30157Labels permutation346 hz
    mixedMoment B raw30157step0 raw30157step0Labels = mixedMoment B raw30157step1 raw30157step1Labels := by
      have ha : raw30157step1 = (fun i j => raw30157step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30157step1 raw30157step0; decide +kernel
      have hl : raw30157step1Labels = raw30157step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30157step0 raw30157step0Labels permutation33 permutation3
    _ = mixedMoment B node2337 node2337Labels := by rfl

def raw30158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30158Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30158step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30158step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30158 raw30158Labels = mixedMoment B node2428 node2428Labels := by
  calc
    mixedMoment B raw30158 raw30158Labels = mixedMoment B raw30158step0 raw30158step0Labels := by
      have ha : raw30158step0 = (fun i j => raw30158 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30158step0 raw30158; decide +kernel
      have hl : raw30158step0Labels = raw30158Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30158 raw30158Labels permutation177 permutation3
    _ = mixedMoment B node2428 node2428Labels := by rfl

def raw30159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw30159Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw30159step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30159step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30159 raw30159Labels = mixedMoment B node2594 node2594Labels := by
  calc
    mixedMoment B raw30159 raw30159Labels = mixedMoment B raw30159step0 raw30159step0Labels := by
      have hz : ∀ j, raw30159 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30159step0 = (fun i j => raw30159 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30159step0 raw30159; decide +kernel
      have hl : raw30159step0Labels = raw30159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30159 raw30159Labels permutation346 hz
    mixedMoment B raw30159step0 raw30159step0Labels = mixedMoment B raw30159step1 raw30159step1Labels := by
      have ha : raw30159step1 = (fun i j => raw30159step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30159step1 raw30159step0; decide +kernel
      have hl : raw30159step1Labels = raw30159step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30159step0 raw30159step0Labels permutation33 permutation3
    _ = mixedMoment B node2594 node2594Labels := by rfl

def raw30160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30160Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30160step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw30160step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30160 raw30160Labels = mixedMoment B node902 node902Labels := by
  calc
    mixedMoment B raw30160 raw30160Labels = mixedMoment B raw30160step0 raw30160step0Labels := by
      have hz : ∀ j, raw30160 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30160step0 = (fun i j => raw30160 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30160step0 raw30160; decide +kernel
      have hl : raw30160step0Labels = raw30160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30160 raw30160Labels permutation346 hz
    mixedMoment B raw30160step0 raw30160step0Labels = mixedMoment B raw30160step1 raw30160step1Labels := by
      have ha : raw30160step1 = (fun i j => raw30160step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30160step1 raw30160step0; decide +kernel
      have hl : raw30160step1Labels = raw30160step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30160step0 raw30160step0Labels permutation33 permutation3
    _ = mixedMoment B node902 node902Labels := by rfl

def raw30161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30161Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30161step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw30161step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30161step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw30161step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30161 raw30161Labels = mixedMoment B node1766 node1766Labels := by
  calc
    mixedMoment B raw30161 raw30161Labels = mixedMoment B raw30161step0 raw30161step0Labels := by
      have hz : ∀ j, raw30161 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30161step0 = (fun i j => raw30161 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30161step0 raw30161; decide +kernel
      have hl : raw30161step0Labels = raw30161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30161 raw30161Labels permutation346 hz
    mixedMoment B raw30161step0 raw30161step0Labels = mixedMoment B raw30161step1 raw30161step1Labels := by
      have ha : raw30161step1 = (fun i j => raw30161step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30161step1 raw30161step0; decide +kernel
      have hl : raw30161step1Labels = raw30161step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30161step0 raw30161step0Labels permutation127 permutation3
    mixedMoment B raw30161step1 raw30161step1Labels = mixedMoment B raw30161step2 raw30161step2Labels := by
      have ha : raw30161step2 = -raw30161step1 := by apply Matrix.ext; change ∀ i j, raw30161step2 i j = -(raw30161step1 i j); unfold raw30161step2 raw30161step1; decide +kernel
      have hl : raw30161step2Labels = raw30161step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1766 node1766Labels := by rfl

def raw30162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30162Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30162step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30162step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30162step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30162step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30162 raw30162Labels = mixedMoment B node1760 node1760Labels := by
  calc
    mixedMoment B raw30162 raw30162Labels = mixedMoment B raw30162step0 raw30162step0Labels := by
      have ha : raw30162step0 = (fun i j => raw30162 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30162step0 raw30162; decide +kernel
      have hl : raw30162step0Labels = raw30162Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30162 raw30162Labels permutation587 permutation3
    mixedMoment B raw30162step0 raw30162step0Labels = mixedMoment B raw30162step1 raw30162step1Labels := by
      have ha : raw30162step1 = -raw30162step0 := by apply Matrix.ext; change ∀ i j, raw30162step1 i j = -(raw30162step0 i j); unfold raw30162step1 raw30162step0; decide +kernel
      have hl : raw30162step1Labels = raw30162step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1760 node1760Labels := by rfl

def raw30163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30163Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw30163step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw30163step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30163step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw30163step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30163 raw30163Labels = mixedMoment B node1773 node1773Labels := by
  calc
    mixedMoment B raw30163 raw30163Labels = mixedMoment B raw30163step0 raw30163step0Labels := by
      have hz : ∀ j, raw30163 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30163step0 = (fun i j => raw30163 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30163step0 raw30163; decide +kernel
      have hl : raw30163step0Labels = raw30163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30163 raw30163Labels permutation346 hz
    mixedMoment B raw30163step0 raw30163step0Labels = mixedMoment B raw30163step1 raw30163step1Labels := by
      have ha : raw30163step1 = (fun i j => raw30163step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30163step1 raw30163step0; decide +kernel
      have hl : raw30163step1Labels = raw30163step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30163step0 raw30163step0Labels permutation125 permutation3
    mixedMoment B raw30163step1 raw30163step1Labels = mixedMoment B raw30163step2 raw30163step2Labels := by
      have ha : raw30163step2 = -raw30163step1 := by apply Matrix.ext; change ∀ i j, raw30163step2 i j = -(raw30163step1 i j); unfold raw30163step2 raw30163step1; decide +kernel
      have hl : raw30163step2Labels = raw30163step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1773 node1773Labels := by rfl

def raw30164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw30164Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw30164step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw30164step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30164step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw30164step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30164 raw30164Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw30164 raw30164Labels = mixedMoment B raw30164step0 raw30164step0Labels := by
      have hz : ∀ j, raw30164 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30164step0 = (fun i j => raw30164 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30164step0 raw30164; decide +kernel
      have hl : raw30164step0Labels = raw30164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30164 raw30164Labels permutation346 hz
    mixedMoment B raw30164step0 raw30164step0Labels = mixedMoment B raw30164step1 raw30164step1Labels := by
      have ha : raw30164step1 = (fun i j => raw30164step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30164step1 raw30164step0; decide +kernel
      have hl : raw30164step1Labels = raw30164step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30164step0 raw30164step0Labels permutation127 permutation3
    mixedMoment B raw30164step1 raw30164step1Labels = mixedMoment B raw30164step2 raw30164step2Labels := by
      have ha : raw30164step2 = -raw30164step1 := by apply Matrix.ext; change ∀ i j, raw30164step2 i j = -(raw30164step1 i j); unfold raw30164step2 raw30164step1; decide +kernel
      have hl : raw30164step2Labels = raw30164step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2022 node2022Labels := by rfl

def raw30165 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30165Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30165step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30165step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30165step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30165step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30165 raw30165Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw30165 raw30165Labels = mixedMoment B raw30165step0 raw30165step0Labels := by
      have hz : ∀ j, raw30165 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30165step0 = (fun i j => raw30165 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30165step0 raw30165; decide +kernel
      have hl : raw30165step0Labels = raw30165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30165 raw30165Labels permutation346 hz
    mixedMoment B raw30165step0 raw30165step0Labels = mixedMoment B raw30165step1 raw30165step1Labels := by
      have ha : raw30165step1 = (fun i j => raw30165step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30165step1 raw30165step0; decide +kernel
      have hl : raw30165step1Labels = raw30165step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30165step0 raw30165step0Labels permutation32 permutation7
    mixedMoment B raw30165step1 raw30165step1Labels = mixedMoment B raw30165step2 raw30165step2Labels := by
      have ha : raw30165step2 = raw30165step1 := by apply Matrix.ext; unfold raw30165step2 raw30165step1; decide +kernel
      have hl : raw30165step1Labels = labelEmbedding10 ∘ raw30165step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30165step1 raw30165step1Labels raw30165step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw30166 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30166Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30166step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30166step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30166step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30166 raw30166Labels = mixedMoment B node5067 node5067Labels := by
  calc
    mixedMoment B raw30166 raw30166Labels = mixedMoment B raw30166step0 raw30166step0Labels := by
      have ha : raw30166step0 = (fun i j => raw30166 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30166step0 raw30166; decide +kernel
      have hl : raw30166step0Labels = raw30166Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30166 raw30166Labels permutation152 permutation7
    mixedMoment B raw30166step0 raw30166step0Labels = mixedMoment B raw30166step1 raw30166step1Labels := by
      have ha : raw30166step1 = raw30166step0 := by apply Matrix.ext; unfold raw30166step1 raw30166step0; decide +kernel
      have hl : raw30166step0Labels = labelEmbedding10 ∘ raw30166step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30166step0 raw30166step0Labels raw30166step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5067 node5067Labels := by rfl

def raw30167 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30167Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30167step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw30167step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30167step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw30167step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30167 raw30167Labels = mixedMoment B node5090 node5090Labels := by
  calc
    mixedMoment B raw30167 raw30167Labels = mixedMoment B raw30167step0 raw30167step0Labels := by
      have hz : ∀ j, raw30167 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30167step0 = (fun i j => raw30167 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30167step0 raw30167; decide +kernel
      have hl : raw30167step0Labels = raw30167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30167 raw30167Labels permutation346 hz
    mixedMoment B raw30167step0 raw30167step0Labels = mixedMoment B raw30167step1 raw30167step1Labels := by
      have ha : raw30167step1 = (fun i j => raw30167step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30167step1 raw30167step0; decide +kernel
      have hl : raw30167step1Labels = raw30167step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30167step0 raw30167step0Labels permutation32 permutation7
    mixedMoment B raw30167step1 raw30167step1Labels = mixedMoment B raw30167step2 raw30167step2Labels := by
      have ha : raw30167step2 = raw30167step1 := by apply Matrix.ext; unfold raw30167step2 raw30167step1; decide +kernel
      have hl : raw30167step1Labels = labelEmbedding10 ∘ raw30167step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30167step1 raw30167step1Labels raw30167step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5090 node5090Labels := by rfl

def raw30168 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30168Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30168step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30168step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30168step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30168 raw30168Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw30168 raw30168Labels = mixedMoment B raw30168step0 raw30168step0Labels := by
      have hz : ∀ j, raw30168 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30168step0 = (fun i j => raw30168 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30168step0 raw30168; decide +kernel
      have hl : raw30168step0Labels = raw30168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30168 raw30168Labels permutation346 hz
    mixedMoment B raw30168step0 raw30168step0Labels = mixedMoment B raw30168step1 raw30168step1Labels := by
      have ha : raw30168step1 = (fun i j => raw30168step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30168step1 raw30168step0; decide +kernel
      have hl : raw30168step1Labels = raw30168step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30168step0 raw30168step0Labels permutation32 permutation7
    mixedMoment B raw30168step1 raw30168step1Labels = mixedMoment B raw30168step2 raw30168step2Labels := by
      have ha : raw30168step2 = raw30168step1 := by apply Matrix.ext; unfold raw30168step2 raw30168step1; decide +kernel
      have hl : raw30168step1Labels = labelEmbedding10 ∘ raw30168step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30168step1 raw30168step1Labels raw30168step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw30169 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30169Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30169step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30169step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30169step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30169step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30169step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30169 raw30169Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw30169 raw30169Labels = mixedMoment B raw30169step0 raw30169step0Labels := by
      have hz : ∀ j, raw30169 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30169step0 = (fun i j => raw30169 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30169step0 raw30169; decide +kernel
      have hl : raw30169step0Labels = raw30169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30169 raw30169Labels permutation346 hz
    mixedMoment B raw30169step0 raw30169step0Labels = mixedMoment B raw30169step1 raw30169step1Labels := by
      have ha : raw30169step1 = (fun i j => raw30169step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30169step1 raw30169step0; decide +kernel
      have hl : raw30169step1Labels = raw30169step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30169step0 raw30169step0Labels permutation39 permutation4
    mixedMoment B raw30169step1 raw30169step1Labels = mixedMoment B raw30169step2 raw30169step2Labels := by
      have ha : raw30169step2 = -raw30169step1 := by apply Matrix.ext; change ∀ i j, raw30169step2 i j = -(raw30169step1 i j); unfold raw30169step2 raw30169step1; decide +kernel
      have hl : raw30169step2Labels = raw30169step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30169step2 raw30169step2Labels = mixedMoment B raw30169step3 raw30169step3Labels := by
      have ha : raw30169step3 = raw30169step2 := by apply Matrix.ext; unfold raw30169step3 raw30169step2; decide +kernel
      have hl : raw30169step2Labels = labelEmbedding7 ∘ raw30169step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30169step2 raw30169step2Labels raw30169step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

def raw30170 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30170Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30170step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30170step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30170step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30170step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30170 raw30170Labels = mixedMoment B node5181 node5181Labels := by
  calc
    mixedMoment B raw30170 raw30170Labels = mixedMoment B raw30170step0 raw30170step0Labels := by
      have ha : raw30170step0 = (fun i j => raw30170 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30170step0 raw30170; decide +kernel
      have hl : raw30170step0Labels = raw30170Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30170 raw30170Labels permutation153 permutation6
    mixedMoment B raw30170step0 raw30170step0Labels = mixedMoment B raw30170step1 raw30170step1Labels := by
      have ha : raw30170step1 = raw30170step0 := by apply Matrix.ext; unfold raw30170step1 raw30170step0; decide +kernel
      have hl : raw30170step0Labels = labelEmbedding9 ∘ raw30170step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30170step0 raw30170step0Labels raw30170step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5181 node5181Labels := by rfl

def raw30171 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30171Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30171step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw30171step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30171step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw30171step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30171 raw30171Labels = mixedMoment B node5180 node5180Labels := by
  calc
    mixedMoment B raw30171 raw30171Labels = mixedMoment B raw30171step0 raw30171step0Labels := by
      have hz : ∀ j, raw30171 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30171step0 = (fun i j => raw30171 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30171step0 raw30171; decide +kernel
      have hl : raw30171step0Labels = raw30171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30171 raw30171Labels permutation346 hz
    mixedMoment B raw30171step0 raw30171step0Labels = mixedMoment B raw30171step1 raw30171step1Labels := by
      have ha : raw30171step1 = (fun i j => raw30171step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30171step1 raw30171step0; decide +kernel
      have hl : raw30171step1Labels = raw30171step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30171step0 raw30171step0Labels permutation33 permutation6
    mixedMoment B raw30171step1 raw30171step1Labels = mixedMoment B raw30171step2 raw30171step2Labels := by
      have ha : raw30171step2 = raw30171step1 := by apply Matrix.ext; unfold raw30171step2 raw30171step1; decide +kernel
      have hl : raw30171step1Labels = labelEmbedding9 ∘ raw30171step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30171step1 raw30171step1Labels raw30171step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5180 node5180Labels := by rfl

def raw30172 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30172Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30172step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30172step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30172step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30172step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30172 raw30172Labels = mixedMoment B node5188 node5188Labels := by
  calc
    mixedMoment B raw30172 raw30172Labels = mixedMoment B raw30172step0 raw30172step0Labels := by
      have hz : ∀ j, raw30172 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30172step0 = (fun i j => raw30172 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30172step0 raw30172; decide +kernel
      have hl : raw30172step0Labels = raw30172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30172 raw30172Labels permutation346 hz
    mixedMoment B raw30172step0 raw30172step0Labels = mixedMoment B raw30172step1 raw30172step1Labels := by
      have ha : raw30172step1 = (fun i j => raw30172step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30172step1 raw30172step0; decide +kernel
      have hl : raw30172step1Labels = raw30172step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30172step0 raw30172step0Labels permutation33 permutation6
    mixedMoment B raw30172step1 raw30172step1Labels = mixedMoment B raw30172step2 raw30172step2Labels := by
      have ha : raw30172step2 = raw30172step1 := by apply Matrix.ext; unfold raw30172step2 raw30172step1; decide +kernel
      have hl : raw30172step1Labels = labelEmbedding9 ∘ raw30172step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30172step1 raw30172step1Labels raw30172step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5188 node5188Labels := by rfl

def raw30173 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30173Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30173step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30173step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30173step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30173 raw30173Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw30173 raw30173Labels = mixedMoment B raw30173step0 raw30173step0Labels := by
      have ha : raw30173step0 = (fun i j => raw30173 (permutation159 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30173step0 raw30173; decide +kernel
      have hl : raw30173step0Labels = raw30173Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30173 raw30173Labels permutation159 permutation6
    mixedMoment B raw30173step0 raw30173step0Labels = mixedMoment B raw30173step1 raw30173step1Labels := by
      have ha : raw30173step1 = raw30173step0 := by apply Matrix.ext; unfold raw30173step1 raw30173step0; decide +kernel
      have hl : raw30173step0Labels = labelEmbedding9 ∘ raw30173step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30173step0 raw30173step0Labels raw30173step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4782 node4782Labels := by rfl

def raw30174 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30174Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30174step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30174step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30174step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30174step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30174 raw30174Labels = mixedMoment B node5050 node5050Labels := by
  calc
    mixedMoment B raw30174 raw30174Labels = mixedMoment B raw30174step0 raw30174step0Labels := by
      have ha : raw30174step0 = (fun i j => raw30174 (permutation159 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30174step0 raw30174; decide +kernel
      have hl : raw30174step0Labels = raw30174Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30174 raw30174Labels permutation159 permutation6
    mixedMoment B raw30174step0 raw30174step0Labels = mixedMoment B raw30174step1 raw30174step1Labels := by
      have ha : raw30174step1 = raw30174step0 := by apply Matrix.ext; unfold raw30174step1 raw30174step0; decide +kernel
      have hl : raw30174step0Labels = labelEmbedding9 ∘ raw30174step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30174step0 raw30174step0Labels raw30174step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5050 node5050Labels := by rfl

def raw30175 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30175Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30175step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30175step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30175step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30175 raw30175Labels = mixedMoment B node5121 node5121Labels := by
  calc
    mixedMoment B raw30175 raw30175Labels = mixedMoment B raw30175step0 raw30175step0Labels := by
      have ha : raw30175step0 = (fun i j => raw30175 (permutation159 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30175step0 raw30175; decide +kernel
      have hl : raw30175step0Labels = raw30175Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30175 raw30175Labels permutation159 permutation6
    mixedMoment B raw30175step0 raw30175step0Labels = mixedMoment B raw30175step1 raw30175step1Labels := by
      have ha : raw30175step1 = raw30175step0 := by apply Matrix.ext; unfold raw30175step1 raw30175step0; decide +kernel
      have hl : raw30175step0Labels = labelEmbedding9 ∘ raw30175step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30175step0 raw30175step0Labels raw30175step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5121 node5121Labels := by rfl

def raw30176 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30176Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30176step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30176step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30176step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30176 raw30176Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw30176 raw30176Labels = mixedMoment B raw30176step0 raw30176step0Labels := by
      have ha : raw30176step0 = (fun i j => raw30176 (permutation159 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30176step0 raw30176; decide +kernel
      have hl : raw30176step0Labels = raw30176Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30176 raw30176Labels permutation159 permutation6
    mixedMoment B raw30176step0 raw30176step0Labels = mixedMoment B raw30176step1 raw30176step1Labels := by
      have ha : raw30176step1 = raw30176step0 := by apply Matrix.ext; unfold raw30176step1 raw30176step0; decide +kernel
      have hl : raw30176step0Labels = labelEmbedding9 ∘ raw30176step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30176step0 raw30176step0Labels raw30176step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5129 node5129Labels := by rfl

def raw30177 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw30177Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw30177step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw30177step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30177step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw30177step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30177step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw30177step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30177 raw30177Labels = mixedMoment B node4788 node4788Labels := by
  calc
    mixedMoment B raw30177 raw30177Labels = mixedMoment B raw30177step0 raw30177step0Labels := by
      have hz : ∀ j, raw30177 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30177step0 = (fun i j => raw30177 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30177step0 raw30177; decide +kernel
      have hl : raw30177step0Labels = raw30177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30177 raw30177Labels permutation346 hz
    mixedMoment B raw30177step0 raw30177step0Labels = mixedMoment B raw30177step1 raw30177step1Labels := by
      have ha : raw30177step1 = (fun i j => raw30177step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30177step1 raw30177step0; decide +kernel
      have hl : raw30177step1Labels = raw30177step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30177step0 raw30177step0Labels permutation39 permutation4
    mixedMoment B raw30177step1 raw30177step1Labels = mixedMoment B raw30177step2 raw30177step2Labels := by
      have ha : raw30177step2 = -raw30177step1 := by apply Matrix.ext; change ∀ i j, raw30177step2 i j = -(raw30177step1 i j); unfold raw30177step2 raw30177step1; decide +kernel
      have hl : raw30177step2Labels = raw30177step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30177step2 raw30177step2Labels = mixedMoment B raw30177step3 raw30177step3Labels := by
      have ha : raw30177step3 = raw30177step2 := by apply Matrix.ext; unfold raw30177step3 raw30177step2; decide +kernel
      have hl : raw30177step2Labels = labelEmbedding7 ∘ raw30177step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30177step2 raw30177step2Labels raw30177step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4788 node4788Labels := by rfl

def raw30178 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw30178Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw30178step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw30178step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw30178step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30178 raw30178Labels = mixedMoment B node5014 node5014Labels := by
  calc
    mixedMoment B raw30178 raw30178Labels = mixedMoment B raw30178step0 raw30178step0Labels := by
      have hz : ∀ j, raw30178 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30178step0 = (fun i j => raw30178 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30178step0 raw30178; decide +kernel
      have hl : raw30178step0Labels = raw30178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30178 raw30178Labels permutation346 hz
    mixedMoment B raw30178step0 raw30178step0Labels = mixedMoment B raw30178step1 raw30178step1Labels := by
      have ha : raw30178step1 = (fun i j => raw30178step0 (permutation127 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30178step1 raw30178step0; decide +kernel
      have hl : raw30178step1Labels = raw30178step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30178step0 raw30178step0Labels permutation127 permutation4
    mixedMoment B raw30178step1 raw30178step1Labels = mixedMoment B raw30178step2 raw30178step2Labels := by
      have ha : raw30178step2 = raw30178step1 := by apply Matrix.ext; unfold raw30178step2 raw30178step1; decide +kernel
      have hl : raw30178step1Labels = labelEmbedding7 ∘ raw30178step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30178step1 raw30178step1Labels raw30178step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5014 node5014Labels := by rfl

def raw30179 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw30179Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw30179step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30179step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw30179step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30179 raw30179Labels = mixedMoment B node4995 node4995Labels := by
  calc
    mixedMoment B raw30179 raw30179Labels = mixedMoment B raw30179step0 raw30179step0Labels := by
      have ha : raw30179step0 = (fun i j => raw30179 (permutation577 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30179step0 raw30179; decide +kernel
      have hl : raw30179step0Labels = raw30179Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30179 raw30179Labels permutation577 permutation4
    mixedMoment B raw30179step0 raw30179step0Labels = mixedMoment B raw30179step1 raw30179step1Labels := by
      have ha : raw30179step1 = raw30179step0 := by apply Matrix.ext; unfold raw30179step1 raw30179step0; decide +kernel
      have hl : raw30179step0Labels = labelEmbedding7 ∘ raw30179step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30179step0 raw30179step0Labels raw30179step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4995 node4995Labels := by rfl

def raw30180 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw30180Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 2, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw30180step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30180step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30180step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30180 raw30180Labels = mixedMoment B node5002 node5002Labels := by
  calc
    mixedMoment B raw30180 raw30180Labels = mixedMoment B raw30180step0 raw30180step0Labels := by
      have hz : ∀ j, raw30180 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30180step0 = (fun i j => raw30180 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30180step0 raw30180; decide +kernel
      have hl : raw30180step0Labels = raw30180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30180 raw30180Labels permutation346 hz
    mixedMoment B raw30180step0 raw30180step0Labels = mixedMoment B raw30180step1 raw30180step1Labels := by
      have ha : raw30180step1 = (fun i j => raw30180step0 (permutation125 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30180step1 raw30180step0; decide +kernel
      have hl : raw30180step1Labels = raw30180step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30180step0 raw30180step0Labels permutation125 permutation4
    mixedMoment B raw30180step1 raw30180step1Labels = mixedMoment B raw30180step2 raw30180step2Labels := by
      have ha : raw30180step2 = raw30180step1 := by apply Matrix.ext; unfold raw30180step2 raw30180step1; decide +kernel
      have hl : raw30180step1Labels = labelEmbedding7 ∘ raw30180step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30180step1 raw30180step1Labels raw30180step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5002 node5002Labels := by rfl

def raw30181 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30181Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30181step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw30181step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30181step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw30181step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30181 raw30181Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw30181 raw30181Labels = mixedMoment B raw30181step0 raw30181step0Labels := by
      have hz : ∀ j, raw30181 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30181step0 = (fun i j => raw30181 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30181step0 raw30181; decide +kernel
      have hl : raw30181step0Labels = raw30181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30181 raw30181Labels permutation346 hz
    mixedMoment B raw30181step0 raw30181step0Labels = mixedMoment B raw30181step1 raw30181step1Labels := by
      have ha : raw30181step1 = (fun i j => raw30181step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30181step1 raw30181step0; decide +kernel
      have hl : raw30181step1Labels = raw30181step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30181step0 raw30181step0Labels permutation33 permutation6
    mixedMoment B raw30181step1 raw30181step1Labels = mixedMoment B raw30181step2 raw30181step2Labels := by
      have ha : raw30181step2 = raw30181step1 := by apply Matrix.ext; unfold raw30181step2 raw30181step1; decide +kernel
      have hl : raw30181step1Labels = labelEmbedding9 ∘ raw30181step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30181step1 raw30181step1Labels raw30181step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5140 node5140Labels := by rfl

def raw30182 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30182step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw30182step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30182step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30182step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30182step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30182step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30182 raw30182Labels = mixedMoment B node4790 node4790Labels := by
  calc
    mixedMoment B raw30182 raw30182Labels = mixedMoment B raw30182step0 raw30182step0Labels := by
      have hz : ∀ j, raw30182 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30182step0 = (fun i j => raw30182 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30182step0 raw30182; decide +kernel
      have hl : raw30182step0Labels = raw30182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30182 raw30182Labels permutation346 hz
    mixedMoment B raw30182step0 raw30182step0Labels = mixedMoment B raw30182step1 raw30182step1Labels := by
      have ha : raw30182step1 = (fun i j => raw30182step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30182step1 raw30182step0; decide +kernel
      have hl : raw30182step1Labels = raw30182step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30182step0 raw30182step0Labels permutation38 permutation4
    mixedMoment B raw30182step1 raw30182step1Labels = mixedMoment B raw30182step2 raw30182step2Labels := by
      have ha : raw30182step2 = -raw30182step1 := by apply Matrix.ext; change ∀ i j, raw30182step2 i j = -(raw30182step1 i j); unfold raw30182step2 raw30182step1; decide +kernel
      have hl : raw30182step2Labels = raw30182step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30182step2 raw30182step2Labels = mixedMoment B raw30182step3 raw30182step3Labels := by
      have ha : raw30182step3 = raw30182step2 := by apply Matrix.ext; unfold raw30182step3 raw30182step2; decide +kernel
      have hl : raw30182step2Labels = labelEmbedding7 ∘ raw30182step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30182step2 raw30182step2Labels raw30182step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4790 node4790Labels := by rfl

def raw30183 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30183Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30183step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30183step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30183step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30183step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30183 raw30183Labels = mixedMoment B node5063 node5063Labels := by
  calc
    mixedMoment B raw30183 raw30183Labels = mixedMoment B raw30183step0 raw30183step0Labels := by
      have hz : ∀ j, raw30183 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30183step0 = (fun i j => raw30183 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30183step0 raw30183; decide +kernel
      have hl : raw30183step0Labels = raw30183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30183 raw30183Labels permutation346 hz
    mixedMoment B raw30183step0 raw30183step0Labels = mixedMoment B raw30183step1 raw30183step1Labels := by
      have ha : raw30183step1 = (fun i j => raw30183step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30183step1 raw30183step0; decide +kernel
      have hl : raw30183step1Labels = raw30183step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30183step0 raw30183step0Labels permutation32 permutation6
    mixedMoment B raw30183step1 raw30183step1Labels = mixedMoment B raw30183step2 raw30183step2Labels := by
      have ha : raw30183step2 = raw30183step1 := by apply Matrix.ext; unfold raw30183step2 raw30183step1; decide +kernel
      have hl : raw30183step1Labels = labelEmbedding9 ∘ raw30183step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30183step1 raw30183step1Labels raw30183step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5063 node5063Labels := by rfl

def raw30184 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30184step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30184step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30184step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30184step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30184 raw30184Labels = mixedMoment B node5126 node5126Labels := by
  calc
    mixedMoment B raw30184 raw30184Labels = mixedMoment B raw30184step0 raw30184step0Labels := by
      have ha : raw30184step0 = (fun i j => raw30184 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30184step0 raw30184; decide +kernel
      have hl : raw30184step0Labels = raw30184Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30184 raw30184Labels permutation152 permutation6
    mixedMoment B raw30184step0 raw30184step0Labels = mixedMoment B raw30184step1 raw30184step1Labels := by
      have ha : raw30184step1 = raw30184step0 := by apply Matrix.ext; unfold raw30184step1 raw30184step0; decide +kernel
      have hl : raw30184step0Labels = labelEmbedding9 ∘ raw30184step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30184step0 raw30184step0Labels raw30184step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5126 node5126Labels := by rfl

def raw30185 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30185step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw30185step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw30185step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30185 raw30185Labels = mixedMoment B node5125 node5125Labels := by
  calc
    mixedMoment B raw30185 raw30185Labels = mixedMoment B raw30185step0 raw30185step0Labels := by
      have hz : ∀ j, raw30185 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30185step0 = (fun i j => raw30185 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30185step0 raw30185; decide +kernel
      have hl : raw30185step0Labels = raw30185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30185 raw30185Labels permutation346 hz
    mixedMoment B raw30185step0 raw30185step0Labels = mixedMoment B raw30185step1 raw30185step1Labels := by
      have ha : raw30185step1 = (fun i j => raw30185step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30185step1 raw30185step0; decide +kernel
      have hl : raw30185step1Labels = raw30185step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30185step0 raw30185step0Labels permutation32 permutation6
    mixedMoment B raw30185step1 raw30185step1Labels = mixedMoment B raw30185step2 raw30185step2Labels := by
      have ha : raw30185step2 = raw30185step1 := by apply Matrix.ext; unfold raw30185step2 raw30185step1; decide +kernel
      have hl : raw30185step1Labels = labelEmbedding9 ∘ raw30185step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30185step1 raw30185step1Labels raw30185step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5125 node5125Labels := by rfl

def raw30186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw30186Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw30186step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw30186step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30186 raw30186Labels = mixedMoment B node3660 node3660Labels := by
  calc
    mixedMoment B raw30186 raw30186Labels = mixedMoment B raw30186step0 raw30186step0Labels := by
      have hz : ∀ j, raw30186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30186step0 = (fun i j => raw30186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30186step0 raw30186; decide +kernel
      have hl : raw30186step0Labels = raw30186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30186 raw30186Labels permutation346 hz
    mixedMoment B raw30186step0 raw30186step0Labels = mixedMoment B raw30186step1 raw30186step1Labels := by
      have ha : raw30186step1 = (fun i j => raw30186step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30186step1 raw30186step0; decide +kernel
      have hl : raw30186step1Labels = raw30186step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30186step0 raw30186step0Labels permutation127 permutation2
    mixedMoment B raw30186step1 raw30186step1Labels = mixedMoment B raw30186step2 raw30186step2Labels := by
      have ha : raw30186step2 = -raw30186step1 := by apply Matrix.ext; change ∀ i j, raw30186step2 i j = -(raw30186step1 i j); unfold raw30186step2 raw30186step1; decide +kernel
      have hl : raw30186step2Labels = raw30186step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3660 node3660Labels := by rfl

def raw30187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw30187Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw30187step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30187step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30187 raw30187Labels = mixedMoment B node3656 node3656Labels := by
  calc
    mixedMoment B raw30187 raw30187Labels = mixedMoment B raw30187step0 raw30187step0Labels := by
      have ha : raw30187step0 = (fun i j => raw30187 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30187step0 raw30187; decide +kernel
      have hl : raw30187step0Labels = raw30187Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30187 raw30187Labels permutation587 permutation2
    mixedMoment B raw30187step0 raw30187step0Labels = mixedMoment B raw30187step1 raw30187step1Labels := by
      have ha : raw30187step1 = -raw30187step0 := by apply Matrix.ext; change ∀ i j, raw30187step1 i j = -(raw30187step0 i j); unfold raw30187step1 raw30187step0; decide +kernel
      have hl : raw30187step1Labels = raw30187step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3656 node3656Labels := by rfl

def raw30188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw30188Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw30188step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30188step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30188step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30188 raw30188Labels = mixedMoment B node3664 node3664Labels := by
  calc
    mixedMoment B raw30188 raw30188Labels = mixedMoment B raw30188step0 raw30188step0Labels := by
      have hz : ∀ j, raw30188 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30188step0 = (fun i j => raw30188 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30188step0 raw30188; decide +kernel
      have hl : raw30188step0Labels = raw30188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30188 raw30188Labels permutation346 hz
    mixedMoment B raw30188step0 raw30188step0Labels = mixedMoment B raw30188step1 raw30188step1Labels := by
      have ha : raw30188step1 = (fun i j => raw30188step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30188step1 raw30188step0; decide +kernel
      have hl : raw30188step1Labels = raw30188step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30188step0 raw30188step0Labels permutation125 permutation2
    mixedMoment B raw30188step1 raw30188step1Labels = mixedMoment B raw30188step2 raw30188step2Labels := by
      have ha : raw30188step2 = -raw30188step1 := by apply Matrix.ext; change ∀ i j, raw30188step2 i j = -(raw30188step1 i j); unfold raw30188step2 raw30188step1; decide +kernel
      have hl : raw30188step2Labels = raw30188step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3664 node3664Labels := by rfl

def raw30189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw30189Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw30189step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw30189step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30189step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30189 raw30189Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw30189 raw30189Labels = mixedMoment B raw30189step0 raw30189step0Labels := by
      have hz : ∀ j, raw30189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30189step0 = (fun i j => raw30189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30189step0 raw30189; decide +kernel
      have hl : raw30189step0Labels = raw30189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30189 raw30189Labels permutation346 hz
    mixedMoment B raw30189step0 raw30189step0Labels = mixedMoment B raw30189step1 raw30189step1Labels := by
      have ha : raw30189step1 = (fun i j => raw30189step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30189step1 raw30189step0; decide +kernel
      have hl : raw30189step1Labels = raw30189step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30189step0 raw30189step0Labels permutation127 permutation2
    mixedMoment B raw30189step1 raw30189step1Labels = mixedMoment B raw30189step2 raw30189step2Labels := by
      have ha : raw30189step2 = -raw30189step1 := by apply Matrix.ext; change ∀ i j, raw30189step2 i j = -(raw30189step1 i j); unfold raw30189step2 raw30189step1; decide +kernel
      have hl : raw30189step2Labels = raw30189step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3770 node3770Labels := by rfl

def raw30190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw30190Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30190step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30190step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30190 raw30190Labels = mixedMoment B node2370 node2370Labels := by
  calc
    mixedMoment B raw30190 raw30190Labels = mixedMoment B raw30190step0 raw30190step0Labels := by
      have ha : raw30190step0 = (fun i j => raw30190 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30190step0 raw30190; decide +kernel
      have hl : raw30190step0Labels = raw30190Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30190 raw30190Labels permutation200 permutation2
    _ = mixedMoment B node2370 node2370Labels := by rfl

def raw30191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![3, -1, -2], ![2, 0, -2]]
def raw30191Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, -1, 2], ![3, -1, -2], ![2, 0, -2]]
def raw30191step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw30191step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw30191step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30191 raw30191Labels = mixedMoment B node2306 node2306Labels := by
  calc
    mixedMoment B raw30191 raw30191Labels = mixedMoment B raw30191step0 raw30191step0Labels := by
      have hz : ∀ j, raw30191 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30191step0 = (fun i j => raw30191 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30191step0 raw30191; decide +kernel
      have hl : raw30191step0Labels = raw30191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30191 raw30191Labels permutation346 hz
    mixedMoment B raw30191step0 raw30191step0Labels = mixedMoment B raw30191step1 raw30191step1Labels := by
      have ha : raw30191step1 = (fun i j => raw30191step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30191step1 raw30191step0; decide +kernel
      have hl : raw30191step1Labels = raw30191step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30191step0 raw30191step0Labels permutation125 permutation2
    mixedMoment B raw30191step1 raw30191step1Labels = mixedMoment B raw30191step2 raw30191step2Labels := by
      have ha : raw30191step2 = -raw30191step1 := by apply Matrix.ext; change ∀ i j, raw30191step2 i j = -(raw30191step1 i j); unfold raw30191step2 raw30191step1; decide +kernel
      have hl : raw30191step2Labels = raw30191step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2306 node2306Labels := by rfl

def raw30192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw30192Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw30192step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw30192step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw30192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30192 raw30192Labels = mixedMoment B node2306 node2306Labels := by
  calc
    mixedMoment B raw30192 raw30192Labels = mixedMoment B raw30192step0 raw30192step0Labels := by
      have hz : ∀ j, raw30192 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30192step0 = (fun i j => raw30192 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30192step0 raw30192; decide +kernel
      have hl : raw30192step0Labels = raw30192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30192 raw30192Labels permutation346 hz
    mixedMoment B raw30192step0 raw30192step0Labels = mixedMoment B raw30192step1 raw30192step1Labels := by
      have ha : raw30192step1 = (fun i j => raw30192step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30192step1 raw30192step0; decide +kernel
      have hl : raw30192step1Labels = raw30192step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30192step0 raw30192step0Labels permutation149 permutation2
    mixedMoment B raw30192step1 raw30192step1Labels = mixedMoment B raw30192step2 raw30192step2Labels := by
      have ha : raw30192step2 = -raw30192step1 := by apply Matrix.ext; change ∀ i j, raw30192step2 i j = -(raw30192step1 i j); unfold raw30192step2 raw30192step1; decide +kernel
      have hl : raw30192step2Labels = raw30192step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2306 node2306Labels := by rfl

def raw30193 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30193Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30193step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw30193step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30193step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30193 raw30193Labels = mixedMoment B node3372 node3372Labels := by
  calc
    mixedMoment B raw30193 raw30193Labels = mixedMoment B raw30193step0 raw30193step0Labels := by
      have hz : ∀ j, raw30193 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30193step0 = (fun i j => raw30193 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30193step0 raw30193; decide +kernel
      have hl : raw30193step0Labels = raw30193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30193 raw30193Labels permutation346 hz
    mixedMoment B raw30193step0 raw30193step0Labels = mixedMoment B raw30193step1 raw30193step1Labels := by
      have ha : raw30193step1 = (fun i j => raw30193step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30193step1 raw30193step0; decide +kernel
      have hl : raw30193step1Labels = raw30193step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30193step0 raw30193step0Labels permutation38 permutation4
    mixedMoment B raw30193step1 raw30193step1Labels = mixedMoment B raw30193step2 raw30193step2Labels := by
      have ha : raw30193step2 = -raw30193step1 := by apply Matrix.ext; change ∀ i j, raw30193step2 i j = -(raw30193step1 i j); unfold raw30193step2 raw30193step1; decide +kernel
      have hl : raw30193step2Labels = raw30193step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3372 node3372Labels := by rfl

def raw30194 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30194Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30194step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 2, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw30194step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30194 raw30194Labels = mixedMoment B node1800 node1800Labels := by
  calc
    mixedMoment B raw30194 raw30194Labels = mixedMoment B raw30194step0 raw30194step0Labels := by
      have hz : ∀ j, raw30194 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30194step0 = (fun i j => raw30194 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30194step0 raw30194; decide +kernel
      have hl : raw30194step0Labels = raw30194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30194 raw30194Labels permutation346 hz
    mixedMoment B raw30194step0 raw30194step0Labels = mixedMoment B raw30194step1 raw30194step1Labels := by
      have ha : raw30194step1 = (fun i j => raw30194step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30194step1 raw30194step0; decide +kernel
      have hl : raw30194step1Labels = raw30194step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30194step0 raw30194step0Labels permutation38 permutation4
    mixedMoment B raw30194step1 raw30194step1Labels = mixedMoment B raw30194step2 raw30194step2Labels := by
      have ha : raw30194step2 = -raw30194step1 := by apply Matrix.ext; change ∀ i j, raw30194step2 i j = -(raw30194step1 i j); unfold raw30194step2 raw30194step1; decide +kernel
      have hl : raw30194step2Labels = raw30194step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1800 node1800Labels := by rfl

def raw30195 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30195Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30195step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw30195step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30195step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30195step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30195 raw30195Labels = mixedMoment B node1785 node1785Labels := by
  calc
    mixedMoment B raw30195 raw30195Labels = mixedMoment B raw30195step0 raw30195step0Labels := by
      have ha : raw30195step0 = (fun i j => raw30195 (permutation200 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30195step0 raw30195; decide +kernel
      have hl : raw30195step0Labels = raw30195Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30195 raw30195Labels permutation200 permutation4
    mixedMoment B raw30195step0 raw30195step0Labels = mixedMoment B raw30195step1 raw30195step1Labels := by
      have ha : raw30195step1 = -raw30195step0 := by apply Matrix.ext; change ∀ i j, raw30195step1 i j = -(raw30195step0 i j); unfold raw30195step1 raw30195step0; decide +kernel
      have hl : raw30195step1Labels = raw30195step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1785 node1785Labels := by rfl

def raw30196 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30196Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30196step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw30196step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30196step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30196step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30196 raw30196Labels = mixedMoment B node2007 node2007Labels := by
  calc
    mixedMoment B raw30196 raw30196Labels = mixedMoment B raw30196step0 raw30196step0Labels := by
      have hz : ∀ j, raw30196 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30196step0 = (fun i j => raw30196 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30196step0 raw30196; decide +kernel
      have hl : raw30196step0Labels = raw30196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30196 raw30196Labels permutation346 hz
    mixedMoment B raw30196step0 raw30196step0Labels = mixedMoment B raw30196step1 raw30196step1Labels := by
      have ha : raw30196step1 = (fun i j => raw30196step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30196step1 raw30196step0; decide +kernel
      have hl : raw30196step1Labels = raw30196step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30196step0 raw30196step0Labels permutation38 permutation4
    mixedMoment B raw30196step1 raw30196step1Labels = mixedMoment B raw30196step2 raw30196step2Labels := by
      have ha : raw30196step2 = -raw30196step1 := by apply Matrix.ext; change ∀ i j, raw30196step2 i j = -(raw30196step1 i j); unfold raw30196step2 raw30196step1; decide +kernel
      have hl : raw30196step2Labels = raw30196step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2007 node2007Labels := by rfl

def raw30197 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![1, -3, 2], ![0, -2, 2]]
def raw30197Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-2, 2, 0], ![1, -3, 2], ![0, -2, 2]]
def raw30197step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 1, 2]]
def raw30197step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30197step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30197 raw30197Labels = mixedMoment B node1788 node1788Labels := by
  calc
    mixedMoment B raw30197 raw30197Labels = mixedMoment B raw30197step0 raw30197step0Labels := by
      have hz : ∀ j, raw30197 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30197step0 = (fun i j => raw30197 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30197step0 raw30197; decide +kernel
      have hl : raw30197step0Labels = raw30197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30197 raw30197Labels permutation346 hz
    mixedMoment B raw30197step0 raw30197step0Labels = mixedMoment B raw30197step1 raw30197step1Labels := by
      have ha : raw30197step1 = (fun i j => raw30197step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30197step1 raw30197step0; decide +kernel
      have hl : raw30197step1Labels = raw30197step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30197step0 raw30197step0Labels permutation39 permutation4
    mixedMoment B raw30197step1 raw30197step1Labels = mixedMoment B raw30197step2 raw30197step2Labels := by
      have ha : raw30197step2 = -raw30197step1 := by apply Matrix.ext; change ∀ i j, raw30197step2 i j = -(raw30197step1 i j); unfold raw30197step2 raw30197step1; decide +kernel
      have hl : raw30197step2Labels = raw30197step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1788 node1788Labels := by rfl

def raw30198 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![1, -3, 2]]
def raw30198Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-2, 2, 0], ![0, -2, 2], ![1, -3, 2]]
def raw30198step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 1, 2]]
def raw30198step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30198step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30198 raw30198Labels = mixedMoment B node1788 node1788Labels := by
  calc
    mixedMoment B raw30198 raw30198Labels = mixedMoment B raw30198step0 raw30198step0Labels := by
      have hz : ∀ j, raw30198 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30198step0 = (fun i j => raw30198 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30198step0 raw30198; decide +kernel
      have hl : raw30198step0Labels = raw30198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30198 raw30198Labels permutation346 hz
    mixedMoment B raw30198step0 raw30198step0Labels = mixedMoment B raw30198step1 raw30198step1Labels := by
      have ha : raw30198step1 = (fun i j => raw30198step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30198step1 raw30198step0; decide +kernel
      have hl : raw30198step1Labels = raw30198step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30198step0 raw30198step0Labels permutation38 permutation4
    mixedMoment B raw30198step1 raw30198step1Labels = mixedMoment B raw30198step2 raw30198step2Labels := by
      have ha : raw30198step2 = -raw30198step1 := by apply Matrix.ext; change ∀ i j, raw30198step2 i j = -(raw30198step1 i j); unfold raw30198step2 raw30198step1; decide +kernel
      have hl : raw30198step2Labels = raw30198step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1788 node1788Labels := by rfl

def raw30199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30199Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw30199step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30199step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30199step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30199 raw30199Labels = mixedMoment B node3646 node3646Labels := by
  calc
    mixedMoment B raw30199 raw30199Labels = mixedMoment B raw30199step0 raw30199step0Labels := by
      have ha : raw30199step0 = (fun i j => raw30199 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30199step0 raw30199; decide +kernel
      have hl : raw30199step0Labels = raw30199Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30199 raw30199Labels permutation584 permutation2
    mixedMoment B raw30199step0 raw30199step0Labels = mixedMoment B raw30199step1 raw30199step1Labels := by
      have ha : raw30199step1 = -raw30199step0 := by apply Matrix.ext; change ∀ i j, raw30199step1 i j = -(raw30199step0 i j); unfold raw30199step1 raw30199step0; decide +kernel
      have hl : raw30199step1Labels = raw30199step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3646 node3646Labels := by rfl

def raw30200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw30200step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30200step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30200step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30200 raw30200Labels = mixedMoment B node3650 node3650Labels := by
  calc
    mixedMoment B raw30200 raw30200Labels = mixedMoment B raw30200step0 raw30200step0Labels := by
      have ha : raw30200step0 = (fun i j => raw30200 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30200step0 raw30200; decide +kernel
      have hl : raw30200step0Labels = raw30200Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30200 raw30200Labels permutation587 permutation2
    mixedMoment B raw30200step0 raw30200step0Labels = mixedMoment B raw30200step1 raw30200step1Labels := by
      have ha : raw30200step1 = -raw30200step0 := by apply Matrix.ext; change ∀ i j, raw30200step1 i j = -(raw30200step0 i j); unfold raw30200step1 raw30200step0; decide +kernel
      have hl : raw30200step1Labels = raw30200step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3650 node3650Labels := by rfl

def raw30201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw30201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30201step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30201step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30201 raw30201Labels = mixedMoment B node3650 node3650Labels := by
  calc
    mixedMoment B raw30201 raw30201Labels = mixedMoment B raw30201step0 raw30201step0Labels := by
      have ha : raw30201step0 = (fun i j => raw30201 (permutation582 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30201step0 raw30201; decide +kernel
      have hl : raw30201step0Labels = raw30201Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30201 raw30201Labels permutation582 permutation2
    mixedMoment B raw30201step0 raw30201step0Labels = mixedMoment B raw30201step1 raw30201step1Labels := by
      have ha : raw30201step1 = -raw30201step0 := by apply Matrix.ext; change ∀ i j, raw30201step1 i j = -(raw30201step0 i j); unfold raw30201step1 raw30201step0; decide +kernel
      have hl : raw30201step1Labels = raw30201step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3650 node3650Labels := by rfl

def raw30202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw30202Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw30202step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30202step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw30202step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30202 raw30202Labels = mixedMoment B node3757 node3757Labels := by
  calc
    mixedMoment B raw30202 raw30202Labels = mixedMoment B raw30202step0 raw30202step0Labels := by
      have ha : raw30202step0 = (fun i j => raw30202 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30202step0 raw30202; decide +kernel
      have hl : raw30202step0Labels = raw30202Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30202 raw30202Labels permutation584 permutation2
    mixedMoment B raw30202step0 raw30202step0Labels = mixedMoment B raw30202step1 raw30202step1Labels := by
      have ha : raw30202step1 = -raw30202step0 := by apply Matrix.ext; change ∀ i j, raw30202step1 i j = -(raw30202step0 i j); unfold raw30202step1 raw30202step0; decide +kernel
      have hl : raw30202step1Labels = raw30202step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3757 node3757Labels := by rfl

def raw30203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30203step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30203 raw30203Labels = mixedMoment B node2424 node2424Labels := by
  calc
    mixedMoment B raw30203 raw30203Labels = mixedMoment B raw30203step0 raw30203step0Labels := by
      have ha : raw30203step0 = (fun i j => raw30203 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30203step0 raw30203; decide +kernel
      have hl : raw30203step0Labels = raw30203Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30203 raw30203Labels permutation176 permutation2
    _ = mixedMoment B node2424 node2424Labels := by rfl

def raw30204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw30204Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30204step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30204step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30204step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30204 raw30204Labels = mixedMoment B node2295 node2295Labels := by
  calc
    mixedMoment B raw30204 raw30204Labels = mixedMoment B raw30204step0 raw30204step0Labels := by
      have ha : raw30204step0 = (fun i j => raw30204 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30204step0 raw30204; decide +kernel
      have hl : raw30204step0Labels = raw30204Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30204 raw30204Labels permutation587 permutation2
    mixedMoment B raw30204step0 raw30204step0Labels = mixedMoment B raw30204step1 raw30204step1Labels := by
      have ha : raw30204step1 = -raw30204step0 := by apply Matrix.ext; change ∀ i j, raw30204step1 i j = -(raw30204step0 i j); unfold raw30204step1 raw30204step0; decide +kernel
      have hl : raw30204step1Labels = raw30204step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2295 node2295Labels := by rfl

def raw30205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30205step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30205step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30205step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30205 raw30205Labels = mixedMoment B node2295 node2295Labels := by
  calc
    mixedMoment B raw30205 raw30205Labels = mixedMoment B raw30205step0 raw30205step0Labels := by
      have ha : raw30205step0 = (fun i j => raw30205 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30205step0 raw30205; decide +kernel
      have hl : raw30205step0Labels = raw30205Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30205 raw30205Labels permutation686 permutation2
    mixedMoment B raw30205step0 raw30205step0Labels = mixedMoment B raw30205step1 raw30205step1Labels := by
      have ha : raw30205step1 = -raw30205step0 := by apply Matrix.ext; change ∀ i j, raw30205step1 i j = -(raw30205step0 i j); unfold raw30205step1 raw30205step0; decide +kernel
      have hl : raw30205step1Labels = raw30205step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2295 node2295Labels := by rfl

def raw30206 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw30206step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30206step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30206step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30206 raw30206Labels = mixedMoment B node3487 node3487Labels := by
  calc
    mixedMoment B raw30206 raw30206Labels = mixedMoment B raw30206step0 raw30206step0Labels := by
      have ha : raw30206step0 = (fun i j => raw30206 (permutation182 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30206step0 raw30206; decide +kernel
      have hl : raw30206step0Labels = raw30206Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30206 raw30206Labels permutation182 permutation4
    mixedMoment B raw30206step0 raw30206step0Labels = mixedMoment B raw30206step1 raw30206step1Labels := by
      have ha : raw30206step1 = -raw30206step0 := by apply Matrix.ext; change ∀ i j, raw30206step1 i j = -(raw30206step0 i j); unfold raw30206step1 raw30206step0; decide +kernel
      have hl : raw30206step1Labels = raw30206step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3487 node3487Labels := by rfl

def raw30207 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw30207step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30207step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30207step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30207 raw30207Labels = mixedMoment B node1958 node1958Labels := by
  calc
    mixedMoment B raw30207 raw30207Labels = mixedMoment B raw30207step0 raw30207step0Labels := by
      have ha : raw30207step0 = (fun i j => raw30207 (permutation182 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30207step0 raw30207; decide +kernel
      have hl : raw30207step0Labels = raw30207Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30207 raw30207Labels permutation182 permutation4
    mixedMoment B raw30207step0 raw30207step0Labels = mixedMoment B raw30207step1 raw30207step1Labels := by
      have ha : raw30207step1 = -raw30207step0 := by apply Matrix.ext; change ∀ i j, raw30207step1 i j = -(raw30207step0 i j); unfold raw30207step1 raw30207step0; decide +kernel
      have hl : raw30207step1Labels = raw30207step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1958 node1958Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
