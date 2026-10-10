import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw28160 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw28160Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw28160step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28160 raw28160Labels = mixedMoment B node2544 node2544Labels := by
  calc
    mixedMoment B raw28160 raw28160Labels = mixedMoment B raw28160step0 raw28160step0Labels := by
      have ha : raw28160step0 = (fun i j => raw28160 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28160step0 raw28160; decide +kernel
      have hl : raw28160step0Labels = raw28160Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28160 raw28160Labels permutation152 permutation6
    _ = mixedMoment B node2544 node2544Labels := by rfl

def raw28161 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw28161Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw28161step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28161step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -2, 1], ![-3, 0, 3]]
def raw28161step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28161step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw28161step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28161 raw28161Labels = mixedMoment B node2602 node2602Labels := by
  calc
    mixedMoment B raw28161 raw28161Labels = mixedMoment B raw28161step0 raw28161step0Labels := by
      have hz : ∀ j, raw28161 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28161step0 = (fun i j => raw28161 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28161step0 raw28161; decide +kernel
      have hl : raw28161step0Labels = raw28161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28161 raw28161Labels permutation434 hz
    mixedMoment B raw28161step0 raw28161step0Labels = mixedMoment B raw28161step1 raw28161step1Labels := by
      have hz : ∀ j, raw28161step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28161step1 = (fun i j => raw28161step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28161step1 raw28161step0; decide +kernel
      have hl : raw28161step1Labels = raw28161step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28161step0 raw28161step0Labels permutation80 hz
    mixedMoment B raw28161step1 raw28161step1Labels = mixedMoment B raw28161step2 raw28161step2Labels := by
      have ha : raw28161step2 = (fun i j => raw28161step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28161step2 raw28161step1; decide +kernel
      have hl : raw28161step2Labels = raw28161step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28161step1 raw28161step1Labels permutation8 permutation6
    _ = mixedMoment B node2602 node2602Labels := by rfl

def raw28162 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw28162Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-4, 1, 3]]
def raw28162step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw28162step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28162 raw28162Labels = mixedMoment B node1433 node1433Labels := by
  calc
    mixedMoment B raw28162 raw28162Labels = mixedMoment B raw28162step0 raw28162step0Labels := by
      have hz : ∀ j, raw28162 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28162step0 = (fun i j => raw28162 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28162step0 raw28162; decide +kernel
      have hl : raw28162step0Labels = raw28162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28162 raw28162Labels permutation346 hz
    mixedMoment B raw28162step0 raw28162step0Labels = mixedMoment B raw28162step1 raw28162step1Labels := by
      have ha : raw28162step1 = (fun i j => raw28162step0 (permutation128 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28162step1 raw28162step0; decide +kernel
      have hl : raw28162step1Labels = raw28162step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28162step0 raw28162step0Labels permutation128 permutation3
    _ = mixedMoment B node1433 node1433Labels := by rfl

def raw28163 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw28163Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw28163step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28163step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28163 raw28163Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw28163 raw28163Labels = mixedMoment B raw28163step0 raw28163step0Labels := by
      have hz : ∀ j, raw28163 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28163step0 = (fun i j => raw28163 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28163step0 raw28163; decide +kernel
      have hl : raw28163step0Labels = raw28163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28163 raw28163Labels permutation346 hz
    mixedMoment B raw28163step0 raw28163step0Labels = mixedMoment B raw28163step1 raw28163step1Labels := by
      have ha : raw28163step1 = (fun i j => raw28163step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28163step1 raw28163step0; decide +kernel
      have hl : raw28163step1Labels = raw28163step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28163step0 raw28163step0Labels permutation32 permutation6
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw28164 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw28164Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw28164step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28164step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28164 raw28164Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw28164 raw28164Labels = mixedMoment B raw28164step0 raw28164step0Labels := by
      have hz : ∀ j, raw28164 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28164step0 = (fun i j => raw28164 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28164step0 raw28164; decide +kernel
      have hl : raw28164step0Labels = raw28164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28164 raw28164Labels permutation346 hz
    mixedMoment B raw28164step0 raw28164step0Labels = mixedMoment B raw28164step1 raw28164step1Labels := by
      have ha : raw28164step1 = (fun i j => raw28164step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28164step1 raw28164step0; decide +kernel
      have hl : raw28164step1Labels = raw28164step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28164step0 raw28164step0Labels permutation32 permutation6
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw28165 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw28165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28165step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28165step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28165 raw28165Labels = mixedMoment B node2543 node2543Labels := by
  calc
    mixedMoment B raw28165 raw28165Labels = mixedMoment B raw28165step0 raw28165step0Labels := by
      have ha : raw28165step0 = (fun i j => raw28165 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28165step0 raw28165; decide +kernel
      have hl : raw28165step0Labels = raw28165Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28165 raw28165Labels permutation152 permutation6
    _ = mixedMoment B node2543 node2543Labels := by rfl

def raw28166 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw28166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw28166step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -1, 1], ![-2, -1, 3]]
def raw28166step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28166step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28166 raw28166Labels = mixedMoment B node2601 node2601Labels := by
  calc
    mixedMoment B raw28166 raw28166Labels = mixedMoment B raw28166step0 raw28166step0Labels := by
      have hz : ∀ j, raw28166 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28166step0 = (fun i j => raw28166 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28166step0 raw28166; decide +kernel
      have hl : raw28166step0Labels = raw28166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28166 raw28166Labels permutation434 hz
    mixedMoment B raw28166step0 raw28166step0Labels = mixedMoment B raw28166step1 raw28166step1Labels := by
      have hz : ∀ j, raw28166step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28166step1 = (fun i j => raw28166step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28166step1 raw28166step0; decide +kernel
      have hl : raw28166step1Labels = raw28166step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28166step0 raw28166step0Labels permutation80 hz
    mixedMoment B raw28166step1 raw28166step1Labels = mixedMoment B raw28166step2 raw28166step2Labels := by
      have ha : raw28166step2 = (fun i j => raw28166step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28166step2 raw28166step1; decide +kernel
      have hl : raw28166step2Labels = raw28166step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28166step1 raw28166step1Labels permutation8 permutation6
    _ = mixedMoment B node2601 node2601Labels := by rfl

def raw28167 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw28167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw28167step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28167 raw28167Labels = mixedMoment B node2572 node2572Labels := by
  calc
    mixedMoment B raw28167 raw28167Labels = mixedMoment B raw28167step0 raw28167step0Labels := by
      have hz : ∀ j, raw28167 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28167step0 = (fun i j => raw28167 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28167step0 raw28167; decide +kernel
      have hl : raw28167step0Labels = raw28167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28167 raw28167Labels permutation346 hz
    mixedMoment B raw28167step0 raw28167step0Labels = mixedMoment B raw28167step1 raw28167step1Labels := by
      have ha : raw28167step1 = (fun i j => raw28167step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw28167step1 raw28167step0; decide +kernel
      have hl : raw28167step1Labels = raw28167step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28167step0 raw28167step0Labels permutation32 permutation6
    _ = mixedMoment B node2572 node2572Labels := by rfl

def raw28168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw28168Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw28168step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw28168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw28168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28168 raw28168Labels = mixedMoment B node2393 node2393Labels := by
  calc
    mixedMoment B raw28168 raw28168Labels = mixedMoment B raw28168step0 raw28168step0Labels := by
      have hz : ∀ j, raw28168 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28168step0 = (fun i j => raw28168 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28168step0 raw28168; decide +kernel
      have hl : raw28168step0Labels = raw28168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28168 raw28168Labels permutation346 hz
    mixedMoment B raw28168step0 raw28168step0Labels = mixedMoment B raw28168step1 raw28168step1Labels := by
      have ha : raw28168step1 = (fun i j => raw28168step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28168step1 raw28168step0; decide +kernel
      have hl : raw28168step1Labels = raw28168step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28168step0 raw28168step0Labels permutation151 permutation2
    mixedMoment B raw28168step1 raw28168step1Labels = mixedMoment B raw28168step2 raw28168step2Labels := by
      have ha : raw28168step2 = -raw28168step1 := by apply Matrix.ext; change ∀ i j, raw28168step2 i j = -(raw28168step1 i j); unfold raw28168step2 raw28168step1; decide +kernel
      have hl : raw28168step2Labels = raw28168step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2393 node2393Labels := by rfl

def raw28169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw28169Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw28169step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw28169step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw28169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28169 raw28169Labels = mixedMoment B node2395 node2395Labels := by
  calc
    mixedMoment B raw28169 raw28169Labels = mixedMoment B raw28169step0 raw28169step0Labels := by
      have hz : ∀ j, raw28169 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28169step0 = (fun i j => raw28169 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28169step0 raw28169; decide +kernel
      have hl : raw28169step0Labels = raw28169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28169 raw28169Labels permutation346 hz
    mixedMoment B raw28169step0 raw28169step0Labels = mixedMoment B raw28169step1 raw28169step1Labels := by
      have ha : raw28169step1 = (fun i j => raw28169step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28169step1 raw28169step0; decide +kernel
      have hl : raw28169step1Labels = raw28169step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28169step0 raw28169step0Labels permutation150 permutation2
    mixedMoment B raw28169step1 raw28169step1Labels = mixedMoment B raw28169step2 raw28169step2Labels := by
      have ha : raw28169step2 = -raw28169step1 := by apply Matrix.ext; change ∀ i j, raw28169step2 i j = -(raw28169step1 i j); unfold raw28169step2 raw28169step1; decide +kernel
      have hl : raw28169step2Labels = raw28169step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2395 node2395Labels := by rfl

def raw28170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw28170Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28170step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw28170step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28170step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw28170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28170 raw28170Labels = mixedMoment B node2390 node2390Labels := by
  calc
    mixedMoment B raw28170 raw28170Labels = mixedMoment B raw28170step0 raw28170step0Labels := by
      have ha : raw28170step0 = (fun i j => raw28170 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28170step0 raw28170; decide +kernel
      have hl : raw28170step0Labels = raw28170Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28170 raw28170Labels permutation688 permutation2
    mixedMoment B raw28170step0 raw28170step0Labels = mixedMoment B raw28170step1 raw28170step1Labels := by
      have ha : raw28170step1 = -raw28170step0 := by apply Matrix.ext; change ∀ i j, raw28170step1 i j = -(raw28170step0 i j); unfold raw28170step1 raw28170step0; decide +kernel
      have hl : raw28170step1Labels = raw28170step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2390 node2390Labels := by rfl

def raw28171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw28171Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw28171step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw28171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28171step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw28171step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28171 raw28171Labels = mixedMoment B node2404 node2404Labels := by
  calc
    mixedMoment B raw28171 raw28171Labels = mixedMoment B raw28171step0 raw28171step0Labels := by
      have hz : ∀ j, raw28171 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28171step0 = (fun i j => raw28171 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28171step0 raw28171; decide +kernel
      have hl : raw28171step0Labels = raw28171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28171 raw28171Labels permutation346 hz
    mixedMoment B raw28171step0 raw28171step0Labels = mixedMoment B raw28171step1 raw28171step1Labels := by
      have ha : raw28171step1 = (fun i j => raw28171step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28171step1 raw28171step0; decide +kernel
      have hl : raw28171step1Labels = raw28171step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28171step0 raw28171step0Labels permutation149 permutation2
    mixedMoment B raw28171step1 raw28171step1Labels = mixedMoment B raw28171step2 raw28171step2Labels := by
      have ha : raw28171step2 = -raw28171step1 := by apply Matrix.ext; change ∀ i j, raw28171step2 i j = -(raw28171step1 i j); unfold raw28171step2 raw28171step1; decide +kernel
      have hl : raw28171step2Labels = raw28171step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2404 node2404Labels := by rfl

def raw28172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw28172Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw28172step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw28172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28172step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw28172step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28172 raw28172Labels = mixedMoment B node2678 node2678Labels := by
  calc
    mixedMoment B raw28172 raw28172Labels = mixedMoment B raw28172step0 raw28172step0Labels := by
      have hz : ∀ j, raw28172 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28172step0 = (fun i j => raw28172 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28172step0 raw28172; decide +kernel
      have hl : raw28172step0Labels = raw28172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28172 raw28172Labels permutation346 hz
    mixedMoment B raw28172step0 raw28172step0Labels = mixedMoment B raw28172step1 raw28172step1Labels := by
      have ha : raw28172step1 = (fun i j => raw28172step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28172step1 raw28172step0; decide +kernel
      have hl : raw28172step1Labels = raw28172step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28172step0 raw28172step0Labels permutation151 permutation2
    mixedMoment B raw28172step1 raw28172step1Labels = mixedMoment B raw28172step2 raw28172step2Labels := by
      have ha : raw28172step2 = -raw28172step1 := by apply Matrix.ext; change ∀ i j, raw28172step2 i j = -(raw28172step1 i j); unfold raw28172step2 raw28172step1; decide +kernel
      have hl : raw28172step2Labels = raw28172step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2678 node2678Labels := by rfl

def raw28173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw28173Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw28173step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw28173step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28173step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw28173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28173 raw28173Labels = mixedMoment B node3771 node3771Labels := by
  calc
    mixedMoment B raw28173 raw28173Labels = mixedMoment B raw28173step0 raw28173step0Labels := by
      have hz : ∀ j, raw28173 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28173step0 = (fun i j => raw28173 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28173step0 raw28173; decide +kernel
      have hl : raw28173step0Labels = raw28173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28173 raw28173Labels permutation346 hz
    mixedMoment B raw28173step0 raw28173step0Labels = mixedMoment B raw28173step1 raw28173step1Labels := by
      have ha : raw28173step1 = (fun i j => raw28173step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28173step1 raw28173step0; decide +kernel
      have hl : raw28173step1Labels = raw28173step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28173step0 raw28173step0Labels permutation151 permutation2
    mixedMoment B raw28173step1 raw28173step1Labels = mixedMoment B raw28173step2 raw28173step2Labels := by
      have ha : raw28173step2 = -raw28173step1 := by apply Matrix.ext; change ∀ i j, raw28173step2 i j = -(raw28173step1 i j); unfold raw28173step2 raw28173step1; decide +kernel
      have hl : raw28173step2Labels = raw28173step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3771 node3771Labels := by rfl

def raw28174 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![-2, 2], ![2, -2], ![2, -2]]
def raw28174Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28174step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![2, -2], ![2, -2]]
def raw28174step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28174step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw28174step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28174step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw28174step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical28174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28174 raw28174Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw28174 raw28174Labels = mixedMoment B raw28174step0 raw28174step0Labels := by
      have hz : ∀ j, raw28174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28174step0 = (fun i j => raw28174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28174step0 raw28174; decide +kernel
      have hl : raw28174step0Labels = raw28174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28174 raw28174Labels permutation346 hz
    mixedMoment B raw28174step0 raw28174step0Labels = mixedMoment B raw28174step1 raw28174step1Labels := by
      have ha : raw28174step1 = (fun i j => raw28174step0 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw28174step1 raw28174step0; decide +kernel
      have hl : raw28174step1Labels = raw28174step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28174step0 raw28174step0Labels permutation122 permutation0
    mixedMoment B raw28174step1 raw28174step1Labels = mixedMoment B raw28174step2 raw28174step2Labels := by
      have ha : raw28174step2 = -raw28174step1 := by apply Matrix.ext; change ∀ i j, raw28174step2 i j = -(raw28174step1 i j); unfold raw28174step2 raw28174step1; decide +kernel
      have hl : raw28174step2Labels = raw28174step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw28175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw28175Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw28175step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28175 raw28175Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw28175 raw28175Labels = mixedMoment B raw28175step0 raw28175step0Labels := by
      have hz : ∀ j, raw28175 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28175step0 = (fun i j => raw28175 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28175step0 raw28175; decide +kernel
      have hl : raw28175step0Labels = raw28175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28175 raw28175Labels permutation346 hz
    mixedMoment B raw28175step0 raw28175step0Labels = mixedMoment B raw28175step1 raw28175step1Labels := by
      have ha : raw28175step1 = (fun i j => raw28175step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28175step1 raw28175step0; decide +kernel
      have hl : raw28175step1Labels = raw28175step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28175step0 raw28175step0Labels permutation38 permutation2
    _ = mixedMoment B node3025 node3025Labels := by rfl

def raw28176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw28176Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw28176step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28176 raw28176Labels = mixedMoment B node2907 node2907Labels := by
  calc
    mixedMoment B raw28176 raw28176Labels = mixedMoment B raw28176step0 raw28176step0Labels := by
      have ha : raw28176step0 = (fun i j => raw28176 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28176step0 raw28176; decide +kernel
      have hl : raw28176step0Labels = raw28176Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28176 raw28176Labels permutation158 permutation2
    _ = mixedMoment B node2907 node2907Labels := by rfl

def raw28177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw28177Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw28177step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw28177step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28177 raw28177Labels = mixedMoment B node2733 node2733Labels := by
  calc
    mixedMoment B raw28177 raw28177Labels = mixedMoment B raw28177step0 raw28177step0Labels := by
      have hz : ∀ j, raw28177 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28177step0 = (fun i j => raw28177 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28177step0 raw28177; decide +kernel
      have hl : raw28177step0Labels = raw28177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28177 raw28177Labels permutation346 hz
    mixedMoment B raw28177step0 raw28177step0Labels = mixedMoment B raw28177step1 raw28177step1Labels := by
      have ha : raw28177step1 = (fun i j => raw28177step0 (permutation91 i) (permutation4 j)) := by apply Matrix.ext; unfold raw28177step1 raw28177step0; decide +kernel
      have hl : raw28177step1Labels = raw28177step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28177step0 raw28177step0Labels permutation91 permutation4
    _ = mixedMoment B node2733 node2733Labels := by rfl

def raw28178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw28178Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw28178step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28178 raw28178Labels = mixedMoment B node2911 node2911Labels := by
  calc
    mixedMoment B raw28178 raw28178Labels = mixedMoment B raw28178step0 raw28178step0Labels := by
      have hz : ∀ j, raw28178 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28178step0 = (fun i j => raw28178 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28178step0 raw28178; decide +kernel
      have hl : raw28178step0Labels = raw28178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28178 raw28178Labels permutation346 hz
    _ = mixedMoment B node2911 node2911Labels := by rfl

def raw28179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw28179Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw28179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw28179step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28179step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw28179step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28179 raw28179Labels = mixedMoment B node1947 node1947Labels := by
  calc
    mixedMoment B raw28179 raw28179Labels = mixedMoment B raw28179step0 raw28179step0Labels := by
      have hz : ∀ j, raw28179 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28179step0 = (fun i j => raw28179 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28179step0 raw28179; decide +kernel
      have hl : raw28179step0Labels = raw28179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28179 raw28179Labels permutation346 hz
    mixedMoment B raw28179step0 raw28179step0Labels = mixedMoment B raw28179step1 raw28179step1Labels := by
      have ha : raw28179step1 = (fun i j => raw28179step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28179step1 raw28179step0; decide +kernel
      have hl : raw28179step1Labels = raw28179step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28179step0 raw28179step0Labels permutation149 permutation2
    mixedMoment B raw28179step1 raw28179step1Labels = mixedMoment B raw28179step2 raw28179step2Labels := by
      have ha : raw28179step2 = -raw28179step1 := by apply Matrix.ext; change ∀ i j, raw28179step2 i j = -(raw28179step1 i j); unfold raw28179step2 raw28179step1; decide +kernel
      have hl : raw28179step2Labels = raw28179step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1947 node1947Labels := by rfl

def raw28180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw28180Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw28180step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28180step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28180 raw28180Labels = mixedMoment B node1915 node1915Labels := by
  calc
    mixedMoment B raw28180 raw28180Labels = mixedMoment B raw28180step0 raw28180step0Labels := by
      have hz : ∀ j, raw28180 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28180step0 = (fun i j => raw28180 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28180step0 raw28180; decide +kernel
      have hl : raw28180step0Labels = raw28180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28180 raw28180Labels permutation346 hz
    mixedMoment B raw28180step0 raw28180step0Labels = mixedMoment B raw28180step1 raw28180step1Labels := by
      have ha : raw28180step1 = (fun i j => raw28180step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28180step1 raw28180step0; decide +kernel
      have hl : raw28180step1Labels = raw28180step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28180step0 raw28180step0Labels permutation149 permutation2
    mixedMoment B raw28180step1 raw28180step1Labels = mixedMoment B raw28180step2 raw28180step2Labels := by
      have ha : raw28180step2 = -raw28180step1 := by apply Matrix.ext; change ∀ i j, raw28180step2 i j = -(raw28180step1 i j); unfold raw28180step2 raw28180step1; decide +kernel
      have hl : raw28180step2Labels = raw28180step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1915 node1915Labels := by rfl

def raw28181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw28181Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28181step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28181step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28181 raw28181Labels = mixedMoment B node1867 node1867Labels := by
  calc
    mixedMoment B raw28181 raw28181Labels = mixedMoment B raw28181step0 raw28181step0Labels := by
      have ha : raw28181step0 = (fun i j => raw28181 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28181step0 raw28181; decide +kernel
      have hl : raw28181step0Labels = raw28181Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28181 raw28181Labels permutation680 permutation2
    mixedMoment B raw28181step0 raw28181step0Labels = mixedMoment B raw28181step1 raw28181step1Labels := by
      have ha : raw28181step1 = -raw28181step0 := by apply Matrix.ext; change ∀ i j, raw28181step1 i j = -(raw28181step0 i j); unfold raw28181step1 raw28181step0; decide +kernel
      have hl : raw28181step1Labels = raw28181step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1867 node1867Labels := by rfl

def raw28182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw28182Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw28182step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw28182step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28182step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw28182step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28182 raw28182Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw28182 raw28182Labels = mixedMoment B raw28182step0 raw28182step0Labels := by
      have hz : ∀ j, raw28182 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28182step0 = (fun i j => raw28182 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28182step0 raw28182; decide +kernel
      have hl : raw28182step0Labels = raw28182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28182 raw28182Labels permutation346 hz
    mixedMoment B raw28182step0 raw28182step0Labels = mixedMoment B raw28182step1 raw28182step1Labels := by
      have ha : raw28182step1 = (fun i j => raw28182step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28182step1 raw28182step0; decide +kernel
      have hl : raw28182step1Labels = raw28182step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28182step0 raw28182step0Labels permutation151 permutation2
    mixedMoment B raw28182step1 raw28182step1Labels = mixedMoment B raw28182step2 raw28182step2Labels := by
      have ha : raw28182step2 = -raw28182step1 := by apply Matrix.ext; change ∀ i j, raw28182step2 i j = -(raw28182step1 i j); unfold raw28182step2 raw28182step1; decide +kernel
      have hl : raw28182step2Labels = raw28182step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1926 node1926Labels := by rfl

def raw28183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw28183Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw28183step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28183step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28183step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28183 raw28183Labels = mixedMoment B node1778 node1778Labels := by
  calc
    mixedMoment B raw28183 raw28183Labels = mixedMoment B raw28183step0 raw28183step0Labels := by
      have hz : ∀ j, raw28183 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28183step0 = (fun i j => raw28183 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28183step0 raw28183; decide +kernel
      have hl : raw28183step0Labels = raw28183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28183 raw28183Labels permutation346 hz
    mixedMoment B raw28183step0 raw28183step0Labels = mixedMoment B raw28183step1 raw28183step1Labels := by
      have ha : raw28183step1 = (fun i j => raw28183step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28183step1 raw28183step0; decide +kernel
      have hl : raw28183step1Labels = raw28183step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28183step0 raw28183step0Labels permutation149 permutation2
    mixedMoment B raw28183step1 raw28183step1Labels = mixedMoment B raw28183step2 raw28183step2Labels := by
      have ha : raw28183step2 = -raw28183step1 := by apply Matrix.ext; change ∀ i j, raw28183step2 i j = -(raw28183step1 i j); unfold raw28183step2 raw28183step1; decide +kernel
      have hl : raw28183step2Labels = raw28183step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1778 node1778Labels := by rfl

def raw28184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![4, -1, -3]]
def raw28184Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![4, -1, -3]]
def raw28184step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28184step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28184step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28184 raw28184Labels = mixedMoment B node887 node887Labels := by
  calc
    mixedMoment B raw28184 raw28184Labels = mixedMoment B raw28184step0 raw28184step0Labels := by
      have hz : ∀ j, raw28184 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28184step0 = (fun i j => raw28184 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28184step0 raw28184; decide +kernel
      have hl : raw28184step0Labels = raw28184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28184 raw28184Labels permutation346 hz
    mixedMoment B raw28184step0 raw28184step0Labels = mixedMoment B raw28184step1 raw28184step1Labels := by
      have ha : raw28184step1 = (fun i j => raw28184step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28184step1 raw28184step0; decide +kernel
      have hl : raw28184step1Labels = raw28184step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28184step0 raw28184step0Labels permutation149 permutation2
    mixedMoment B raw28184step1 raw28184step1Labels = mixedMoment B raw28184step2 raw28184step2Labels := by
      have ha : raw28184step2 = -raw28184step1 := by apply Matrix.ext; change ∀ i j, raw28184step2 i j = -(raw28184step1 i j); unfold raw28184step2 raw28184step1; decide +kernel
      have hl : raw28184step2Labels = raw28184step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node887 node887Labels := by rfl

def raw28185 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![-2, 2], ![1, -1], ![3, -3]]
def raw28185Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28185step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![1, -1], ![3, -3]]
def raw28185step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28185step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw28185step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28185step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw28185step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical28185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28185 raw28185Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw28185 raw28185Labels = mixedMoment B raw28185step0 raw28185step0Labels := by
      have hz : ∀ j, raw28185 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28185step0 = (fun i j => raw28185 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28185step0 raw28185; decide +kernel
      have hl : raw28185step0Labels = raw28185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28185 raw28185Labels permutation346 hz
    mixedMoment B raw28185step0 raw28185step0Labels = mixedMoment B raw28185step1 raw28185step1Labels := by
      have ha : raw28185step1 = (fun i j => raw28185step0 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw28185step1 raw28185step0; decide +kernel
      have hl : raw28185step1Labels = raw28185step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28185step0 raw28185step0Labels permutation146 permutation0
    mixedMoment B raw28185step1 raw28185step1Labels = mixedMoment B raw28185step2 raw28185step2Labels := by
      have ha : raw28185step2 = -raw28185step1 := by apply Matrix.ext; change ∀ i j, raw28185step2 i j = -(raw28185step1 i j); unfold raw28185step2 raw28185step1; decide +kernel
      have hl : raw28185step2Labels = raw28185step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw28186 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw28186Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28186step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28186step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28186 raw28186Labels = mixedMoment B node1868 node1868Labels := by
  calc
    mixedMoment B raw28186 raw28186Labels = mixedMoment B raw28186step0 raw28186step0Labels := by
      have ha : raw28186step0 = (fun i j => raw28186 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28186step0 raw28186; decide +kernel
      have hl : raw28186step0Labels = raw28186Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28186 raw28186Labels permutation680 permutation2
    _ = mixedMoment B node1868 node1868Labels := by rfl

def raw28187 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw28187Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw28187step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28187step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw28187step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28187 raw28187Labels = mixedMoment B node1944 node1944Labels := by
  calc
    mixedMoment B raw28187 raw28187Labels = mixedMoment B raw28187step0 raw28187step0Labels := by
      have hz : ∀ j, raw28187 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28187step0 = (fun i j => raw28187 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28187step0 raw28187; decide +kernel
      have hl : raw28187step0Labels = raw28187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28187 raw28187Labels permutation346 hz
    mixedMoment B raw28187step0 raw28187step0Labels = mixedMoment B raw28187step1 raw28187step1Labels := by
      have ha : raw28187step1 = (fun i j => raw28187step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28187step1 raw28187step0; decide +kernel
      have hl : raw28187step1Labels = raw28187step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28187step0 raw28187step0Labels permutation151 permutation2
    _ = mixedMoment B node1944 node1944Labels := by rfl

def raw28188 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-3, 0, 3]]
def raw28188Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-3, 0, 3]]
def raw28188step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28188step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28188 raw28188Labels = mixedMoment B node1779 node1779Labels := by
  calc
    mixedMoment B raw28188 raw28188Labels = mixedMoment B raw28188step0 raw28188step0Labels := by
      have hz : ∀ j, raw28188 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28188step0 = (fun i j => raw28188 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28188step0 raw28188; decide +kernel
      have hl : raw28188step0Labels = raw28188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28188 raw28188Labels permutation346 hz
    mixedMoment B raw28188step0 raw28188step0Labels = mixedMoment B raw28188step1 raw28188step1Labels := by
      have ha : raw28188step1 = (fun i j => raw28188step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28188step1 raw28188step0; decide +kernel
      have hl : raw28188step1Labels = raw28188step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28188step0 raw28188step0Labels permutation149 permutation2
    _ = mixedMoment B node1779 node1779Labels := by rfl

def raw28189 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-4, 1, 3]]
def raw28189Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-4, 1, 3]]
def raw28189step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw28189step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28189 raw28189Labels = mixedMoment B node888 node888Labels := by
  calc
    mixedMoment B raw28189 raw28189Labels = mixedMoment B raw28189step0 raw28189step0Labels := by
      have hz : ∀ j, raw28189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28189step0 = (fun i j => raw28189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28189step0 raw28189; decide +kernel
      have hl : raw28189step0Labels = raw28189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28189 raw28189Labels permutation346 hz
    mixedMoment B raw28189step0 raw28189step0Labels = mixedMoment B raw28189step1 raw28189step1Labels := by
      have ha : raw28189step1 = (fun i j => raw28189step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28189step1 raw28189step0; decide +kernel
      have hl : raw28189step1Labels = raw28189step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28189step0 raw28189step0Labels permutation149 permutation2
    _ = mixedMoment B node888 node888Labels := by rfl

def raw28190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw28190Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28190step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28190step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28190step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28190step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28190 raw28190Labels = mixedMoment B node2378 node2378Labels := by
  calc
    mixedMoment B raw28190 raw28190Labels = mixedMoment B raw28190step0 raw28190step0Labels := by
      have ha : raw28190step0 = (fun i j => raw28190 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28190step0 raw28190; decide +kernel
      have hl : raw28190step0Labels = raw28190Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28190 raw28190Labels permutation682 permutation2
    mixedMoment B raw28190step0 raw28190step0Labels = mixedMoment B raw28190step1 raw28190step1Labels := by
      have ha : raw28190step1 = -raw28190step0 := by apply Matrix.ext; change ∀ i j, raw28190step1 i j = -(raw28190step0 i j); unfold raw28190step1 raw28190step0; decide +kernel
      have hl : raw28190step1Labels = raw28190step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2378 node2378Labels := by rfl

def raw28191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw28191Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28191step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw28191step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28191step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw28191step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28191 raw28191Labels = mixedMoment B node2380 node2380Labels := by
  calc
    mixedMoment B raw28191 raw28191Labels = mixedMoment B raw28191step0 raw28191step0Labels := by
      have ha : raw28191step0 = (fun i j => raw28191 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28191step0 raw28191; decide +kernel
      have hl : raw28191step0Labels = raw28191Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28191 raw28191Labels permutation681 permutation2
    mixedMoment B raw28191step0 raw28191step0Labels = mixedMoment B raw28191step1 raw28191step1Labels := by
      have ha : raw28191step1 = -raw28191step0 := by apply Matrix.ext; change ∀ i j, raw28191step1 i j = -(raw28191step0 i j); unfold raw28191step1 raw28191step0; decide +kernel
      have hl : raw28191step1Labels = raw28191step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2380 node2380Labels := by rfl

def raw28192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw28192Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw28192step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw28192step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28192 raw28192Labels = mixedMoment B node2383 node2383Labels := by
  calc
    mixedMoment B raw28192 raw28192Labels = mixedMoment B raw28192step0 raw28192step0Labels := by
      have ha : raw28192step0 = (fun i j => raw28192 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28192step0 raw28192; decide +kernel
      have hl : raw28192step0Labels = raw28192Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28192 raw28192Labels permutation686 permutation2
    mixedMoment B raw28192step0 raw28192step0Labels = mixedMoment B raw28192step1 raw28192step1Labels := by
      have ha : raw28192step1 = -raw28192step0 := by apply Matrix.ext; change ∀ i j, raw28192step1 i j = -(raw28192step0 i j); unfold raw28192step1 raw28192step0; decide +kernel
      have hl : raw28192step1Labels = raw28192step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2383 node2383Labels := by rfl

def raw28193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw28193Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw28193step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28193step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw28193step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28193 raw28193Labels = mixedMoment B node2383 node2383Labels := by
  calc
    mixedMoment B raw28193 raw28193Labels = mixedMoment B raw28193step0 raw28193step0Labels := by
      have ha : raw28193step0 = (fun i j => raw28193 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28193step0 raw28193; decide +kernel
      have hl : raw28193step0Labels = raw28193Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28193 raw28193Labels permutation680 permutation2
    mixedMoment B raw28193step0 raw28193step0Labels = mixedMoment B raw28193step1 raw28193step1Labels := by
      have ha : raw28193step1 = -raw28193step0 := by apply Matrix.ext; change ∀ i j, raw28193step1 i j = -(raw28193step0 i j); unfold raw28193step1 raw28193step0; decide +kernel
      have hl : raw28193step1Labels = raw28193step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2383 node2383Labels := by rfl

def raw28194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw28194Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw28194step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28194step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw28194step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28194 raw28194Labels = mixedMoment B node2662 node2662Labels := by
  calc
    mixedMoment B raw28194 raw28194Labels = mixedMoment B raw28194step0 raw28194step0Labels := by
      have ha : raw28194step0 = (fun i j => raw28194 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28194step0 raw28194; decide +kernel
      have hl : raw28194step0Labels = raw28194Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28194 raw28194Labels permutation682 permutation2
    mixedMoment B raw28194step0 raw28194step0Labels = mixedMoment B raw28194step1 raw28194step1Labels := by
      have ha : raw28194step1 = -raw28194step0 := by apply Matrix.ext; change ∀ i j, raw28194step1 i j = -(raw28194step0 i j); unfold raw28194step1 raw28194step0; decide +kernel
      have hl : raw28194step1Labels = raw28194step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2662 node2662Labels := by rfl

def raw28195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28195Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28195step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw28195step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28195step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw28195step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28195 raw28195Labels = mixedMoment B node3758 node3758Labels := by
  calc
    mixedMoment B raw28195 raw28195Labels = mixedMoment B raw28195step0 raw28195step0Labels := by
      have ha : raw28195step0 = (fun i j => raw28195 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28195step0 raw28195; decide +kernel
      have hl : raw28195step0Labels = raw28195Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28195 raw28195Labels permutation682 permutation2
    mixedMoment B raw28195step0 raw28195step0Labels = mixedMoment B raw28195step1 raw28195step1Labels := by
      have ha : raw28195step1 = -raw28195step0 := by apply Matrix.ext; change ∀ i j, raw28195step1 i j = -(raw28195step0 i j); unfold raw28195step1 raw28195step0; decide +kernel
      have hl : raw28195step1Labels = raw28195step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3758 node3758Labels := by rfl

def raw28196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28196Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28196step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28196 raw28196Labels = mixedMoment B node2922 node2922Labels := by
  calc
    mixedMoment B raw28196 raw28196Labels = mixedMoment B raw28196step0 raw28196step0Labels := by
      have ha : raw28196step0 = (fun i j => raw28196 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28196step0 raw28196; decide +kernel
      have hl : raw28196step0Labels = raw28196Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28196 raw28196Labels permutation158 permutation2
    _ = mixedMoment B node2922 node2922Labels := by rfl

def raw28197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw28197Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28197 raw28197Labels = mixedMoment B node2922 node2922Labels := by
  calc
    _ = mixedMoment B node2922 node2922Labels := by rfl

def raw28198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28198Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw28198step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28198step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw28198step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28198 raw28198Labels = mixedMoment B node1901 node1901Labels := by
  calc
    mixedMoment B raw28198 raw28198Labels = mixedMoment B raw28198step0 raw28198step0Labels := by
      have ha : raw28198step0 = (fun i j => raw28198 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28198step0 raw28198; decide +kernel
      have hl : raw28198step0Labels = raw28198Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28198 raw28198Labels permutation681 permutation2
    mixedMoment B raw28198step0 raw28198step0Labels = mixedMoment B raw28198step1 raw28198step1Labels := by
      have ha : raw28198step1 = -raw28198step0 := by apply Matrix.ext; change ∀ i j, raw28198step1 i j = -(raw28198step0 i j); unfold raw28198step1 raw28198step0; decide +kernel
      have hl : raw28198step1Labels = raw28198step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1901 node1901Labels := by rfl

def raw28199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28199Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw28199step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28199step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw28199step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28199 raw28199Labels = mixedMoment B node1912 node1912Labels := by
  calc
    mixedMoment B raw28199 raw28199Labels = mixedMoment B raw28199step0 raw28199step0Labels := by
      have ha : raw28199step0 = (fun i j => raw28199 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28199step0 raw28199; decide +kernel
      have hl : raw28199step0Labels = raw28199Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28199 raw28199Labels permutation686 permutation2
    mixedMoment B raw28199step0 raw28199step0Labels = mixedMoment B raw28199step1 raw28199step1Labels := by
      have ha : raw28199step1 = -raw28199step0 := by apply Matrix.ext; change ∀ i j, raw28199step1 i j = -(raw28199step0 i j); unfold raw28199step1 raw28199step0; decide +kernel
      have hl : raw28199step1Labels = raw28199step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1912 node1912Labels := by rfl

def raw28200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw28200step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28200step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw28200step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28200 raw28200Labels = mixedMoment B node1912 node1912Labels := by
  calc
    mixedMoment B raw28200 raw28200Labels = mixedMoment B raw28200step0 raw28200step0Labels := by
      have ha : raw28200step0 = (fun i j => raw28200 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28200step0 raw28200; decide +kernel
      have hl : raw28200step0Labels = raw28200Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28200 raw28200Labels permutation680 permutation2
    mixedMoment B raw28200step0 raw28200step0Labels = mixedMoment B raw28200step1 raw28200step1Labels := by
      have ha : raw28200step1 = -raw28200step0 := by apply Matrix.ext; change ∀ i j, raw28200step1 i j = -(raw28200step0 i j); unfold raw28200step1 raw28200step0; decide +kernel
      have hl : raw28200step1Labels = raw28200step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1912 node1912Labels := by rfl

def raw28201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw28201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw28201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28201step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw28201step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28201 raw28201Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw28201 raw28201Labels = mixedMoment B raw28201step0 raw28201step0Labels := by
      have ha : raw28201step0 = (fun i j => raw28201 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28201step0 raw28201; decide +kernel
      have hl : raw28201step0Labels = raw28201Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28201 raw28201Labels permutation682 permutation2
    mixedMoment B raw28201step0 raw28201step0Labels = mixedMoment B raw28201step1 raw28201step1Labels := by
      have ha : raw28201step1 = -raw28201step0 := by apply Matrix.ext; change ∀ i j, raw28201step1 i j = -(raw28201step0 i j); unfold raw28201step1 raw28201step0; decide +kernel
      have hl : raw28201step1Labels = raw28201step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2191 node2191Labels := by rfl

def raw28202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw28202Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw28202step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28202step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw28202step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28202 raw28202Labels = mixedMoment B node3460 node3460Labels := by
  calc
    mixedMoment B raw28202 raw28202Labels = mixedMoment B raw28202step0 raw28202step0Labels := by
      have ha : raw28202step0 = (fun i j => raw28202 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28202step0 raw28202; decide +kernel
      have hl : raw28202step0Labels = raw28202Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28202 raw28202Labels permutation682 permutation2
    mixedMoment B raw28202step0 raw28202step0Labels = mixedMoment B raw28202step1 raw28202step1Labels := by
      have ha : raw28202step1 = -raw28202step0 := by apply Matrix.ext; change ∀ i j, raw28202step1 i j = -(raw28202step0 i j); unfold raw28202step1 raw28202step0; decide +kernel
      have hl : raw28202step1Labels = raw28202step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3460 node3460Labels := by rfl

def raw28203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw28203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28203step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28203step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28203step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28203 raw28203Labels = mixedMoment B node1877 node1877Labels := by
  calc
    mixedMoment B raw28203 raw28203Labels = mixedMoment B raw28203step0 raw28203step0Labels := by
      have ha : raw28203step0 = (fun i j => raw28203 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28203step0 raw28203; decide +kernel
      have hl : raw28203step0Labels = raw28203Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28203 raw28203Labels permutation686 permutation2
    mixedMoment B raw28203step0 raw28203step0Labels = mixedMoment B raw28203step1 raw28203step1Labels := by
      have ha : raw28203step1 = -raw28203step0 := by apply Matrix.ext; change ∀ i j, raw28203step1 i j = -(raw28203step0 i j); unfold raw28203step1 raw28203step0; decide +kernel
      have hl : raw28203step1Labels = raw28203step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1877 node1877Labels := by rfl

def raw28204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw28204Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28204step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28204step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28204step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28204 raw28204Labels = mixedMoment B node1762 node1762Labels := by
  calc
    mixedMoment B raw28204 raw28204Labels = mixedMoment B raw28204step0 raw28204step0Labels := by
      have ha : raw28204step0 = (fun i j => raw28204 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28204step0 raw28204; decide +kernel
      have hl : raw28204step0Labels = raw28204Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28204 raw28204Labels permutation686 permutation2
    mixedMoment B raw28204step0 raw28204step0Labels = mixedMoment B raw28204step1 raw28204step1Labels := by
      have ha : raw28204step1 = -raw28204step0 := by apply Matrix.ext; change ∀ i j, raw28204step1 i j = -(raw28204step0 i j); unfold raw28204step1 raw28204step0; decide +kernel
      have hl : raw28204step1Labels = raw28204step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1762 node1762Labels := by rfl

def raw28205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw28205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28205step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28205step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28205step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28205 raw28205Labels = mixedMoment B node868 node868Labels := by
  calc
    mixedMoment B raw28205 raw28205Labels = mixedMoment B raw28205step0 raw28205step0Labels := by
      have ha : raw28205step0 = (fun i j => raw28205 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28205step0 raw28205; decide +kernel
      have hl : raw28205step0Labels = raw28205Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28205 raw28205Labels permutation686 permutation2
    mixedMoment B raw28205step0 raw28205step0Labels = mixedMoment B raw28205step1 raw28205step1Labels := by
      have ha : raw28205step1 = -raw28205step0 := by apply Matrix.ext; change ∀ i j, raw28205step1 i j = -(raw28205step0 i j); unfold raw28205step1 raw28205step0; decide +kernel
      have hl : raw28205step1Labels = raw28205step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node868 node868Labels := by rfl

def raw28206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw28206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw28206step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28206 raw28206Labels = mixedMoment B node2921 node2921Labels := by
  calc
    mixedMoment B raw28206 raw28206Labels = mixedMoment B raw28206step0 raw28206step0Labels := by
      have ha : raw28206step0 = (fun i j => raw28206 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28206step0 raw28206; decide +kernel
      have hl : raw28206step0Labels = raw28206Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28206 raw28206Labels permutation158 permutation2
    _ = mixedMoment B node2921 node2921Labels := by rfl

def raw28207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw28207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28207 raw28207Labels = mixedMoment B node2921 node2921Labels := by
  calc
    _ = mixedMoment B node2921 node2921Labels := by rfl

def raw28208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw28208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28208 raw28208Labels = mixedMoment B node2912 node2912Labels := by
  calc
    _ = mixedMoment B node2912 node2912Labels := by rfl

def raw28209 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw28209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw28209step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw28209step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28209 raw28209Labels = mixedMoment B node1944 node1944Labels := by
  calc
    mixedMoment B raw28209 raw28209Labels = mixedMoment B raw28209step0 raw28209step0Labels := by
      have hz : ∀ j, raw28209 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28209step0 = (fun i j => raw28209 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28209step0 raw28209; decide +kernel
      have hl : raw28209step0Labels = raw28209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28209 raw28209Labels permutation434 hz
    mixedMoment B raw28209step0 raw28209step0Labels = mixedMoment B raw28209step1 raw28209step1Labels := by
      have ha : raw28209step1 = (fun i j => raw28209step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28209step1 raw28209step0; decide +kernel
      have hl : raw28209step1Labels = raw28209step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28209step0 raw28209step0Labels permutation151 permutation2
    _ = mixedMoment B node1944 node1944Labels := by rfl

def raw28210 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-3, 0, 3]]
def raw28210Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw28210step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28210 raw28210Labels = mixedMoment B node1768 node1768Labels := by
  calc
    mixedMoment B raw28210 raw28210Labels = mixedMoment B raw28210step0 raw28210step0Labels := by
      have ha : raw28210step0 = (fun i j => raw28210 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28210step0 raw28210; decide +kernel
      have hl : raw28210step0Labels = raw28210Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28210 raw28210Labels permutation682 permutation2
    _ = mixedMoment B node1768 node1768Labels := by rfl

def raw28211 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-4, 1, 3]]
def raw28211Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw28211step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28211 raw28211Labels = mixedMoment B node875 node875Labels := by
  calc
    mixedMoment B raw28211 raw28211Labels = mixedMoment B raw28211step0 raw28211step0Labels := by
      have ha : raw28211step0 = (fun i j => raw28211 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28211step0 raw28211; decide +kernel
      have hl : raw28211step0Labels = raw28211Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28211 raw28211Labels permutation682 permutation2
    _ = mixedMoment B node875 node875Labels := by rfl

def raw28212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw28212step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28212step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28212step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw28212step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28212 raw28212Labels = mixedMoment B node2080 node2080Labels := by
  calc
    mixedMoment B raw28212 raw28212Labels = mixedMoment B raw28212step0 raw28212step0Labels := by
      have hz : ∀ j, raw28212 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28212step0 = (fun i j => raw28212 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28212step0 raw28212; decide +kernel
      have hl : raw28212step0Labels = raw28212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28212 raw28212Labels permutation434 hz
    mixedMoment B raw28212step0 raw28212step0Labels = mixedMoment B raw28212step1 raw28212step1Labels := by
      have ha : raw28212step1 = (fun i j => raw28212step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28212step1 raw28212step0; decide +kernel
      have hl : raw28212step1Labels = raw28212step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28212step0 raw28212step0Labels permutation151 permutation2
    mixedMoment B raw28212step1 raw28212step1Labels = mixedMoment B raw28212step2 raw28212step2Labels := by
      have ha : raw28212step2 = -raw28212step1 := by apply Matrix.ext; change ∀ i j, raw28212step2 i j = -(raw28212step1 i j); unfold raw28212step2 raw28212step1; decide +kernel
      have hl : raw28212step2Labels = raw28212step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2080 node2080Labels := by rfl

def raw28213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw28213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw28213step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28213step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw28213step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28213 raw28213Labels = mixedMoment B node2082 node2082Labels := by
  calc
    mixedMoment B raw28213 raw28213Labels = mixedMoment B raw28213step0 raw28213step0Labels := by
      have hz : ∀ j, raw28213 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28213step0 = (fun i j => raw28213 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28213step0 raw28213; decide +kernel
      have hl : raw28213step0Labels = raw28213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28213 raw28213Labels permutation434 hz
    mixedMoment B raw28213step0 raw28213step0Labels = mixedMoment B raw28213step1 raw28213step1Labels := by
      have ha : raw28213step1 = (fun i j => raw28213step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28213step1 raw28213step0; decide +kernel
      have hl : raw28213step1Labels = raw28213step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28213step0 raw28213step0Labels permutation150 permutation2
    mixedMoment B raw28213step1 raw28213step1Labels = mixedMoment B raw28213step2 raw28213step2Labels := by
      have ha : raw28213step2 = -raw28213step1 := by apply Matrix.ext; change ∀ i j, raw28213step2 i j = -(raw28213step1 i j); unfold raw28213step2 raw28213step1; decide +kernel
      have hl : raw28213step2Labels = raw28213step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2082 node2082Labels := by rfl

def raw28214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28214Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw28214step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw28214step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28214step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw28214step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28214 raw28214Labels = mixedMoment B node2102 node2102Labels := by
  calc
    mixedMoment B raw28214 raw28214Labels = mixedMoment B raw28214step0 raw28214step0Labels := by
      have hz : ∀ j, raw28214 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28214step0 = (fun i j => raw28214 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28214step0 raw28214; decide +kernel
      have hl : raw28214step0Labels = raw28214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28214 raw28214Labels permutation434 hz
    mixedMoment B raw28214step0 raw28214step0Labels = mixedMoment B raw28214step1 raw28214step1Labels := by
      have ha : raw28214step1 = (fun i j => raw28214step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28214step1 raw28214step0; decide +kernel
      have hl : raw28214step1Labels = raw28214step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28214step0 raw28214step0Labels permutation151 permutation2
    mixedMoment B raw28214step1 raw28214step1Labels = mixedMoment B raw28214step2 raw28214step2Labels := by
      have ha : raw28214step2 = -raw28214step1 := by apply Matrix.ext; change ∀ i j, raw28214step2 i j = -(raw28214step1 i j); unfold raw28214step2 raw28214step1; decide +kernel
      have hl : raw28214step2Labels = raw28214step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2102 node2102Labels := by rfl

def raw28215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, 0, -3]]
def raw28215Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw28215step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28215step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw28215step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28215 raw28215Labels = mixedMoment B node2076 node2076Labels := by
  calc
    mixedMoment B raw28215 raw28215Labels = mixedMoment B raw28215step0 raw28215step0Labels := by
      have ha : raw28215step0 = (fun i j => raw28215 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28215step0 raw28215; decide +kernel
      have hl : raw28215step0Labels = raw28215Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28215 raw28215Labels permutation682 permutation2
    mixedMoment B raw28215step0 raw28215step0Labels = mixedMoment B raw28215step1 raw28215step1Labels := by
      have ha : raw28215step1 = -raw28215step0 := by apply Matrix.ext; change ∀ i j, raw28215step1 i j = -(raw28215step0 i j); unfold raw28215step1 raw28215step0; decide +kernel
      have hl : raw28215step1Labels = raw28215step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2076 node2076Labels := by rfl

def raw28216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw28216Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![3, 0, -3]]
def raw28216step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw28216step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28216step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw28216step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28216 raw28216Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw28216 raw28216Labels = mixedMoment B raw28216step0 raw28216step0Labels := by
      have hz : ∀ j, raw28216 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28216step0 = (fun i j => raw28216 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28216step0 raw28216; decide +kernel
      have hl : raw28216step0Labels = raw28216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28216 raw28216Labels permutation434 hz
    mixedMoment B raw28216step0 raw28216step0Labels = mixedMoment B raw28216step1 raw28216step1Labels := by
      have ha : raw28216step1 = (fun i j => raw28216step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28216step1 raw28216step0; decide +kernel
      have hl : raw28216step1Labels = raw28216step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28216step0 raw28216step0Labels permutation145 permutation2
    mixedMoment B raw28216step1 raw28216step1Labels = mixedMoment B raw28216step2 raw28216step2Labels := by
      have ha : raw28216step2 = -raw28216step1 := by apply Matrix.ext; change ∀ i j, raw28216step2 i j = -(raw28216step1 i j); unfold raw28216step2 raw28216step1; decide +kernel
      have hl : raw28216step2Labels = raw28216step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2206 node2206Labels := by rfl

def raw28217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw28217Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw28217step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw28217step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28217step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw28217step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28217 raw28217Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw28217 raw28217Labels = mixedMoment B raw28217step0 raw28217step0Labels := by
      have hz : ∀ j, raw28217 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28217step0 = (fun i j => raw28217 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28217step0 raw28217; decide +kernel
      have hl : raw28217step0Labels = raw28217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28217 raw28217Labels permutation434 hz
    mixedMoment B raw28217step0 raw28217step0Labels = mixedMoment B raw28217step1 raw28217step1Labels := by
      have ha : raw28217step1 = (fun i j => raw28217step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28217step1 raw28217step0; decide +kernel
      have hl : raw28217step1Labels = raw28217step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28217step0 raw28217step0Labels permutation151 permutation2
    mixedMoment B raw28217step1 raw28217step1Labels = mixedMoment B raw28217step2 raw28217step2Labels := by
      have ha : raw28217step2 = -raw28217step1 := by apply Matrix.ext; change ∀ i j, raw28217step2 i j = -(raw28217step1 i j); unfold raw28217step2 raw28217step1; decide +kernel
      have hl : raw28217step2Labels = raw28217step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3565 node3565Labels := by rfl

def raw28218 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![0, 0], ![-1, 1], ![3, -3]]
def raw28218Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28218step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![-1, 1], ![3, -3]]
def raw28218step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28218step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw28218step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28218step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw28218step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical28218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28218 raw28218Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw28218 raw28218Labels = mixedMoment B raw28218step0 raw28218step0Labels := by
      have hz : ∀ j, raw28218 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28218step0 = (fun i j => raw28218 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28218step0 raw28218; decide +kernel
      have hl : raw28218step0Labels = raw28218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28218 raw28218Labels permutation434 hz
    mixedMoment B raw28218step0 raw28218step0Labels = mixedMoment B raw28218step1 raw28218step1Labels := by
      have ha : raw28218step1 = (fun i j => raw28218step0 (permutation141 i) (permutation0 j)) := by apply Matrix.ext; unfold raw28218step1 raw28218step0; decide +kernel
      have hl : raw28218step1Labels = raw28218step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28218step0 raw28218step0Labels permutation141 permutation0
    mixedMoment B raw28218step1 raw28218step1Labels = mixedMoment B raw28218step2 raw28218step2Labels := by
      have ha : raw28218step2 = -raw28218step1 := by apply Matrix.ext; change ∀ i j, raw28218step2 i j = -(raw28218step1 i j); unfold raw28218step2 raw28218step1; decide +kernel
      have hl : raw28218step2Labels = raw28218step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw28219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28219Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28219step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28219step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28219step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28219 raw28219Labels = mixedMoment B node2450 node2450Labels := by
  calc
    mixedMoment B raw28219 raw28219Labels = mixedMoment B raw28219step0 raw28219step0Labels := by
      have ha : raw28219step0 = (fun i j => raw28219 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28219step0 raw28219; decide +kernel
      have hl : raw28219step0Labels = raw28219Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28219 raw28219Labels permutation682 permutation2
    mixedMoment B raw28219step0 raw28219step0Labels = mixedMoment B raw28219step1 raw28219step1Labels := by
      have ha : raw28219step1 = -raw28219step0 := by apply Matrix.ext; change ∀ i j, raw28219step1 i j = -(raw28219step0 i j); unfold raw28219step1 raw28219step0; decide +kernel
      have hl : raw28219step1Labels = raw28219step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2450 node2450Labels := by rfl

def raw28220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28220Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw28220step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28220step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw28220step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28220 raw28220Labels = mixedMoment B node2452 node2452Labels := by
  calc
    mixedMoment B raw28220 raw28220Labels = mixedMoment B raw28220step0 raw28220step0Labels := by
      have ha : raw28220step0 = (fun i j => raw28220 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28220step0 raw28220; decide +kernel
      have hl : raw28220step0Labels = raw28220Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28220 raw28220Labels permutation681 permutation2
    mixedMoment B raw28220step0 raw28220step0Labels = mixedMoment B raw28220step1 raw28220step1Labels := by
      have ha : raw28220step1 = -raw28220step0 := by apply Matrix.ext; change ∀ i j, raw28220step1 i j = -(raw28220step0 i j); unfold raw28220step1 raw28220step0; decide +kernel
      have hl : raw28220step1Labels = raw28220step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2452 node2452Labels := by rfl

def raw28221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28221Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw28221step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28221step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw28221step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28221 raw28221Labels = mixedMoment B node2478 node2478Labels := by
  calc
    mixedMoment B raw28221 raw28221Labels = mixedMoment B raw28221step0 raw28221step0Labels := by
      have ha : raw28221step0 = (fun i j => raw28221 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28221step0 raw28221; decide +kernel
      have hl : raw28221step0Labels = raw28221Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28221 raw28221Labels permutation688 permutation2
    mixedMoment B raw28221step0 raw28221step0Labels = mixedMoment B raw28221step1 raw28221step1Labels := by
      have ha : raw28221step1 = -raw28221step0 := by apply Matrix.ext; change ∀ i j, raw28221step1 i j = -(raw28221step0 i j); unfold raw28221step1 raw28221step0; decide +kernel
      have hl : raw28221step1Labels = raw28221step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2478 node2478Labels := by rfl

def raw28222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28222Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw28222step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28222step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw28222step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28222 raw28222Labels = mixedMoment B node2462 node2462Labels := by
  calc
    mixedMoment B raw28222 raw28222Labels = mixedMoment B raw28222step0 raw28222step0Labels := by
      have ha : raw28222step0 = (fun i j => raw28222 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28222step0 raw28222; decide +kernel
      have hl : raw28222step0Labels = raw28222Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28222 raw28222Labels permutation682 permutation2
    mixedMoment B raw28222step0 raw28222step0Labels = mixedMoment B raw28222step1 raw28222step1Labels := by
      have ha : raw28222step1 = -raw28222step0 := by apply Matrix.ext; change ∀ i j, raw28222step1 i j = -(raw28222step0 i j); unfold raw28222step1 raw28222step0; decide +kernel
      have hl : raw28222step1Labels = raw28222step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2462 node2462Labels := by rfl

def raw28223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw28223Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28223step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw28223step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28223step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw28223step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28223 raw28223Labels = mixedMoment B node2695 node2695Labels := by
  calc
    mixedMoment B raw28223 raw28223Labels = mixedMoment B raw28223step0 raw28223step0Labels := by
      have ha : raw28223step0 = (fun i j => raw28223 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28223step0 raw28223; decide +kernel
      have hl : raw28223step0Labels = raw28223Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28223 raw28223Labels permutation646 permutation2
    mixedMoment B raw28223step0 raw28223step0Labels = mixedMoment B raw28223step1 raw28223step1Labels := by
      have ha : raw28223step1 = -raw28223step0 := by apply Matrix.ext; change ∀ i j, raw28223step1 i j = -(raw28223step0 i j); unfold raw28223step1 raw28223step0; decide +kernel
      have hl : raw28223step1Labels = raw28223step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2695 node2695Labels := by rfl

def raw28224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw28224Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw28224step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28224step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw28224step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28224 raw28224Labels = mixedMoment B node3794 node3794Labels := by
  calc
    mixedMoment B raw28224 raw28224Labels = mixedMoment B raw28224step0 raw28224step0Labels := by
      have ha : raw28224step0 = (fun i j => raw28224 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28224step0 raw28224; decide +kernel
      have hl : raw28224step0Labels = raw28224Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28224 raw28224Labels permutation682 permutation2
    mixedMoment B raw28224step0 raw28224step0Labels = mixedMoment B raw28224step1 raw28224step1Labels := by
      have ha : raw28224step1 = -raw28224step0 := by apply Matrix.ext; change ∀ i j, raw28224step1 i j = -(raw28224step0 i j); unfold raw28224step1 raw28224step0; decide +kernel
      have hl : raw28224step1Labels = raw28224step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3794 node3794Labels := by rfl

def raw28225 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![2, -2]]
def raw28225Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28225step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw28225step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical28225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28225 raw28225Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw28225 raw28225Labels = mixedMoment B raw28225step0 raw28225step0Labels := by
      have ha : raw28225step0 = (fun i j => raw28225 (permutation271 i) (permutation0 j)) := by apply Matrix.ext; unfold raw28225step0 raw28225; decide +kernel
      have hl : raw28225step0Labels = raw28225Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28225 raw28225Labels permutation271 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw28226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28226Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28226step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28226step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 1, -2], ![3, -2, -1]]
def raw28226step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28226step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-2, 1, 1], ![-2, 0, 2]]
def raw28226step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28226step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw28226step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28226 raw28226Labels = mixedMoment B node2889 node2889Labels := by
  calc
    mixedMoment B raw28226 raw28226Labels = mixedMoment B raw28226step0 raw28226step0Labels := by
      have hz : ∀ j, raw28226 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28226step0 = (fun i j => raw28226 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28226step0 raw28226; decide +kernel
      have hl : raw28226step0Labels = raw28226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28226 raw28226Labels permutation434 hz
    mixedMoment B raw28226step0 raw28226step0Labels = mixedMoment B raw28226step1 raw28226step1Labels := by
      have hz : ∀ j, raw28226step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28226step1 = (fun i j => raw28226step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28226step1 raw28226step0; decide +kernel
      have hl : raw28226step1Labels = raw28226step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28226step0 raw28226step0Labels permutation80 hz
    mixedMoment B raw28226step1 raw28226step1Labels = mixedMoment B raw28226step2 raw28226step2Labels := by
      have ha : raw28226step2 = (fun i j => raw28226step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28226step2 raw28226step1; decide +kernel
      have hl : raw28226step2Labels = raw28226step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28226step1 raw28226step1Labels permutation30 permutation2
    mixedMoment B raw28226step2 raw28226step2Labels = mixedMoment B raw28226step3 raw28226step3Labels := by
      have ha : raw28226step3 = -raw28226step2 := by apply Matrix.ext; change ∀ i j, raw28226step3 i j = -(raw28226step2 i j); unfold raw28226step3 raw28226step2; decide +kernel
      have hl : raw28226step3Labels = raw28226step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2889 node2889Labels := by rfl

def raw28227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28227step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28227step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![3, -2, -1]]
def raw28227step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28227 raw28227Labels = mixedMoment B node2886 node2886Labels := by
  calc
    mixedMoment B raw28227 raw28227Labels = mixedMoment B raw28227step0 raw28227step0Labels := by
      have hz : ∀ j, raw28227 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28227step0 = (fun i j => raw28227 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28227step0 raw28227; decide +kernel
      have hl : raw28227step0Labels = raw28227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28227 raw28227Labels permutation434 hz
    mixedMoment B raw28227step0 raw28227step0Labels = mixedMoment B raw28227step1 raw28227step1Labels := by
      have hz : ∀ j, raw28227step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28227step1 = (fun i j => raw28227step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28227step1 raw28227step0; decide +kernel
      have hl : raw28227step1Labels = raw28227step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28227step0 raw28227step0Labels permutation80 hz
    _ = mixedMoment B node2886 node2886Labels := by rfl

def raw28228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28228Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28228step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28228 raw28228Labels = mixedMoment B node2811 node2811Labels := by
  calc
    mixedMoment B raw28228 raw28228Labels = mixedMoment B raw28228step0 raw28228step0Labels := by
      have hz : ∀ j, raw28228 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28228step0 = (fun i j => raw28228 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28228step0 raw28228; decide +kernel
      have hl : raw28228step0Labels = raw28228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28228 raw28228Labels permutation434 hz
    _ = mixedMoment B node2811 node2811Labels := by rfl

def raw28229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28229Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw28229step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28229 raw28229Labels = mixedMoment B node2811 node2811Labels := by
  calc
    mixedMoment B raw28229 raw28229Labels = mixedMoment B raw28229step0 raw28229step0Labels := by
      have hz : ∀ j, raw28229 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28229step0 = (fun i j => raw28229 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28229step0 raw28229; decide +kernel
      have hl : raw28229step0Labels = raw28229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28229 raw28229Labels permutation346 hz
    _ = mixedMoment B node2811 node2811Labels := by rfl

def raw28230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28230Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw28230step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28230step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 0, -2], ![3, -2, -1]]
def raw28230step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28230 raw28230Labels = mixedMoment B node2820 node2820Labels := by
  calc
    mixedMoment B raw28230 raw28230Labels = mixedMoment B raw28230step0 raw28230step0Labels := by
      have hz : ∀ j, raw28230 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28230step0 = (fun i j => raw28230 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28230step0 raw28230; decide +kernel
      have hl : raw28230step0Labels = raw28230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28230 raw28230Labels permutation434 hz
    mixedMoment B raw28230step0 raw28230step0Labels = mixedMoment B raw28230step1 raw28230step1Labels := by
      have hz : ∀ j, raw28230step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28230step1 = (fun i j => raw28230step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28230step1 raw28230step0; decide +kernel
      have hl : raw28230step1Labels = raw28230step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28230step0 raw28230step0Labels permutation80 hz
    _ = mixedMoment B node2820 node2820Labels := by rfl

def raw28231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw28231Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw28231step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28231step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![4, -3, -1]]
def raw28231step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28231step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-2, 0, 2], ![-3, 2, 1]]
def raw28231step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28231step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw28231step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28231 raw28231Labels = mixedMoment B node1325 node1325Labels := by
  calc
    mixedMoment B raw28231 raw28231Labels = mixedMoment B raw28231step0 raw28231step0Labels := by
      have hz : ∀ j, raw28231 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28231step0 = (fun i j => raw28231 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28231step0 raw28231; decide +kernel
      have hl : raw28231step0Labels = raw28231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28231 raw28231Labels permutation434 hz
    mixedMoment B raw28231step0 raw28231step0Labels = mixedMoment B raw28231step1 raw28231step1Labels := by
      have hz : ∀ j, raw28231step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28231step1 = (fun i j => raw28231step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28231step1 raw28231step0; decide +kernel
      have hl : raw28231step1Labels = raw28231step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28231step0 raw28231step0Labels permutation80 hz
    mixedMoment B raw28231step1 raw28231step1Labels = mixedMoment B raw28231step2 raw28231step2Labels := by
      have ha : raw28231step2 = (fun i j => raw28231step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28231step2 raw28231step1; decide +kernel
      have hl : raw28231step2Labels = raw28231step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28231step1 raw28231step1Labels permutation31 permutation2
    mixedMoment B raw28231step2 raw28231step2Labels = mixedMoment B raw28231step3 raw28231step3Labels := by
      have ha : raw28231step3 = -raw28231step2 := by apply Matrix.ext; change ∀ i j, raw28231step3 i j = -(raw28231step2 i j); unfold raw28231step3 raw28231step2; decide +kernel
      have hl : raw28231step3Labels = raw28231step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1325 node1325Labels := by rfl

def raw28232 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]
def raw28232Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28232step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![0, 0], ![2, -2], ![1, -1]]
def raw28232step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28232step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]
def raw28232step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw28232step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw28232step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical28232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28232 raw28232Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw28232 raw28232Labels = mixedMoment B raw28232step0 raw28232step0Labels := by
      have hz : ∀ j, raw28232 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28232step0 = (fun i j => raw28232 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28232step0 raw28232; decide +kernel
      have hl : raw28232step0Labels = raw28232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28232 raw28232Labels permutation434 hz
    mixedMoment B raw28232step0 raw28232step0Labels = mixedMoment B raw28232step1 raw28232step1Labels := by
      have hz : ∀ j, raw28232step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28232step1 = (fun i j => raw28232step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28232step1 raw28232step0; decide +kernel
      have hl : raw28232step1Labels = raw28232step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28232step0 raw28232step0Labels permutation80 hz
    mixedMoment B raw28232step1 raw28232step1Labels = mixedMoment B raw28232step2 raw28232step2Labels := by
      have ha : raw28232step2 = (fun i j => raw28232step1 (permutation15 i) (permutation0 j)) := by apply Matrix.ext; unfold raw28232step2 raw28232step1; decide +kernel
      have hl : raw28232step2Labels = raw28232step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28232step1 raw28232step1Labels permutation15 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw28233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw28233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw28233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28233step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw28233step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28233 raw28233Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw28233 raw28233Labels = mixedMoment B raw28233step0 raw28233step0Labels := by
      have hz : ∀ j, raw28233 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28233step0 = (fun i j => raw28233 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28233step0 raw28233; decide +kernel
      have hl : raw28233step0Labels = raw28233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28233 raw28233Labels permutation434 hz
    mixedMoment B raw28233step0 raw28233step0Labels = mixedMoment B raw28233step1 raw28233step1Labels := by
      have hz : ∀ j, raw28233step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28233step1 = (fun i j => raw28233step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28233step1 raw28233step0; decide +kernel
      have hl : raw28233step1Labels = raw28233step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28233step0 raw28233step0Labels permutation80 hz
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw28234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28234step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28234step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28234step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28234step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28234step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28234 raw28234Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw28234 raw28234Labels = mixedMoment B raw28234step0 raw28234step0Labels := by
      have hz : ∀ j, raw28234 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28234step0 = (fun i j => raw28234 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28234step0 raw28234; decide +kernel
      have hl : raw28234step0Labels = raw28234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28234 raw28234Labels permutation434 hz
    mixedMoment B raw28234step0 raw28234step0Labels = mixedMoment B raw28234step1 raw28234step1Labels := by
      have hz : ∀ j, raw28234step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28234step1 = (fun i j => raw28234step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28234step1 raw28234step0; decide +kernel
      have hl : raw28234step1Labels = raw28234step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28234step0 raw28234step0Labels permutation80 hz
    mixedMoment B raw28234step1 raw28234step1Labels = mixedMoment B raw28234step2 raw28234step2Labels := by
      have ha : raw28234step2 = (fun i j => raw28234step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28234step2 raw28234step1; decide +kernel
      have hl : raw28234step2Labels = raw28234step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28234step1 raw28234step1Labels permutation8 permutation3
    mixedMoment B raw28234step2 raw28234step2Labels = mixedMoment B raw28234step3 raw28234step3Labels := by
      have ha : raw28234step3 = raw28234step2 := by apply Matrix.ext; unfold raw28234step3 raw28234step2; decide +kernel
      have hl : raw28234step2Labels = labelEmbedding6 ∘ raw28234step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28234step2 raw28234step2Labels raw28234step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

def raw28235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28235step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28235step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28235step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28235step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28235step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28235 raw28235Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw28235 raw28235Labels = mixedMoment B raw28235step0 raw28235step0Labels := by
      have hz : ∀ j, raw28235 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28235step0 = (fun i j => raw28235 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28235step0 raw28235; decide +kernel
      have hl : raw28235step0Labels = raw28235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28235 raw28235Labels permutation434 hz
    mixedMoment B raw28235step0 raw28235step0Labels = mixedMoment B raw28235step1 raw28235step1Labels := by
      have ha : raw28235step1 = (fun i j => raw28235step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28235step1 raw28235step0; decide +kernel
      have hl : raw28235step1Labels = raw28235step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28235step0 raw28235step0Labels permutation149 permutation3
    mixedMoment B raw28235step1 raw28235step1Labels = mixedMoment B raw28235step2 raw28235step2Labels := by
      have ha : raw28235step2 = -raw28235step1 := by apply Matrix.ext; change ∀ i j, raw28235step2 i j = -(raw28235step1 i j); unfold raw28235step2 raw28235step1; decide +kernel
      have hl : raw28235step2Labels = raw28235step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28235step2 raw28235step2Labels = mixedMoment B raw28235step3 raw28235step3Labels := by
      have ha : raw28235step3 = raw28235step2 := by apply Matrix.ext; unfold raw28235step3 raw28235step2; decide +kernel
      have hl : raw28235step2Labels = labelEmbedding6 ∘ raw28235step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28235step2 raw28235step2Labels raw28235step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw28236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28236step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28236step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28236step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28236step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28236step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28236 raw28236Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw28236 raw28236Labels = mixedMoment B raw28236step0 raw28236step0Labels := by
      have hz : ∀ j, raw28236 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28236step0 = (fun i j => raw28236 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28236step0 raw28236; decide +kernel
      have hl : raw28236step0Labels = raw28236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28236 raw28236Labels permutation346 hz
    mixedMoment B raw28236step0 raw28236step0Labels = mixedMoment B raw28236step1 raw28236step1Labels := by
      have ha : raw28236step1 = (fun i j => raw28236step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28236step1 raw28236step0; decide +kernel
      have hl : raw28236step1Labels = raw28236step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28236step0 raw28236step0Labels permutation149 permutation3
    mixedMoment B raw28236step1 raw28236step1Labels = mixedMoment B raw28236step2 raw28236step2Labels := by
      have ha : raw28236step2 = -raw28236step1 := by apply Matrix.ext; change ∀ i j, raw28236step2 i j = -(raw28236step1 i j); unfold raw28236step2 raw28236step1; decide +kernel
      have hl : raw28236step2Labels = raw28236step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28236step2 raw28236step2Labels = mixedMoment B raw28236step3 raw28236step3Labels := by
      have ha : raw28236step3 = raw28236step2 := by apply Matrix.ext; unfold raw28236step3 raw28236step2; decide +kernel
      have hl : raw28236step2Labels = labelEmbedding6 ∘ raw28236step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28236step2 raw28236step2Labels raw28236step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw28237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw28237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw28237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28237step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw28237step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28237step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw28237step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28237 raw28237Labels = mixedMoment B node5296 node5296Labels := by
  calc
    mixedMoment B raw28237 raw28237Labels = mixedMoment B raw28237step0 raw28237step0Labels := by
      have hz : ∀ j, raw28237 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28237step0 = (fun i j => raw28237 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28237step0 raw28237; decide +kernel
      have hl : raw28237step0Labels = raw28237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28237 raw28237Labels permutation520 hz
    mixedMoment B raw28237step0 raw28237step0Labels = mixedMoment B raw28237step1 raw28237step1Labels := by
      have hz : ∀ j, raw28237step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28237step1 = (fun i j => raw28237step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28237step1 raw28237step0; decide +kernel
      have hl : raw28237step1Labels = raw28237step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28237step0 raw28237step0Labels permutation104 hz
    mixedMoment B raw28237step1 raw28237step1Labels = mixedMoment B raw28237step2 raw28237step2Labels := by
      have hz : ∀ j, raw28237step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw28237step2 = (fun i j => raw28237step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw28237step2 raw28237step1; decide +kernel
      have hl : raw28237step2Labels = raw28237step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28237step1 raw28237step1Labels permutation20 hz
    _ = mixedMoment B node5296 node5296Labels := by rfl

def raw28238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28238step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28238step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28238step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28238 raw28238Labels = mixedMoment B node4517 node4517Labels := by
  calc
    mixedMoment B raw28238 raw28238Labels = mixedMoment B raw28238step0 raw28238step0Labels := by
      have hz : ∀ j, raw28238 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28238step0 = (fun i j => raw28238 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28238step0 raw28238; decide +kernel
      have hl : raw28238step0Labels = raw28238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28238 raw28238Labels permutation434 hz
    mixedMoment B raw28238step0 raw28238step0Labels = mixedMoment B raw28238step1 raw28238step1Labels := by
      have ha : raw28238step1 = (fun i j => raw28238step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28238step1 raw28238step0; decide +kernel
      have hl : raw28238step1Labels = raw28238step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28238step0 raw28238step0Labels permutation32 permutation3
    mixedMoment B raw28238step1 raw28238step1Labels = mixedMoment B raw28238step2 raw28238step2Labels := by
      have ha : raw28238step2 = raw28238step1 := by apply Matrix.ext; unfold raw28238step2 raw28238step1; decide +kernel
      have hl : raw28238step1Labels = labelEmbedding6 ∘ raw28238step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28238step1 raw28238step1Labels raw28238step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4517 node4517Labels := by rfl

def raw28239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28239 raw28239Labels = mixedMoment B node4982 node4982Labels := by
  calc
    mixedMoment B raw28239 raw28239Labels = mixedMoment B raw28239step0 raw28239step0Labels := by
      have hz : ∀ j, raw28239 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28239step0 = (fun i j => raw28239 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28239step0 raw28239; decide +kernel
      have hl : raw28239step0Labels = raw28239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28239 raw28239Labels permutation434 hz
    _ = mixedMoment B node4982 node4982Labels := by rfl

def raw28240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28240step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28240step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28240step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28240step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28240step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28240step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28240 raw28240Labels = mixedMoment B node5027 node5027Labels := by
  calc
    mixedMoment B raw28240 raw28240Labels = mixedMoment B raw28240step0 raw28240step0Labels := by
      have ha : raw28240step0 = (fun i j => raw28240 (permutation646 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28240step0 raw28240; decide +kernel
      have hl : raw28240step0Labels = raw28240Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28240 raw28240Labels permutation646 permutation3
    mixedMoment B raw28240step0 raw28240step0Labels = mixedMoment B raw28240step1 raw28240step1Labels := by
      have ha : raw28240step1 = -raw28240step0 := by apply Matrix.ext; change ∀ i j, raw28240step1 i j = -(raw28240step0 i j); unfold raw28240step1 raw28240step0; decide +kernel
      have hl : raw28240step1Labels = raw28240step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28240step1 raw28240step1Labels = mixedMoment B raw28240step2 raw28240step2Labels := by
      have ha : raw28240step2 = raw28240step1 := by apply Matrix.ext; unfold raw28240step2 raw28240step1; decide +kernel
      have hl : raw28240step1Labels = labelEmbedding6 ∘ raw28240step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28240step1 raw28240step1Labels raw28240step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5027 node5027Labels := by rfl

def raw28241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw28241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![3, -2, -1]]
def raw28241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28241step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28241step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28241step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28241step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28241step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw28241step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28241step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw28241step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28241 raw28241Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw28241 raw28241Labels = mixedMoment B raw28241step0 raw28241step0Labels := by
      have hz : ∀ j, raw28241 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28241step0 = (fun i j => raw28241 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28241step0 raw28241; decide +kernel
      have hl : raw28241step0Labels = raw28241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28241 raw28241Labels permutation520 hz
    mixedMoment B raw28241step0 raw28241step0Labels = mixedMoment B raw28241step1 raw28241step1Labels := by
      have hz : ∀ j, raw28241step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28241step1 = (fun i j => raw28241step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28241step1 raw28241step0; decide +kernel
      have hl : raw28241step1Labels = raw28241step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28241step0 raw28241step0Labels permutation104 hz
    mixedMoment B raw28241step1 raw28241step1Labels = mixedMoment B raw28241step2 raw28241step2Labels := by
      have ha : raw28241step2 = (fun i j => raw28241step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28241step2 raw28241step1; decide +kernel
      have hl : raw28241step2Labels = raw28241step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28241step1 raw28241step1Labels permutation31 permutation3
    mixedMoment B raw28241step2 raw28241step2Labels = mixedMoment B raw28241step3 raw28241step3Labels := by
      have ha : raw28241step3 = -raw28241step2 := by apply Matrix.ext; change ∀ i j, raw28241step3 i j = -(raw28241step2 i j); unfold raw28241step3 raw28241step2; decide +kernel
      have hl : raw28241step3Labels = raw28241step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28241step3 raw28241step3Labels = mixedMoment B raw28241step4 raw28241step4Labels := by
      have ha : raw28241step4 = raw28241step3 := by apply Matrix.ext; unfold raw28241step4 raw28241step3; decide +kernel
      have hl : raw28241step3Labels = labelEmbedding6 ∘ raw28241step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28241step3 raw28241step3Labels raw28241step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5109 node5109Labels := by rfl

def raw28242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28242step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28242step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28242step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28242 raw28242Labels = mixedMoment B node4517 node4517Labels := by
  calc
    mixedMoment B raw28242 raw28242Labels = mixedMoment B raw28242step0 raw28242step0Labels := by
      have hz : ∀ j, raw28242 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28242step0 = (fun i j => raw28242 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28242step0 raw28242; decide +kernel
      have hl : raw28242step0Labels = raw28242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28242 raw28242Labels permutation346 hz
    mixedMoment B raw28242step0 raw28242step0Labels = mixedMoment B raw28242step1 raw28242step1Labels := by
      have ha : raw28242step1 = (fun i j => raw28242step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28242step1 raw28242step0; decide +kernel
      have hl : raw28242step1Labels = raw28242step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28242step0 raw28242step0Labels permutation32 permutation3
    mixedMoment B raw28242step1 raw28242step1Labels = mixedMoment B raw28242step2 raw28242step2Labels := by
      have ha : raw28242step2 = raw28242step1 := by apply Matrix.ext; unfold raw28242step2 raw28242step1; decide +kernel
      have hl : raw28242step1Labels = labelEmbedding6 ∘ raw28242step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28242step1 raw28242step1Labels raw28242step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4517 node4517Labels := by rfl

def raw28243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28243 raw28243Labels = mixedMoment B node4982 node4982Labels := by
  calc
    mixedMoment B raw28243 raw28243Labels = mixedMoment B raw28243step0 raw28243step0Labels := by
      have hz : ∀ j, raw28243 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28243step0 = (fun i j => raw28243 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28243step0 raw28243; decide +kernel
      have hl : raw28243step0Labels = raw28243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28243 raw28243Labels permutation346 hz
    _ = mixedMoment B node4982 node4982Labels := by rfl

def raw28244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28244step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28244step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28244step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28244step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28244step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28244step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28244 raw28244Labels = mixedMoment B node5027 node5027Labels := by
  calc
    mixedMoment B raw28244 raw28244Labels = mixedMoment B raw28244step0 raw28244step0Labels := by
      have ha : raw28244step0 = (fun i j => raw28244 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28244step0 raw28244; decide +kernel
      have hl : raw28244step0Labels = raw28244Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28244 raw28244Labels permutation664 permutation3
    mixedMoment B raw28244step0 raw28244step0Labels = mixedMoment B raw28244step1 raw28244step1Labels := by
      have ha : raw28244step1 = -raw28244step0 := by apply Matrix.ext; change ∀ i j, raw28244step1 i j = -(raw28244step0 i j); unfold raw28244step1 raw28244step0; decide +kernel
      have hl : raw28244step1Labels = raw28244step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28244step1 raw28244step1Labels = mixedMoment B raw28244step2 raw28244step2Labels := by
      have ha : raw28244step2 = raw28244step1 := by apply Matrix.ext; unfold raw28244step2 raw28244step1; decide +kernel
      have hl : raw28244step1Labels = labelEmbedding6 ∘ raw28244step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28244step1 raw28244step1Labels raw28244step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5027 node5027Labels := by rfl

def raw28245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -2, -1]]
def raw28245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28245step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28245step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28245step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw28245step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28245step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw28245step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28245 raw28245Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw28245 raw28245Labels = mixedMoment B raw28245step0 raw28245step0Labels := by
      have hz : ∀ j, raw28245 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28245step0 = (fun i j => raw28245 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28245step0 raw28245; decide +kernel
      have hl : raw28245step0Labels = raw28245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28245 raw28245Labels permutation520 hz
    mixedMoment B raw28245step0 raw28245step0Labels = mixedMoment B raw28245step1 raw28245step1Labels := by
      have hz : ∀ j, raw28245step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28245step1 = (fun i j => raw28245step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28245step1 raw28245step0; decide +kernel
      have hl : raw28245step1Labels = raw28245step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28245step0 raw28245step0Labels permutation80 hz
    mixedMoment B raw28245step1 raw28245step1Labels = mixedMoment B raw28245step2 raw28245step2Labels := by
      have ha : raw28245step2 = (fun i j => raw28245step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28245step2 raw28245step1; decide +kernel
      have hl : raw28245step2Labels = raw28245step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28245step1 raw28245step1Labels permutation31 permutation3
    mixedMoment B raw28245step2 raw28245step2Labels = mixedMoment B raw28245step3 raw28245step3Labels := by
      have ha : raw28245step3 = -raw28245step2 := by apply Matrix.ext; change ∀ i j, raw28245step3 i j = -(raw28245step2 i j); unfold raw28245step3 raw28245step2; decide +kernel
      have hl : raw28245step3Labels = raw28245step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28245step3 raw28245step3Labels = mixedMoment B raw28245step4 raw28245step4Labels := by
      have ha : raw28245step4 = raw28245step3 := by apply Matrix.ext; unfold raw28245step4 raw28245step3; decide +kernel
      have hl : raw28245step3Labels = labelEmbedding6 ∘ raw28245step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28245step3 raw28245step3Labels raw28245step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5109 node5109Labels := by rfl

def raw28246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -2, -1]]
def raw28246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![3, -2, -1]]
def raw28246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28246step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28246step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw28246step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28246step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw28246step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28246 raw28246Labels = mixedMoment B node4520 node4520Labels := by
  calc
    mixedMoment B raw28246 raw28246Labels = mixedMoment B raw28246step0 raw28246step0Labels := by
      have hz : ∀ j, raw28246 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28246step0 = (fun i j => raw28246 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28246step0 raw28246; decide +kernel
      have hl : raw28246step0Labels = raw28246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28246 raw28246Labels permutation434 hz
    mixedMoment B raw28246step0 raw28246step0Labels = mixedMoment B raw28246step1 raw28246step1Labels := by
      have hz : ∀ j, raw28246step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28246step1 = (fun i j => raw28246step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28246step1 raw28246step0; decide +kernel
      have hl : raw28246step1Labels = raw28246step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28246step0 raw28246step0Labels permutation80 hz
    mixedMoment B raw28246step1 raw28246step1Labels = mixedMoment B raw28246step2 raw28246step2Labels := by
      have ha : raw28246step2 = (fun i j => raw28246step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28246step2 raw28246step1; decide +kernel
      have hl : raw28246step2Labels = raw28246step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28246step1 raw28246step1Labels permutation8 permutation3
    mixedMoment B raw28246step2 raw28246step2Labels = mixedMoment B raw28246step3 raw28246step3Labels := by
      have ha : raw28246step3 = raw28246step2 := by apply Matrix.ext; unfold raw28246step3 raw28246step2; decide +kernel
      have hl : raw28246step2Labels = labelEmbedding6 ∘ raw28246step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28246step2 raw28246step2Labels raw28246step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4520 node4520Labels := by rfl

def raw28247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -2, -1]]
def raw28247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -2, 0], ![3, -2, -1]]
def raw28247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28247step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28247step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-2, -1, 3], ![-3, 2, 1]]
def raw28247step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28247step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 1, -3], ![3, -2, -1]]
def raw28247step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28247step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 1, -3], ![3, -2, -1]]
def raw28247step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28247 raw28247Labels = mixedMoment B node4925 node4925Labels := by
  calc
    mixedMoment B raw28247 raw28247Labels = mixedMoment B raw28247step0 raw28247step0Labels := by
      have hz : ∀ j, raw28247 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28247step0 = (fun i j => raw28247 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28247step0 raw28247; decide +kernel
      have hl : raw28247step0Labels = raw28247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28247 raw28247Labels permutation434 hz
    mixedMoment B raw28247step0 raw28247step0Labels = mixedMoment B raw28247step1 raw28247step1Labels := by
      have hz : ∀ j, raw28247step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28247step1 = (fun i j => raw28247step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28247step1 raw28247step0; decide +kernel
      have hl : raw28247step1Labels = raw28247step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28247step0 raw28247step0Labels permutation80 hz
    mixedMoment B raw28247step1 raw28247step1Labels = mixedMoment B raw28247step2 raw28247step2Labels := by
      have ha : raw28247step2 = (fun i j => raw28247step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28247step2 raw28247step1; decide +kernel
      have hl : raw28247step2Labels = raw28247step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28247step1 raw28247step1Labels permutation31 permutation3
    mixedMoment B raw28247step2 raw28247step2Labels = mixedMoment B raw28247step3 raw28247step3Labels := by
      have ha : raw28247step3 = -raw28247step2 := by apply Matrix.ext; change ∀ i j, raw28247step3 i j = -(raw28247step2 i j); unfold raw28247step3 raw28247step2; decide +kernel
      have hl : raw28247step3Labels = raw28247step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28247step3 raw28247step3Labels = mixedMoment B raw28247step4 raw28247step4Labels := by
      have ha : raw28247step4 = raw28247step3 := by apply Matrix.ext; unfold raw28247step4 raw28247step3; decide +kernel
      have hl : raw28247step3Labels = labelEmbedding6 ∘ raw28247step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28247step3 raw28247step3Labels raw28247step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4925 node4925Labels := by rfl

def raw28248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -2, -1]]
def raw28248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![3, -2, -1]]
def raw28248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28248step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28248step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28248step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28248step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28248step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28248 raw28248Labels = mixedMoment B node4919 node4919Labels := by
  calc
    mixedMoment B raw28248 raw28248Labels = mixedMoment B raw28248step0 raw28248step0Labels := by
      have hz : ∀ j, raw28248 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28248step0 = (fun i j => raw28248 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28248step0 raw28248; decide +kernel
      have hl : raw28248step0Labels = raw28248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28248 raw28248Labels permutation434 hz
    mixedMoment B raw28248step0 raw28248step0Labels = mixedMoment B raw28248step1 raw28248step1Labels := by
      have ha : raw28248step1 = (fun i j => raw28248step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28248step1 raw28248step0; decide +kernel
      have hl : raw28248step1Labels = raw28248step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28248step0 raw28248step0Labels permutation151 permutation3
    mixedMoment B raw28248step1 raw28248step1Labels = mixedMoment B raw28248step2 raw28248step2Labels := by
      have ha : raw28248step2 = -raw28248step1 := by apply Matrix.ext; change ∀ i j, raw28248step2 i j = -(raw28248step1 i j); unfold raw28248step2 raw28248step1; decide +kernel
      have hl : raw28248step2Labels = raw28248step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28248step2 raw28248step2Labels = mixedMoment B raw28248step3 raw28248step3Labels := by
      have ha : raw28248step3 = raw28248step2 := by apply Matrix.ext; unfold raw28248step3 raw28248step2; decide +kernel
      have hl : raw28248step2Labels = labelEmbedding6 ∘ raw28248step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28248step2 raw28248step2Labels raw28248step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4919 node4919Labels := by rfl

def raw28249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -2, -1]]
def raw28249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![3, -2, -1]]
def raw28249step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28249step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28249step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28249step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28249step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28249step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28249 raw28249Labels = mixedMoment B node4919 node4919Labels := by
  calc
    mixedMoment B raw28249 raw28249Labels = mixedMoment B raw28249step0 raw28249step0Labels := by
      have hz : ∀ j, raw28249 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28249step0 = (fun i j => raw28249 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28249step0 raw28249; decide +kernel
      have hl : raw28249step0Labels = raw28249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28249 raw28249Labels permutation346 hz
    mixedMoment B raw28249step0 raw28249step0Labels = mixedMoment B raw28249step1 raw28249step1Labels := by
      have ha : raw28249step1 = (fun i j => raw28249step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28249step1 raw28249step0; decide +kernel
      have hl : raw28249step1Labels = raw28249step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28249step0 raw28249step0Labels permutation151 permutation3
    mixedMoment B raw28249step1 raw28249step1Labels = mixedMoment B raw28249step2 raw28249step2Labels := by
      have ha : raw28249step2 = -raw28249step1 := by apply Matrix.ext; change ∀ i j, raw28249step2 i j = -(raw28249step1 i j); unfold raw28249step2 raw28249step1; decide +kernel
      have hl : raw28249step2Labels = raw28249step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28249step2 raw28249step2Labels = mixedMoment B raw28249step3 raw28249step3Labels := by
      have ha : raw28249step3 = raw28249step2 := by apply Matrix.ext; unfold raw28249step3 raw28249step2; decide +kernel
      have hl : raw28249step2Labels = labelEmbedding6 ∘ raw28249step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28249step2 raw28249step2Labels raw28249step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4919 node4919Labels := by rfl

def raw28250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -3, -1]]
def raw28250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![4, -3, -1]]
def raw28250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28250step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28250step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, -1, 2], ![-4, 2, 2]]
def raw28250step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28250step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw28250step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28250step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw28250step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28250 raw28250Labels = mixedMoment B node4315 node4315Labels := by
  calc
    mixedMoment B raw28250 raw28250Labels = mixedMoment B raw28250step0 raw28250step0Labels := by
      have hz : ∀ j, raw28250 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28250step0 = (fun i j => raw28250 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28250step0 raw28250; decide +kernel
      have hl : raw28250step0Labels = raw28250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28250 raw28250Labels permutation434 hz
    mixedMoment B raw28250step0 raw28250step0Labels = mixedMoment B raw28250step1 raw28250step1Labels := by
      have hz : ∀ j, raw28250step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28250step1 = (fun i j => raw28250step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28250step1 raw28250step0; decide +kernel
      have hl : raw28250step1Labels = raw28250step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28250step0 raw28250step0Labels permutation80 hz
    mixedMoment B raw28250step1 raw28250step1Labels = mixedMoment B raw28250step2 raw28250step2Labels := by
      have ha : raw28250step2 = (fun i j => raw28250step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28250step2 raw28250step1; decide +kernel
      have hl : raw28250step2Labels = raw28250step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28250step1 raw28250step1Labels permutation31 permutation3
    mixedMoment B raw28250step2 raw28250step2Labels = mixedMoment B raw28250step3 raw28250step3Labels := by
      have ha : raw28250step3 = -raw28250step2 := by apply Matrix.ext; change ∀ i j, raw28250step3 i j = -(raw28250step2 i j); unfold raw28250step3 raw28250step2; decide +kernel
      have hl : raw28250step3Labels = raw28250step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28250step3 raw28250step3Labels = mixedMoment B raw28250step4 raw28250step4Labels := by
      have ha : raw28250step4 = raw28250step3 := by apply Matrix.ext; unfold raw28250step4 raw28250step3; decide +kernel
      have hl : raw28250step3Labels = labelEmbedding6 ∘ raw28250step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28250step3 raw28250step3Labels raw28250step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4315 node4315Labels := by rfl

def raw28251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -3, -1]]
def raw28251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![4, -3, -1]]
def raw28251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28251step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28251step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28251step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-2, -1, 3], ![-3, 2, 1]]
def raw28251step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28251step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw28251step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28251step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw28251step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28251 raw28251Labels = mixedMoment B node4319 node4319Labels := by
  calc
    mixedMoment B raw28251 raw28251Labels = mixedMoment B raw28251step0 raw28251step0Labels := by
      have hz : ∀ j, raw28251 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28251step0 = (fun i j => raw28251 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28251step0 raw28251; decide +kernel
      have hl : raw28251step0Labels = raw28251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28251 raw28251Labels permutation434 hz
    mixedMoment B raw28251step0 raw28251step0Labels = mixedMoment B raw28251step1 raw28251step1Labels := by
      have hz : ∀ j, raw28251step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28251step1 = (fun i j => raw28251step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28251step1 raw28251step0; decide +kernel
      have hl : raw28251step1Labels = raw28251step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28251step0 raw28251step0Labels permutation80 hz
    mixedMoment B raw28251step1 raw28251step1Labels = mixedMoment B raw28251step2 raw28251step2Labels := by
      have ha : raw28251step2 = (fun i j => raw28251step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28251step2 raw28251step1; decide +kernel
      have hl : raw28251step2Labels = raw28251step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28251step1 raw28251step1Labels permutation31 permutation3
    mixedMoment B raw28251step2 raw28251step2Labels = mixedMoment B raw28251step3 raw28251step3Labels := by
      have ha : raw28251step3 = -raw28251step2 := by apply Matrix.ext; change ∀ i j, raw28251step3 i j = -(raw28251step2 i j); unfold raw28251step3 raw28251step2; decide +kernel
      have hl : raw28251step3Labels = raw28251step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28251step3 raw28251step3Labels = mixedMoment B raw28251step4 raw28251step4Labels := by
      have ha : raw28251step4 = raw28251step3 := by apply Matrix.ext; unfold raw28251step4 raw28251step3; decide +kernel
      have hl : raw28251step3Labels = labelEmbedding6 ∘ raw28251step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28251step3 raw28251step3Labels raw28251step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4319 node4319Labels := by rfl

def raw28252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -3, -1]]
def raw28252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![4, -3, -1]]
def raw28252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28252step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28252step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28252step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28252step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28252 raw28252Labels = mixedMoment B node4309 node4309Labels := by
  calc
    mixedMoment B raw28252 raw28252Labels = mixedMoment B raw28252step0 raw28252step0Labels := by
      have hz : ∀ j, raw28252 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28252step0 = (fun i j => raw28252 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28252step0 raw28252; decide +kernel
      have hl : raw28252step0Labels = raw28252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28252 raw28252Labels permutation434 hz
    mixedMoment B raw28252step0 raw28252step0Labels = mixedMoment B raw28252step1 raw28252step1Labels := by
      have ha : raw28252step1 = (fun i j => raw28252step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28252step1 raw28252step0; decide +kernel
      have hl : raw28252step1Labels = raw28252step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28252step0 raw28252step0Labels permutation151 permutation3
    mixedMoment B raw28252step1 raw28252step1Labels = mixedMoment B raw28252step2 raw28252step2Labels := by
      have ha : raw28252step2 = -raw28252step1 := by apply Matrix.ext; change ∀ i j, raw28252step2 i j = -(raw28252step1 i j); unfold raw28252step2 raw28252step1; decide +kernel
      have hl : raw28252step2Labels = raw28252step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28252step2 raw28252step2Labels = mixedMoment B raw28252step3 raw28252step3Labels := by
      have ha : raw28252step3 = raw28252step2 := by apply Matrix.ext; unfold raw28252step3 raw28252step2; decide +kernel
      have hl : raw28252step2Labels = labelEmbedding6 ∘ raw28252step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28252step2 raw28252step2Labels raw28252step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4309 node4309Labels := by rfl

def raw28253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -3, -1]]
def raw28253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![4, -3, -1]]
def raw28253step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28253step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28253step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28253step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28253step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28253 raw28253Labels = mixedMoment B node4309 node4309Labels := by
  calc
    mixedMoment B raw28253 raw28253Labels = mixedMoment B raw28253step0 raw28253step0Labels := by
      have hz : ∀ j, raw28253 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28253step0 = (fun i j => raw28253 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28253step0 raw28253; decide +kernel
      have hl : raw28253step0Labels = raw28253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28253 raw28253Labels permutation346 hz
    mixedMoment B raw28253step0 raw28253step0Labels = mixedMoment B raw28253step1 raw28253step1Labels := by
      have ha : raw28253step1 = (fun i j => raw28253step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28253step1 raw28253step0; decide +kernel
      have hl : raw28253step1Labels = raw28253step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28253step0 raw28253step0Labels permutation151 permutation3
    mixedMoment B raw28253step1 raw28253step1Labels = mixedMoment B raw28253step2 raw28253step2Labels := by
      have ha : raw28253step2 = -raw28253step1 := by apply Matrix.ext; change ∀ i j, raw28253step2 i j = -(raw28253step1 i j); unfold raw28253step2 raw28253step1; decide +kernel
      have hl : raw28253step2Labels = raw28253step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28253step2 raw28253step2Labels = mixedMoment B raw28253step3 raw28253step3Labels := by
      have ha : raw28253step3 = raw28253step2 := by apply Matrix.ext; unfold raw28253step3 raw28253step2; decide +kernel
      have hl : raw28253step2Labels = labelEmbedding6 ∘ raw28253step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28253step2 raw28253step2Labels raw28253step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4309 node4309Labels := by rfl

def raw28254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -3, -1]]
def raw28254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![4, -3, -1]]
def raw28254step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28254step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![4, -3, -1]]
def raw28254step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28254step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![4, -3, -1]]
def raw28254step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28254step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, -1, 2], ![-3, 2, 1]]
def raw28254step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28254step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw28254step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28254step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw28254step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28254 raw28254Labels = mixedMoment B node4507 node4507Labels := by
  calc
    mixedMoment B raw28254 raw28254Labels = mixedMoment B raw28254step0 raw28254step0Labels := by
      have hz : ∀ j, raw28254 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28254step0 = (fun i j => raw28254 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28254step0 raw28254; decide +kernel
      have hl : raw28254step0Labels = raw28254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28254 raw28254Labels permutation520 hz
    mixedMoment B raw28254step0 raw28254step0Labels = mixedMoment B raw28254step1 raw28254step1Labels := by
      have hz : ∀ j, raw28254step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28254step1 = (fun i j => raw28254step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28254step1 raw28254step0; decide +kernel
      have hl : raw28254step1Labels = raw28254step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28254step0 raw28254step0Labels permutation104 hz
    mixedMoment B raw28254step1 raw28254step1Labels = mixedMoment B raw28254step2 raw28254step2Labels := by
      have hz : ∀ j, raw28254step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw28254step2 = (fun i j => raw28254step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw28254step2 raw28254step1; decide +kernel
      have hl : raw28254step2Labels = raw28254step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28254step1 raw28254step1Labels permutation20 hz
    mixedMoment B raw28254step2 raw28254step2Labels = mixedMoment B raw28254step3 raw28254step3Labels := by
      have ha : raw28254step3 = (fun i j => raw28254step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28254step3 raw28254step2; decide +kernel
      have hl : raw28254step3Labels = raw28254step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28254step2 raw28254step2Labels permutation7 permutation3
    mixedMoment B raw28254step3 raw28254step3Labels = mixedMoment B raw28254step4 raw28254step4Labels := by
      have ha : raw28254step4 = -raw28254step3 := by apply Matrix.ext; change ∀ i j, raw28254step4 i j = -(raw28254step3 i j); unfold raw28254step4 raw28254step3; decide +kernel
      have hl : raw28254step4Labels = raw28254step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw28254step4 raw28254step4Labels = mixedMoment B raw28254step5 raw28254step5Labels := by
      have ha : raw28254step5 = raw28254step4 := by apply Matrix.ext; unfold raw28254step5 raw28254step4; decide +kernel
      have hl : raw28254step4Labels = labelEmbedding6 ∘ raw28254step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28254step4 raw28254step4Labels raw28254step5Labels labelEmbedding6 hl
    _ = mixedMoment B node4507 node4507Labels := by rfl

def raw28255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw28255Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw28255step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28255step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw28255step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28255step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw28255step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28255step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw28255step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28255 raw28255Labels = mixedMoment B node3987 node3987Labels := by
  calc
    mixedMoment B raw28255 raw28255Labels = mixedMoment B raw28255step0 raw28255step0Labels := by
      have hz : ∀ j, raw28255 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28255step0 = (fun i j => raw28255 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28255step0 raw28255; decide +kernel
      have hl : raw28255step0Labels = raw28255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28255 raw28255Labels permutation434 hz
    mixedMoment B raw28255step0 raw28255step0Labels = mixedMoment B raw28255step1 raw28255step1Labels := by
      have hz : ∀ j, raw28255step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28255step1 = (fun i j => raw28255step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28255step1 raw28255step0; decide +kernel
      have hl : raw28255step1Labels = raw28255step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28255step0 raw28255step0Labels permutation80 hz
    mixedMoment B raw28255step1 raw28255step1Labels = mixedMoment B raw28255step2 raw28255step2Labels := by
      have ha : raw28255step2 = (fun i j => raw28255step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28255step2 raw28255step1; decide +kernel
      have hl : raw28255step2Labels = raw28255step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28255step1 raw28255step1Labels permutation31 permutation3
    mixedMoment B raw28255step2 raw28255step2Labels = mixedMoment B raw28255step3 raw28255step3Labels := by
      have ha : raw28255step3 = -raw28255step2 := by apply Matrix.ext; change ∀ i j, raw28255step3 i j = -(raw28255step2 i j); unfold raw28255step3 raw28255step2; decide +kernel
      have hl : raw28255step3Labels = raw28255step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3987 node3987Labels := by rfl

def raw28256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28256Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28256step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28256step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28256step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28256step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw28256step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28256 raw28256Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw28256 raw28256Labels = mixedMoment B raw28256step0 raw28256step0Labels := by
      have hz : ∀ j, raw28256 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28256step0 = (fun i j => raw28256 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28256step0 raw28256; decide +kernel
      have hl : raw28256step0Labels = raw28256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28256 raw28256Labels permutation434 hz
    mixedMoment B raw28256step0 raw28256step0Labels = mixedMoment B raw28256step1 raw28256step1Labels := by
      have hz : ∀ j, raw28256step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28256step1 = (fun i j => raw28256step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28256step1 raw28256step0; decide +kernel
      have hl : raw28256step1Labels = raw28256step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28256step0 raw28256step0Labels permutation80 hz
    mixedMoment B raw28256step1 raw28256step1Labels = mixedMoment B raw28256step2 raw28256step2Labels := by
      have ha : raw28256step2 = (fun i j => raw28256step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28256step2 raw28256step1; decide +kernel
      have hl : raw28256step2Labels = raw28256step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28256step1 raw28256step1Labels permutation8 permutation3
    _ = mixedMoment B node1242 node1242Labels := by rfl

def raw28257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28257Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28257step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28257step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28257step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28257step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28257 raw28257Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw28257 raw28257Labels = mixedMoment B raw28257step0 raw28257step0Labels := by
      have hz : ∀ j, raw28257 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28257step0 = (fun i j => raw28257 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28257step0 raw28257; decide +kernel
      have hl : raw28257step0Labels = raw28257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28257 raw28257Labels permutation434 hz
    mixedMoment B raw28257step0 raw28257step0Labels = mixedMoment B raw28257step1 raw28257step1Labels := by
      have ha : raw28257step1 = (fun i j => raw28257step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28257step1 raw28257step0; decide +kernel
      have hl : raw28257step1Labels = raw28257step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28257step0 raw28257step0Labels permutation149 permutation3
    mixedMoment B raw28257step1 raw28257step1Labels = mixedMoment B raw28257step2 raw28257step2Labels := by
      have ha : raw28257step2 = -raw28257step1 := by apply Matrix.ext; change ∀ i j, raw28257step2 i j = -(raw28257step1 i j); unfold raw28257step2 raw28257step1; decide +kernel
      have hl : raw28257step2Labels = raw28257step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw28258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28258Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28258step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw28258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28258step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw28258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28258 raw28258Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw28258 raw28258Labels = mixedMoment B raw28258step0 raw28258step0Labels := by
      have hz : ∀ j, raw28258 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28258step0 = (fun i j => raw28258 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28258step0 raw28258; decide +kernel
      have hl : raw28258step0Labels = raw28258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28258 raw28258Labels permutation346 hz
    mixedMoment B raw28258step0 raw28258step0Labels = mixedMoment B raw28258step1 raw28258step1Labels := by
      have ha : raw28258step1 = (fun i j => raw28258step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28258step1 raw28258step0; decide +kernel
      have hl : raw28258step1Labels = raw28258step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28258step0 raw28258step0Labels permutation149 permutation3
    mixedMoment B raw28258step1 raw28258step1Labels = mixedMoment B raw28258step2 raw28258step2Labels := by
      have ha : raw28258step2 = -raw28258step1 := by apply Matrix.ext; change ∀ i j, raw28258step2 i j = -(raw28258step1 i j); unfold raw28258step2 raw28258step1; decide +kernel
      have hl : raw28258step2Labels = raw28258step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw28259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw28259Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw28259step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28259step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw28259step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28259step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw28259step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28259step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw28259step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28259step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw28259step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28259 raw28259Labels = mixedMoment B node2770 node2770Labels := by
  calc
    mixedMoment B raw28259 raw28259Labels = mixedMoment B raw28259step0 raw28259step0Labels := by
      have hz : ∀ j, raw28259 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28259step0 = (fun i j => raw28259 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28259step0 raw28259; decide +kernel
      have hl : raw28259step0Labels = raw28259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28259 raw28259Labels permutation520 hz
    mixedMoment B raw28259step0 raw28259step0Labels = mixedMoment B raw28259step1 raw28259step1Labels := by
      have hz : ∀ j, raw28259step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28259step1 = (fun i j => raw28259step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28259step1 raw28259step0; decide +kernel
      have hl : raw28259step1Labels = raw28259step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28259step0 raw28259step0Labels permutation104 hz
    mixedMoment B raw28259step1 raw28259step1Labels = mixedMoment B raw28259step2 raw28259step2Labels := by
      have hz : ∀ j, raw28259step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw28259step2 = (fun i j => raw28259step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw28259step2 raw28259step1; decide +kernel
      have hl : raw28259step2Labels = raw28259step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28259step1 raw28259step1Labels permutation20 hz
    mixedMoment B raw28259step2 raw28259step2Labels = mixedMoment B raw28259step3 raw28259step3Labels := by
      have ha : raw28259step3 = (fun i j => raw28259step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28259step3 raw28259step2; decide +kernel
      have hl : raw28259step3Labels = raw28259step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28259step2 raw28259step2Labels permutation7 permutation3
    mixedMoment B raw28259step3 raw28259step3Labels = mixedMoment B raw28259step4 raw28259step4Labels := by
      have ha : raw28259step4 = -raw28259step3 := by apply Matrix.ext; change ∀ i j, raw28259step4 i j = -(raw28259step3 i j); unfold raw28259step4 raw28259step3; decide +kernel
      have hl : raw28259step4Labels = raw28259step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2770 node2770Labels := by rfl

def raw28260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28260Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28260step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28260step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28260 raw28260Labels = mixedMoment B node1101 node1101Labels := by
  calc
    mixedMoment B raw28260 raw28260Labels = mixedMoment B raw28260step0 raw28260step0Labels := by
      have hz : ∀ j, raw28260 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28260step0 = (fun i j => raw28260 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28260step0 raw28260; decide +kernel
      have hl : raw28260step0Labels = raw28260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28260 raw28260Labels permutation434 hz
    mixedMoment B raw28260step0 raw28260step0Labels = mixedMoment B raw28260step1 raw28260step1Labels := by
      have ha : raw28260step1 = (fun i j => raw28260step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28260step1 raw28260step0; decide +kernel
      have hl : raw28260step1Labels = raw28260step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28260step0 raw28260step0Labels permutation32 permutation3
    _ = mixedMoment B node1101 node1101Labels := by rfl

def raw28261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28261Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28261step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, 0, -1], ![-2, -1, 3], ![-3, 2, 1]]
def raw28261step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28261step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw28261step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28261 raw28261Labels = mixedMoment B node2421 node2421Labels := by
  calc
    mixedMoment B raw28261 raw28261Labels = mixedMoment B raw28261step0 raw28261step0Labels := by
      have hz : ∀ j, raw28261 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28261step0 = (fun i j => raw28261 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28261step0 raw28261; decide +kernel
      have hl : raw28261step0Labels = raw28261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28261 raw28261Labels permutation434 hz
    mixedMoment B raw28261step0 raw28261step0Labels = mixedMoment B raw28261step1 raw28261step1Labels := by
      have ha : raw28261step1 = (fun i j => raw28261step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28261step1 raw28261step0; decide +kernel
      have hl : raw28261step1Labels = raw28261step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28261step0 raw28261step0Labels permutation145 permutation3
    mixedMoment B raw28261step1 raw28261step1Labels = mixedMoment B raw28261step2 raw28261step2Labels := by
      have ha : raw28261step2 = -raw28261step1 := by apply Matrix.ext; change ∀ i j, raw28261step2 i j = -(raw28261step1 i j); unfold raw28261step2 raw28261step1; decide +kernel
      have hl : raw28261step2Labels = raw28261step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2421 node2421Labels := by rfl

def raw28262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28262Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28262step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28262step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28262step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28262 raw28262Labels = mixedMoment B node2416 node2416Labels := by
  calc
    mixedMoment B raw28262 raw28262Labels = mixedMoment B raw28262step0 raw28262step0Labels := by
      have ha : raw28262step0 = (fun i j => raw28262 (permutation646 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28262step0 raw28262; decide +kernel
      have hl : raw28262step0Labels = raw28262Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28262 raw28262Labels permutation646 permutation3
    mixedMoment B raw28262step0 raw28262step0Labels = mixedMoment B raw28262step1 raw28262step1Labels := by
      have ha : raw28262step1 = -raw28262step0 := by apply Matrix.ext; change ∀ i j, raw28262step1 i j = -(raw28262step0 i j); unfold raw28262step1 raw28262step0; decide +kernel
      have hl : raw28262step1Labels = raw28262step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2416 node2416Labels := by rfl

def raw28263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw28263Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![3, -2, -1]]
def raw28263step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28263step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28263step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28263step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28263step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw28263step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28263 raw28263Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw28263 raw28263Labels = mixedMoment B raw28263step0 raw28263step0Labels := by
      have hz : ∀ j, raw28263 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28263step0 = (fun i j => raw28263 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28263step0 raw28263; decide +kernel
      have hl : raw28263step0Labels = raw28263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28263 raw28263Labels permutation520 hz
    mixedMoment B raw28263step0 raw28263step0Labels = mixedMoment B raw28263step1 raw28263step1Labels := by
      have hz : ∀ j, raw28263step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28263step1 = (fun i j => raw28263step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28263step1 raw28263step0; decide +kernel
      have hl : raw28263step1Labels = raw28263step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28263step0 raw28263step0Labels permutation104 hz
    mixedMoment B raw28263step1 raw28263step1Labels = mixedMoment B raw28263step2 raw28263step2Labels := by
      have ha : raw28263step2 = (fun i j => raw28263step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28263step2 raw28263step1; decide +kernel
      have hl : raw28263step2Labels = raw28263step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28263step1 raw28263step1Labels permutation31 permutation3
    mixedMoment B raw28263step2 raw28263step2Labels = mixedMoment B raw28263step3 raw28263step3Labels := by
      have ha : raw28263step3 = -raw28263step2 := by apply Matrix.ext; change ∀ i j, raw28263step3 i j = -(raw28263step2 i j); unfold raw28263step3 raw28263step2; decide +kernel
      have hl : raw28263step3Labels = raw28263step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2519 node2519Labels := by rfl

def raw28264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28264Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28264step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw28264step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28264 raw28264Labels = mixedMoment B node1101 node1101Labels := by
  calc
    mixedMoment B raw28264 raw28264Labels = mixedMoment B raw28264step0 raw28264step0Labels := by
      have hz : ∀ j, raw28264 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28264step0 = (fun i j => raw28264 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28264step0 raw28264; decide +kernel
      have hl : raw28264step0Labels = raw28264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28264 raw28264Labels permutation346 hz
    mixedMoment B raw28264step0 raw28264step0Labels = mixedMoment B raw28264step1 raw28264step1Labels := by
      have ha : raw28264step1 = (fun i j => raw28264step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28264step1 raw28264step0; decide +kernel
      have hl : raw28264step1Labels = raw28264step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28264step0 raw28264step0Labels permutation32 permutation3
    _ = mixedMoment B node1101 node1101Labels := by rfl

def raw28265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28265Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28265step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, 0, -1], ![-2, -1, 3], ![-3, 2, 1]]
def raw28265step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28265step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw28265step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28265 raw28265Labels = mixedMoment B node2421 node2421Labels := by
  calc
    mixedMoment B raw28265 raw28265Labels = mixedMoment B raw28265step0 raw28265step0Labels := by
      have hz : ∀ j, raw28265 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28265step0 = (fun i j => raw28265 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28265step0 raw28265; decide +kernel
      have hl : raw28265step0Labels = raw28265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28265 raw28265Labels permutation346 hz
    mixedMoment B raw28265step0 raw28265step0Labels = mixedMoment B raw28265step1 raw28265step1Labels := by
      have ha : raw28265step1 = (fun i j => raw28265step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28265step1 raw28265step0; decide +kernel
      have hl : raw28265step1Labels = raw28265step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28265step0 raw28265step0Labels permutation145 permutation3
    mixedMoment B raw28265step1 raw28265step1Labels = mixedMoment B raw28265step2 raw28265step2Labels := by
      have ha : raw28265step2 = -raw28265step1 := by apply Matrix.ext; change ∀ i j, raw28265step2 i j = -(raw28265step1 i j); unfold raw28265step2 raw28265step1; decide +kernel
      have hl : raw28265step2Labels = raw28265step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2421 node2421Labels := by rfl

def raw28266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28266Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28266step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28266step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28266step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28266 raw28266Labels = mixedMoment B node2416 node2416Labels := by
  calc
    mixedMoment B raw28266 raw28266Labels = mixedMoment B raw28266step0 raw28266step0Labels := by
      have ha : raw28266step0 = (fun i j => raw28266 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28266step0 raw28266; decide +kernel
      have hl : raw28266step0Labels = raw28266Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28266 raw28266Labels permutation664 permutation3
    mixedMoment B raw28266step0 raw28266step0Labels = mixedMoment B raw28266step1 raw28266step1Labels := by
      have ha : raw28266step1 = -raw28266step0 := by apply Matrix.ext; change ∀ i j, raw28266step1 i j = -(raw28266step0 i j); unfold raw28266step1 raw28266step0; decide +kernel
      have hl : raw28266step1Labels = raw28266step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2416 node2416Labels := by rfl

def raw28267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -2, -1]]
def raw28267Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw28267step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28267step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw28267step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28267step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28267step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28267step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw28267step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28267 raw28267Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw28267 raw28267Labels = mixedMoment B raw28267step0 raw28267step0Labels := by
      have hz : ∀ j, raw28267 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28267step0 = (fun i j => raw28267 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28267step0 raw28267; decide +kernel
      have hl : raw28267step0Labels = raw28267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28267 raw28267Labels permutation520 hz
    mixedMoment B raw28267step0 raw28267step0Labels = mixedMoment B raw28267step1 raw28267step1Labels := by
      have hz : ∀ j, raw28267step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28267step1 = (fun i j => raw28267step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28267step1 raw28267step0; decide +kernel
      have hl : raw28267step1Labels = raw28267step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28267step0 raw28267step0Labels permutation80 hz
    mixedMoment B raw28267step1 raw28267step1Labels = mixedMoment B raw28267step2 raw28267step2Labels := by
      have ha : raw28267step2 = (fun i j => raw28267step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28267step2 raw28267step1; decide +kernel
      have hl : raw28267step2Labels = raw28267step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28267step1 raw28267step1Labels permutation31 permutation3
    mixedMoment B raw28267step2 raw28267step2Labels = mixedMoment B raw28267step3 raw28267step3Labels := by
      have ha : raw28267step3 = -raw28267step2 := by apply Matrix.ext; change ∀ i j, raw28267step3 i j = -(raw28267step2 i j); unfold raw28267step3 raw28267step2; decide +kernel
      have hl : raw28267step3Labels = raw28267step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2519 node2519Labels := by rfl

def raw28268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -2, -1]]
def raw28268Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![3, -2, -1]]
def raw28268step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28268step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28268step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28268step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw28268step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28268 raw28268Labels = mixedMoment B node1104 node1104Labels := by
  calc
    mixedMoment B raw28268 raw28268Labels = mixedMoment B raw28268step0 raw28268step0Labels := by
      have hz : ∀ j, raw28268 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28268step0 = (fun i j => raw28268 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28268step0 raw28268; decide +kernel
      have hl : raw28268step0Labels = raw28268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28268 raw28268Labels permutation434 hz
    mixedMoment B raw28268step0 raw28268step0Labels = mixedMoment B raw28268step1 raw28268step1Labels := by
      have hz : ∀ j, raw28268step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28268step1 = (fun i j => raw28268step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28268step1 raw28268step0; decide +kernel
      have hl : raw28268step1Labels = raw28268step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28268step0 raw28268step0Labels permutation80 hz
    mixedMoment B raw28268step1 raw28268step1Labels = mixedMoment B raw28268step2 raw28268step2Labels := by
      have ha : raw28268step2 = (fun i j => raw28268step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28268step2 raw28268step1; decide +kernel
      have hl : raw28268step2Labels = raw28268step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28268step1 raw28268step1Labels permutation8 permutation3
    _ = mixedMoment B node1104 node1104Labels := by rfl

def raw28269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -2, -1]]
def raw28269Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -2, 0], ![3, -2, -1]]
def raw28269step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28269step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![2, -2, 0], ![3, -2, -1]]
def raw28269step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28269step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-2, -1, 3], ![-3, 2, 1]]
def raw28269step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28269step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 1, -3], ![3, -2, -1]]
def raw28269step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28269 raw28269Labels = mixedMoment B node2315 node2315Labels := by
  calc
    mixedMoment B raw28269 raw28269Labels = mixedMoment B raw28269step0 raw28269step0Labels := by
      have hz : ∀ j, raw28269 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28269step0 = (fun i j => raw28269 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28269step0 raw28269; decide +kernel
      have hl : raw28269step0Labels = raw28269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28269 raw28269Labels permutation434 hz
    mixedMoment B raw28269step0 raw28269step0Labels = mixedMoment B raw28269step1 raw28269step1Labels := by
      have hz : ∀ j, raw28269step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28269step1 = (fun i j => raw28269step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28269step1 raw28269step0; decide +kernel
      have hl : raw28269step1Labels = raw28269step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28269step0 raw28269step0Labels permutation80 hz
    mixedMoment B raw28269step1 raw28269step1Labels = mixedMoment B raw28269step2 raw28269step2Labels := by
      have ha : raw28269step2 = (fun i j => raw28269step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28269step2 raw28269step1; decide +kernel
      have hl : raw28269step2Labels = raw28269step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28269step1 raw28269step1Labels permutation31 permutation3
    mixedMoment B raw28269step2 raw28269step2Labels = mixedMoment B raw28269step3 raw28269step3Labels := by
      have ha : raw28269step3 = -raw28269step2 := by apply Matrix.ext; change ∀ i j, raw28269step3 i j = -(raw28269step2 i j); unfold raw28269step3 raw28269step2; decide +kernel
      have hl : raw28269step3Labels = raw28269step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2315 node2315Labels := by rfl

def raw28270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -2, -1]]
def raw28270Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![3, -2, -1]]
def raw28270step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28270step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28270step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28270step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28270 raw28270Labels = mixedMoment B node2310 node2310Labels := by
  calc
    mixedMoment B raw28270 raw28270Labels = mixedMoment B raw28270step0 raw28270step0Labels := by
      have hz : ∀ j, raw28270 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28270step0 = (fun i j => raw28270 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28270step0 raw28270; decide +kernel
      have hl : raw28270step0Labels = raw28270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28270 raw28270Labels permutation434 hz
    mixedMoment B raw28270step0 raw28270step0Labels = mixedMoment B raw28270step1 raw28270step1Labels := by
      have ha : raw28270step1 = (fun i j => raw28270step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28270step1 raw28270step0; decide +kernel
      have hl : raw28270step1Labels = raw28270step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28270step0 raw28270step0Labels permutation151 permutation3
    mixedMoment B raw28270step1 raw28270step1Labels = mixedMoment B raw28270step2 raw28270step2Labels := by
      have ha : raw28270step2 = -raw28270step1 := by apply Matrix.ext; change ∀ i j, raw28270step2 i j = -(raw28270step1 i j); unfold raw28270step2 raw28270step1; decide +kernel
      have hl : raw28270step2Labels = raw28270step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2310 node2310Labels := by rfl

def raw28271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -2, -1]]
def raw28271Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![3, -2, -1]]
def raw28271step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28271step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28271step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28271step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28271 raw28271Labels = mixedMoment B node2310 node2310Labels := by
  calc
    mixedMoment B raw28271 raw28271Labels = mixedMoment B raw28271step0 raw28271step0Labels := by
      have hz : ∀ j, raw28271 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28271step0 = (fun i j => raw28271 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28271step0 raw28271; decide +kernel
      have hl : raw28271step0Labels = raw28271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28271 raw28271Labels permutation346 hz
    mixedMoment B raw28271step0 raw28271step0Labels = mixedMoment B raw28271step1 raw28271step1Labels := by
      have ha : raw28271step1 = (fun i j => raw28271step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28271step1 raw28271step0; decide +kernel
      have hl : raw28271step1Labels = raw28271step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28271step0 raw28271step0Labels permutation151 permutation3
    mixedMoment B raw28271step1 raw28271step1Labels = mixedMoment B raw28271step2 raw28271step2Labels := by
      have ha : raw28271step2 = -raw28271step1 := by apply Matrix.ext; change ∀ i j, raw28271step2 i j = -(raw28271step1 i j); unfold raw28271step2 raw28271step1; decide +kernel
      have hl : raw28271step2Labels = raw28271step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2310 node2310Labels := by rfl

def raw28272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -3, -1]]
def raw28272Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![4, -3, -1]]
def raw28272step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28272step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28272step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28272step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, -1, 2], ![-4, 2, 2]]
def raw28272step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28272step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw28272step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28272 raw28272Labels = mixedMoment B node893 node893Labels := by
  calc
    mixedMoment B raw28272 raw28272Labels = mixedMoment B raw28272step0 raw28272step0Labels := by
      have hz : ∀ j, raw28272 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28272step0 = (fun i j => raw28272 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28272step0 raw28272; decide +kernel
      have hl : raw28272step0Labels = raw28272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28272 raw28272Labels permutation434 hz
    mixedMoment B raw28272step0 raw28272step0Labels = mixedMoment B raw28272step1 raw28272step1Labels := by
      have hz : ∀ j, raw28272step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28272step1 = (fun i j => raw28272step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28272step1 raw28272step0; decide +kernel
      have hl : raw28272step1Labels = raw28272step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28272step0 raw28272step0Labels permutation80 hz
    mixedMoment B raw28272step1 raw28272step1Labels = mixedMoment B raw28272step2 raw28272step2Labels := by
      have ha : raw28272step2 = (fun i j => raw28272step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28272step2 raw28272step1; decide +kernel
      have hl : raw28272step2Labels = raw28272step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28272step1 raw28272step1Labels permutation31 permutation3
    mixedMoment B raw28272step2 raw28272step2Labels = mixedMoment B raw28272step3 raw28272step3Labels := by
      have ha : raw28272step3 = -raw28272step2 := by apply Matrix.ext; change ∀ i j, raw28272step3 i j = -(raw28272step2 i j); unfold raw28272step3 raw28272step2; decide +kernel
      have hl : raw28272step3Labels = raw28272step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node893 node893Labels := by rfl

def raw28273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -3, -1]]
def raw28273Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![4, -3, -1]]
def raw28273step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28273step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![4, -3, -1]]
def raw28273step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28273step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-2, -1, 3], ![-3, 2, 1]]
def raw28273step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28273step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw28273step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28273 raw28273Labels = mixedMoment B node897 node897Labels := by
  calc
    mixedMoment B raw28273 raw28273Labels = mixedMoment B raw28273step0 raw28273step0Labels := by
      have hz : ∀ j, raw28273 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28273step0 = (fun i j => raw28273 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28273step0 raw28273; decide +kernel
      have hl : raw28273step0Labels = raw28273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28273 raw28273Labels permutation434 hz
    mixedMoment B raw28273step0 raw28273step0Labels = mixedMoment B raw28273step1 raw28273step1Labels := by
      have hz : ∀ j, raw28273step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28273step1 = (fun i j => raw28273step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28273step1 raw28273step0; decide +kernel
      have hl : raw28273step1Labels = raw28273step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28273step0 raw28273step0Labels permutation80 hz
    mixedMoment B raw28273step1 raw28273step1Labels = mixedMoment B raw28273step2 raw28273step2Labels := by
      have ha : raw28273step2 = (fun i j => raw28273step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28273step2 raw28273step1; decide +kernel
      have hl : raw28273step2Labels = raw28273step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28273step1 raw28273step1Labels permutation31 permutation3
    mixedMoment B raw28273step2 raw28273step2Labels = mixedMoment B raw28273step3 raw28273step3Labels := by
      have ha : raw28273step3 = -raw28273step2 := by apply Matrix.ext; change ∀ i j, raw28273step3 i j = -(raw28273step2 i j); unfold raw28273step3 raw28273step2; decide +kernel
      have hl : raw28273step3Labels = raw28273step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node897 node897Labels := by rfl

def raw28274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -3, -1]]
def raw28274Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![4, -3, -1]]
def raw28274step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28274step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28274step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28274step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28274 raw28274Labels = mixedMoment B node887 node887Labels := by
  calc
    mixedMoment B raw28274 raw28274Labels = mixedMoment B raw28274step0 raw28274step0Labels := by
      have hz : ∀ j, raw28274 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28274step0 = (fun i j => raw28274 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28274step0 raw28274; decide +kernel
      have hl : raw28274step0Labels = raw28274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28274 raw28274Labels permutation434 hz
    mixedMoment B raw28274step0 raw28274step0Labels = mixedMoment B raw28274step1 raw28274step1Labels := by
      have ha : raw28274step1 = (fun i j => raw28274step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28274step1 raw28274step0; decide +kernel
      have hl : raw28274step1Labels = raw28274step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28274step0 raw28274step0Labels permutation151 permutation3
    mixedMoment B raw28274step1 raw28274step1Labels = mixedMoment B raw28274step2 raw28274step2Labels := by
      have ha : raw28274step2 = -raw28274step1 := by apply Matrix.ext; change ∀ i j, raw28274step2 i j = -(raw28274step1 i j); unfold raw28274step2 raw28274step1; decide +kernel
      have hl : raw28274step2Labels = raw28274step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node887 node887Labels := by rfl

def raw28275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -3, -1]]
def raw28275Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![4, -3, -1]]
def raw28275step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw28275step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28275step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw28275step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28275 raw28275Labels = mixedMoment B node887 node887Labels := by
  calc
    mixedMoment B raw28275 raw28275Labels = mixedMoment B raw28275step0 raw28275step0Labels := by
      have hz : ∀ j, raw28275 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28275step0 = (fun i j => raw28275 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28275step0 raw28275; decide +kernel
      have hl : raw28275step0Labels = raw28275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28275 raw28275Labels permutation346 hz
    mixedMoment B raw28275step0 raw28275step0Labels = mixedMoment B raw28275step1 raw28275step1Labels := by
      have ha : raw28275step1 = (fun i j => raw28275step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28275step1 raw28275step0; decide +kernel
      have hl : raw28275step1Labels = raw28275step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28275step0 raw28275step0Labels permutation151 permutation3
    mixedMoment B raw28275step1 raw28275step1Labels = mixedMoment B raw28275step2 raw28275step2Labels := by
      have ha : raw28275step2 = -raw28275step1 := by apply Matrix.ext; change ∀ i j, raw28275step2 i j = -(raw28275step1 i j); unfold raw28275step2 raw28275step1; decide +kernel
      have hl : raw28275step2Labels = raw28275step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node887 node887Labels := by rfl

def raw28276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -3, -1]]
def raw28276Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![4, -3, -1]]
def raw28276step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28276step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![4, -3, -1]]
def raw28276step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28276step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![4, -3, -1]]
def raw28276step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw28276step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, -1, 2], ![-3, 2, 1]]
def raw28276step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw28276step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw28276step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical28276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28276 raw28276Labels = mixedMoment B node1091 node1091Labels := by
  calc
    mixedMoment B raw28276 raw28276Labels = mixedMoment B raw28276step0 raw28276step0Labels := by
      have hz : ∀ j, raw28276 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw28276step0 = (fun i j => raw28276 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw28276step0 raw28276; decide +kernel
      have hl : raw28276step0Labels = raw28276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28276 raw28276Labels permutation520 hz
    mixedMoment B raw28276step0 raw28276step0Labels = mixedMoment B raw28276step1 raw28276step1Labels := by
      have hz : ∀ j, raw28276step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw28276step1 = (fun i j => raw28276step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw28276step1 raw28276step0; decide +kernel
      have hl : raw28276step1Labels = raw28276step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28276step0 raw28276step0Labels permutation104 hz
    mixedMoment B raw28276step1 raw28276step1Labels = mixedMoment B raw28276step2 raw28276step2Labels := by
      have hz : ∀ j, raw28276step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw28276step2 = (fun i j => raw28276step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw28276step2 raw28276step1; decide +kernel
      have hl : raw28276step2Labels = raw28276step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28276step1 raw28276step1Labels permutation20 hz
    mixedMoment B raw28276step2 raw28276step2Labels = mixedMoment B raw28276step3 raw28276step3Labels := by
      have ha : raw28276step3 = (fun i j => raw28276step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28276step3 raw28276step2; decide +kernel
      have hl : raw28276step3Labels = raw28276step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28276step2 raw28276step2Labels permutation7 permutation3
    mixedMoment B raw28276step3 raw28276step3Labels = mixedMoment B raw28276step4 raw28276step4Labels := by
      have ha : raw28276step4 = -raw28276step3 := by apply Matrix.ext; change ∀ i j, raw28276step4 i j = -(raw28276step3 i j); unfold raw28276step4 raw28276step3; decide +kernel
      have hl : raw28276step4Labels = raw28276step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1091 node1091Labels := by rfl

def raw28277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28277step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![3, -1, -2]]
def raw28277step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28277step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw28277step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28277step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw28277step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28277 raw28277Labels = mixedMoment B node5111 node5111Labels := by
  calc
    mixedMoment B raw28277 raw28277Labels = mixedMoment B raw28277step0 raw28277step0Labels := by
      have hz : ∀ j, raw28277 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28277step0 = (fun i j => raw28277 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28277step0 raw28277; decide +kernel
      have hl : raw28277step0Labels = raw28277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28277 raw28277Labels permutation434 hz
    mixedMoment B raw28277step0 raw28277step0Labels = mixedMoment B raw28277step1 raw28277step1Labels := by
      have hz : ∀ j, raw28277step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28277step1 = (fun i j => raw28277step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28277step1 raw28277step0; decide +kernel
      have hl : raw28277step1Labels = raw28277step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28277step0 raw28277step0Labels permutation80 hz
    mixedMoment B raw28277step1 raw28277step1Labels = mixedMoment B raw28277step2 raw28277step2Labels := by
      have ha : raw28277step2 = (fun i j => raw28277step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28277step2 raw28277step1; decide +kernel
      have hl : raw28277step2Labels = raw28277step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28277step1 raw28277step1Labels permutation30 permutation2
    mixedMoment B raw28277step2 raw28277step2Labels = mixedMoment B raw28277step3 raw28277step3Labels := by
      have ha : raw28277step3 = -raw28277step2 := by apply Matrix.ext; change ∀ i j, raw28277step3 i j = -(raw28277step2 i j); unfold raw28277step3 raw28277step2; decide +kernel
      have hl : raw28277step3Labels = raw28277step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5111 node5111Labels := by rfl

def raw28278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw28278step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28278step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw28278step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28278 raw28278Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw28278 raw28278Labels = mixedMoment B raw28278step0 raw28278step0Labels := by
      have hz : ∀ j, raw28278 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28278step0 = (fun i j => raw28278 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28278step0 raw28278; decide +kernel
      have hl : raw28278step0Labels = raw28278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28278 raw28278Labels permutation434 hz
    mixedMoment B raw28278step0 raw28278step0Labels = mixedMoment B raw28278step1 raw28278step1Labels := by
      have ha : raw28278step1 = (fun i j => raw28278step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28278step1 raw28278step0; decide +kernel
      have hl : raw28278step1Labels = raw28278step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28278step0 raw28278step0Labels permutation151 permutation2
    mixedMoment B raw28278step1 raw28278step1Labels = mixedMoment B raw28278step2 raw28278step2Labels := by
      have ha : raw28278step2 = -raw28278step1 := by apply Matrix.ext; change ∀ i j, raw28278step2 i j = -(raw28278step1 i j); unfold raw28278step2 raw28278step1; decide +kernel
      have hl : raw28278step2Labels = raw28278step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw28279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28279step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw28279step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28279step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw28279step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28279 raw28279Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw28279 raw28279Labels = mixedMoment B raw28279step0 raw28279step0Labels := by
      have hz : ∀ j, raw28279 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28279step0 = (fun i j => raw28279 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28279step0 raw28279; decide +kernel
      have hl : raw28279step0Labels = raw28279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28279 raw28279Labels permutation346 hz
    mixedMoment B raw28279step0 raw28279step0Labels = mixedMoment B raw28279step1 raw28279step1Labels := by
      have ha : raw28279step1 = (fun i j => raw28279step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28279step1 raw28279step0; decide +kernel
      have hl : raw28279step1Labels = raw28279step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28279step0 raw28279step0Labels permutation151 permutation2
    mixedMoment B raw28279step1 raw28279step1Labels = mixedMoment B raw28279step2 raw28279step2Labels := by
      have ha : raw28279step2 = -raw28279step1 := by apply Matrix.ext; change ∀ i j, raw28279step2 i j = -(raw28279step1 i j); unfold raw28279step2 raw28279step1; decide +kernel
      have hl : raw28279step2Labels = raw28279step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw28280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28280step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![3, -1, -2]]
def raw28280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28280step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw28280step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28280step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw28280step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28280 raw28280Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw28280 raw28280Labels = mixedMoment B raw28280step0 raw28280step0Labels := by
      have hz : ∀ j, raw28280 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28280step0 = (fun i j => raw28280 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28280step0 raw28280; decide +kernel
      have hl : raw28280step0Labels = raw28280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28280 raw28280Labels permutation434 hz
    mixedMoment B raw28280step0 raw28280step0Labels = mixedMoment B raw28280step1 raw28280step1Labels := by
      have hz : ∀ j, raw28280step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28280step1 = (fun i j => raw28280step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28280step1 raw28280step0; decide +kernel
      have hl : raw28280step1Labels = raw28280step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28280step0 raw28280step0Labels permutation80 hz
    mixedMoment B raw28280step1 raw28280step1Labels = mixedMoment B raw28280step2 raw28280step2Labels := by
      have ha : raw28280step2 = (fun i j => raw28280step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28280step2 raw28280step1; decide +kernel
      have hl : raw28280step2Labels = raw28280step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28280step1 raw28280step1Labels permutation31 permutation2
    mixedMoment B raw28280step2 raw28280step2Labels = mixedMoment B raw28280step3 raw28280step3Labels := by
      have ha : raw28280step3 = -raw28280step2 := by apply Matrix.ext; change ∀ i j, raw28280step3 i j = -(raw28280step2 i j); unfold raw28280step3 raw28280step2; decide +kernel
      have hl : raw28280step3Labels = raw28280step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw28281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28281step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28281step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28281step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw28281step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28281step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw28281step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28281 raw28281Labels = mixedMoment B node5413 node5413Labels := by
  calc
    mixedMoment B raw28281 raw28281Labels = mixedMoment B raw28281step0 raw28281step0Labels := by
      have hz : ∀ j, raw28281 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28281step0 = (fun i j => raw28281 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28281step0 raw28281; decide +kernel
      have hl : raw28281step0Labels = raw28281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28281 raw28281Labels permutation434 hz
    mixedMoment B raw28281step0 raw28281step0Labels = mixedMoment B raw28281step1 raw28281step1Labels := by
      have hz : ∀ j, raw28281step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28281step1 = (fun i j => raw28281step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28281step1 raw28281step0; decide +kernel
      have hl : raw28281step1Labels = raw28281step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28281step0 raw28281step0Labels permutation80 hz
    mixedMoment B raw28281step1 raw28281step1Labels = mixedMoment B raw28281step2 raw28281step2Labels := by
      have ha : raw28281step2 = (fun i j => raw28281step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28281step2 raw28281step1; decide +kernel
      have hl : raw28281step2Labels = raw28281step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28281step1 raw28281step1Labels permutation31 permutation2
    mixedMoment B raw28281step2 raw28281step2Labels = mixedMoment B raw28281step3 raw28281step3Labels := by
      have ha : raw28281step3 = -raw28281step2 := by apply Matrix.ext; change ∀ i j, raw28281step3 i j = -(raw28281step2 i j); unfold raw28281step3 raw28281step2; decide +kernel
      have hl : raw28281step3Labels = raw28281step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5413 node5413Labels := by rfl

def raw28282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw28282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28282step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw28282step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28282step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw28282step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28282 raw28282Labels = mixedMoment B node4476 node4476Labels := by
  calc
    mixedMoment B raw28282 raw28282Labels = mixedMoment B raw28282step0 raw28282step0Labels := by
      have hz : ∀ j, raw28282 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28282step0 = (fun i j => raw28282 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28282step0 raw28282; decide +kernel
      have hl : raw28282step0Labels = raw28282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28282 raw28282Labels permutation434 hz
    mixedMoment B raw28282step0 raw28282step0Labels = mixedMoment B raw28282step1 raw28282step1Labels := by
      have hz : ∀ j, raw28282step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28282step1 = (fun i j => raw28282step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28282step1 raw28282step0; decide +kernel
      have hl : raw28282step1Labels = raw28282step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28282step0 raw28282step0Labels permutation80 hz
    mixedMoment B raw28282step1 raw28282step1Labels = mixedMoment B raw28282step2 raw28282step2Labels := by
      have ha : raw28282step2 = (fun i j => raw28282step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28282step2 raw28282step1; decide +kernel
      have hl : raw28282step2Labels = raw28282step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28282step1 raw28282step1Labels permutation8 permutation3
    mixedMoment B raw28282step2 raw28282step2Labels = mixedMoment B raw28282step3 raw28282step3Labels := by
      have ha : raw28282step3 = raw28282step2 := by apply Matrix.ext; unfold raw28282step3 raw28282step2; decide +kernel
      have hl : raw28282step2Labels = labelEmbedding6 ∘ raw28282step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28282step2 raw28282step2Labels raw28282step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4476 node4476Labels := by rfl

def raw28283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw28283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28283step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw28283step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28283 raw28283Labels = mixedMoment B node5087 node5087Labels := by
  calc
    mixedMoment B raw28283 raw28283Labels = mixedMoment B raw28283step0 raw28283step0Labels := by
      have hz : ∀ j, raw28283 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28283step0 = (fun i j => raw28283 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28283step0 raw28283; decide +kernel
      have hl : raw28283step0Labels = raw28283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28283 raw28283Labels permutation434 hz
    mixedMoment B raw28283step0 raw28283step0Labels = mixedMoment B raw28283step1 raw28283step1Labels := by
      have ha : raw28283step1 = (fun i j => raw28283step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28283step1 raw28283step0; decide +kernel
      have hl : raw28283step1Labels = raw28283step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28283step0 raw28283step0Labels permutation149 permutation2
    mixedMoment B raw28283step1 raw28283step1Labels = mixedMoment B raw28283step2 raw28283step2Labels := by
      have ha : raw28283step2 = -raw28283step1 := by apply Matrix.ext; change ∀ i j, raw28283step2 i j = -(raw28283step1 i j); unfold raw28283step2 raw28283step1; decide +kernel
      have hl : raw28283step2Labels = raw28283step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5087 node5087Labels := by rfl

def raw28284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28284step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw28284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28284step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw28284step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28284 raw28284Labels = mixedMoment B node5087 node5087Labels := by
  calc
    mixedMoment B raw28284 raw28284Labels = mixedMoment B raw28284step0 raw28284step0Labels := by
      have hz : ∀ j, raw28284 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw28284step0 = (fun i j => raw28284 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw28284step0 raw28284; decide +kernel
      have hl : raw28284step0Labels = raw28284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28284 raw28284Labels permutation346 hz
    mixedMoment B raw28284step0 raw28284step0Labels = mixedMoment B raw28284step1 raw28284step1Labels := by
      have ha : raw28284step1 = (fun i j => raw28284step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28284step1 raw28284step0; decide +kernel
      have hl : raw28284step1Labels = raw28284step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28284step0 raw28284step0Labels permutation149 permutation2
    mixedMoment B raw28284step1 raw28284step1Labels = mixedMoment B raw28284step2 raw28284step2Labels := by
      have ha : raw28284step2 = -raw28284step1 := by apply Matrix.ext; change ∀ i j, raw28284step2 i j = -(raw28284step1 i j); unfold raw28284step2 raw28284step1; decide +kernel
      have hl : raw28284step2Labels = raw28284step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5087 node5087Labels := by rfl

def raw28285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![3, -1, -2]]
def raw28285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28285step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw28285step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28285step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw28285step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28285step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw28285step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28285 raw28285Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw28285 raw28285Labels = mixedMoment B raw28285step0 raw28285step0Labels := by
      have hz : ∀ j, raw28285 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28285step0 = (fun i j => raw28285 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28285step0 raw28285; decide +kernel
      have hl : raw28285step0Labels = raw28285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28285 raw28285Labels permutation434 hz
    mixedMoment B raw28285step0 raw28285step0Labels = mixedMoment B raw28285step1 raw28285step1Labels := by
      have hz : ∀ j, raw28285step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28285step1 = (fun i j => raw28285step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28285step1 raw28285step0; decide +kernel
      have hl : raw28285step1Labels = raw28285step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28285step0 raw28285step0Labels permutation80 hz
    mixedMoment B raw28285step1 raw28285step1Labels = mixedMoment B raw28285step2 raw28285step2Labels := by
      have ha : raw28285step2 = (fun i j => raw28285step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw28285step2 raw28285step1; decide +kernel
      have hl : raw28285step2Labels = raw28285step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28285step1 raw28285step1Labels permutation31 permutation2
    mixedMoment B raw28285step2 raw28285step2Labels = mixedMoment B raw28285step3 raw28285step3Labels := by
      have ha : raw28285step3 = -raw28285step2 := by apply Matrix.ext; change ∀ i j, raw28285step3 i j = -(raw28285step2 i j); unfold raw28285step3 raw28285step2; decide +kernel
      have hl : raw28285step3Labels = raw28285step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5268 node5268Labels := by rfl

def raw28286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw28286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28286step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw28286step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28286step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw28286step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28286step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw28286step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28286 raw28286Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw28286 raw28286Labels = mixedMoment B raw28286step0 raw28286step0Labels := by
      have hz : ∀ j, raw28286 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28286step0 = (fun i j => raw28286 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28286step0 raw28286; decide +kernel
      have hl : raw28286step0Labels = raw28286Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28286 raw28286Labels permutation434 hz
    mixedMoment B raw28286step0 raw28286step0Labels = mixedMoment B raw28286step1 raw28286step1Labels := by
      have hz : ∀ j, raw28286step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw28286step1 = (fun i j => raw28286step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw28286step1 raw28286step0; decide +kernel
      have hl : raw28286step1Labels = raw28286step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28286step0 raw28286step0Labels permutation80 hz
    mixedMoment B raw28286step1 raw28286step1Labels = mixedMoment B raw28286step2 raw28286step2Labels := by
      have ha : raw28286step2 = (fun i j => raw28286step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28286step2 raw28286step1; decide +kernel
      have hl : raw28286step2Labels = raw28286step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28286step1 raw28286step1Labels permutation8 permutation3
    mixedMoment B raw28286step2 raw28286step2Labels = mixedMoment B raw28286step3 raw28286step3Labels := by
      have ha : raw28286step3 = raw28286step2 := by apply Matrix.ext; unfold raw28286step3 raw28286step2; decide +kernel
      have hl : raw28286step2Labels = labelEmbedding6 ∘ raw28286step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28286step2 raw28286step2Labels raw28286step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw28287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw28287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw28287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28287step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw28287step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw28287step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical28287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw28287 raw28287Labels = mixedMoment B node4367 node4367Labels := by
  calc
    mixedMoment B raw28287 raw28287Labels = mixedMoment B raw28287step0 raw28287step0Labels := by
      have hz : ∀ j, raw28287 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw28287step0 = (fun i j => raw28287 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw28287step0 raw28287; decide +kernel
      have hl : raw28287step0Labels = raw28287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw28287 raw28287Labels permutation434 hz
    mixedMoment B raw28287step0 raw28287step0Labels = mixedMoment B raw28287step1 raw28287step1Labels := by
      have ha : raw28287step1 = (fun i j => raw28287step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw28287step1 raw28287step0; decide +kernel
      have hl : raw28287step1Labels = raw28287step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw28287step0 raw28287step0Labels permutation34 permutation3
    mixedMoment B raw28287step1 raw28287step1Labels = mixedMoment B raw28287step2 raw28287step2Labels := by
      have ha : raw28287step2 = raw28287step1 := by apply Matrix.ext; unfold raw28287step2 raw28287step1; decide +kernel
      have hl : raw28287step1Labels = labelEmbedding6 ∘ raw28287step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw28287step1 raw28287step1Labels raw28287step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4367 node4367Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
