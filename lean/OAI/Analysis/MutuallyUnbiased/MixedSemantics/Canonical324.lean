import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw41472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw41472Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, -1, 1], ![2, 1, -3]]
def raw41472step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw41472step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41472step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw41472step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41472 raw41472Labels = mixedMoment B node2434 node2434Labels := by
  calc
    mixedMoment B raw41472 raw41472Labels = mixedMoment B raw41472step0 raw41472step0Labels := by
      have hz : ∀ j, raw41472 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41472step0 = (fun i j => raw41472 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41472step0 raw41472; decide +kernel
      have hl : raw41472step0Labels = raw41472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41472 raw41472Labels permutation434 hz
    mixedMoment B raw41472step0 raw41472step0Labels = mixedMoment B raw41472step1 raw41472step1Labels := by
      have ha : raw41472step1 = (fun i j => raw41472step0 (permutation68 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41472step1 raw41472step0; decide +kernel
      have hl : raw41472step1Labels = raw41472step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41472step0 raw41472step0Labels permutation68 permutation6
    mixedMoment B raw41472step1 raw41472step1Labels = mixedMoment B raw41472step2 raw41472step2Labels := by
      have ha : raw41472step2 = -raw41472step1 := by apply Matrix.ext; change ∀ i j, raw41472step2 i j = -(raw41472step1 i j); unfold raw41472step2 raw41472step1; decide +kernel
      have hl : raw41472step2Labels = raw41472step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2434 node2434Labels := by rfl

def raw41473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw41473Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41473step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw41473step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41473step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw41473step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41473 raw41473Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw41473 raw41473Labels = mixedMoment B raw41473step0 raw41473step0Labels := by
      have hz : ∀ j, raw41473 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41473step0 = (fun i j => raw41473 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41473step0 raw41473; decide +kernel
      have hl : raw41473step0Labels = raw41473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41473 raw41473Labels permutation434 hz
    mixedMoment B raw41473step0 raw41473step0Labels = mixedMoment B raw41473step1 raw41473step1Labels := by
      have ha : raw41473step1 = (fun i j => raw41473step0 (permutation61 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41473step1 raw41473step0; decide +kernel
      have hl : raw41473step1Labels = raw41473step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41473step0 raw41473step0Labels permutation61 permutation6
    mixedMoment B raw41473step1 raw41473step1Labels = mixedMoment B raw41473step2 raw41473step2Labels := by
      have ha : raw41473step2 = -raw41473step1 := by apply Matrix.ext; change ∀ i j, raw41473step2 i j = -(raw41473step1 i j); unfold raw41473step2 raw41473step1; decide +kernel
      have hl : raw41473step2Labels = raw41473step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2561 node2561Labels := by rfl

def raw41474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw41474Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw41474step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41474step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41474 raw41474Labels = mixedMoment B node2428 node2428Labels := by
  calc
    mixedMoment B raw41474 raw41474Labels = mixedMoment B raw41474step0 raw41474step0Labels := by
      have ha : raw41474step0 = (fun i j => raw41474 (permutation310 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41474step0 raw41474; decide +kernel
      have hl : raw41474step0Labels = raw41474Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41474 raw41474Labels permutation310 permutation6
    mixedMoment B raw41474step0 raw41474step0Labels = mixedMoment B raw41474step1 raw41474step1Labels := by
      have ha : raw41474step1 = -raw41474step0 := by apply Matrix.ext; change ∀ i j, raw41474step1 i j = -(raw41474step0 i j); unfold raw41474step1 raw41474step0; decide +kernel
      have hl : raw41474step1Labels = raw41474step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2428 node2428Labels := by rfl

def raw41475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw41475Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw41475step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41475step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41475step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41475 raw41475Labels = mixedMoment B node2589 node2589Labels := by
  calc
    mixedMoment B raw41475 raw41475Labels = mixedMoment B raw41475step0 raw41475step0Labels := by
      have ha : raw41475step0 = (fun i j => raw41475 (permutation283 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41475step0 raw41475; decide +kernel
      have hl : raw41475step0Labels = raw41475Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41475 raw41475Labels permutation283 permutation6
    mixedMoment B raw41475step0 raw41475step0Labels = mixedMoment B raw41475step1 raw41475step1Labels := by
      have ha : raw41475step1 = -raw41475step0 := by apply Matrix.ext; change ∀ i j, raw41475step1 i j = -(raw41475step0 i j); unfold raw41475step1 raw41475step0; decide +kernel
      have hl : raw41475step1Labels = raw41475step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2589 node2589Labels := by rfl

def raw41476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, 1, -3]]
def raw41476Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw41476step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41476 raw41476Labels = mixedMoment B node2429 node2429Labels := by
  calc
    mixedMoment B raw41476 raw41476Labels = mixedMoment B raw41476step0 raw41476step0Labels := by
      have ha : raw41476step0 = (fun i j => raw41476 (permutation322 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41476step0 raw41476; decide +kernel
      have hl : raw41476step0Labels = raw41476Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41476 raw41476Labels permutation322 permutation6
    mixedMoment B raw41476step0 raw41476step0Labels = mixedMoment B raw41476step1 raw41476step1Labels := by
      have ha : raw41476step1 = -raw41476step0 := by apply Matrix.ext; change ∀ i j, raw41476step1 i j = -(raw41476step0 i j); unfold raw41476step1 raw41476step0; decide +kernel
      have hl : raw41476step1Labels = raw41476step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2429 node2429Labels := by rfl

def raw41477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 2, -4]]
def raw41477Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, -1, 1], ![2, 2, -4]]
def raw41477step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw41477step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41477 raw41477Labels = mixedMoment B node1131 node1131Labels := by
  calc
    mixedMoment B raw41477 raw41477Labels = mixedMoment B raw41477step0 raw41477step0Labels := by
      have hz : ∀ j, raw41477 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41477step0 = (fun i j => raw41477 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41477step0 raw41477; decide +kernel
      have hl : raw41477step0Labels = raw41477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41477 raw41477Labels permutation434 hz
    mixedMoment B raw41477step0 raw41477step0Labels = mixedMoment B raw41477step1 raw41477step1Labels := by
      have ha : raw41477step1 = (fun i j => raw41477step0 (permutation141 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41477step1 raw41477step0; decide +kernel
      have hl : raw41477step1Labels = raw41477step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41477step0 raw41477step0Labels permutation141 permutation6
    _ = mixedMoment B node1131 node1131Labels := by rfl

def raw41478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw41478Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0]]
def raw41478step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw41478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41478 raw41478Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw41478 raw41478Labels = mixedMoment B raw41478step0 raw41478step0Labels := by
      have hz : ∀ j, raw41478 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41478step0 = (fun i j => raw41478 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41478step0 raw41478; decide +kernel
      have hl : raw41478step0Labels = raw41478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41478 raw41478Labels permutation434 hz
    mixedMoment B raw41478step0 raw41478step0Labels = mixedMoment B raw41478step1 raw41478step1Labels := by
      have ha : raw41478step1 = (fun i j => raw41478step0 (permutation120 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41478step1 raw41478step0; decide +kernel
      have hl : raw41478step1Labels = raw41478step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41478step0 raw41478step0Labels permutation120 permutation6
    _ = mixedMoment B node2482 node2482Labels := by rfl

def raw41479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw41479Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw41479step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41479 raw41479Labels = mixedMoment B node2425 node2425Labels := by
  calc
    mixedMoment B raw41479 raw41479Labels = mixedMoment B raw41479step0 raw41479step0Labels := by
      have ha : raw41479step0 = (fun i j => raw41479 (permutation548 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41479step0 raw41479; decide +kernel
      have hl : raw41479step0Labels = raw41479Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41479 raw41479Labels permutation548 permutation6
    _ = mixedMoment B node2425 node2425Labels := by rfl

def raw41480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw41480Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw41480step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -2, 3], ![0, -1, 1], ![2, 3, -5]]
def raw41480step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41480step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw41480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41480 raw41480Labels = mixedMoment B node605 node605Labels := by
  calc
    mixedMoment B raw41480 raw41480Labels = mixedMoment B raw41480step0 raw41480step0Labels := by
      have hz : ∀ j, raw41480 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41480step0 = (fun i j => raw41480 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41480step0 raw41480; decide +kernel
      have hl : raw41480step0Labels = raw41480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41480 raw41480Labels permutation434 hz
    mixedMoment B raw41480step0 raw41480step0Labels = mixedMoment B raw41480step1 raw41480step1Labels := by
      have hz : ∀ j, raw41480step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41480step1 = (fun i j => raw41480step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41480step1 raw41480step0; decide +kernel
      have hl : raw41480step1Labels = raw41480step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41480step0 raw41480step0Labels permutation80 hz
    mixedMoment B raw41480step1 raw41480step1Labels = mixedMoment B raw41480step2 raw41480step2Labels := by
      have ha : raw41480step2 = (fun i j => raw41480step1 (permutation27 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41480step2 raw41480step1; decide +kernel
      have hl : raw41480step2Labels = raw41480step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41480step1 raw41480step1Labels permutation27 permutation6
    _ = mixedMoment B node605 node605Labels := by rfl

def raw41481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw41481Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 3, -3], ![0, 0, 0], ![2, 0, -2]]
def raw41481step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41481step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 3, -3], ![2, 0, -2]]
def raw41481step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41481step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 2, 0], ![-3, 0, 3]]
def raw41481step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41481step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw41481step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41481 raw41481Labels = mixedMoment B node937 node937Labels := by
  calc
    mixedMoment B raw41481 raw41481Labels = mixedMoment B raw41481step0 raw41481step0Labels := by
      have hz : ∀ j, raw41481 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41481step0 = (fun i j => raw41481 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41481step0 raw41481; decide +kernel
      have hl : raw41481step0Labels = raw41481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41481 raw41481Labels permutation520 hz
    mixedMoment B raw41481step0 raw41481step0Labels = mixedMoment B raw41481step1 raw41481step1Labels := by
      have hz : ∀ j, raw41481step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41481step1 = (fun i j => raw41481step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41481step1 raw41481step0; decide +kernel
      have hl : raw41481step1Labels = raw41481step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41481step0 raw41481step0Labels permutation104 hz
    mixedMoment B raw41481step1 raw41481step1Labels = mixedMoment B raw41481step2 raw41481step2Labels := by
      have ha : raw41481step2 = (fun i j => raw41481step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41481step2 raw41481step1; decide +kernel
      have hl : raw41481step2Labels = raw41481step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41481step1 raw41481step1Labels permutation15 permutation6
    mixedMoment B raw41481step2 raw41481step2Labels = mixedMoment B raw41481step3 raw41481step3Labels := by
      have ha : raw41481step3 = -raw41481step2 := by apply Matrix.ext; change ∀ i j, raw41481step3 i j = -(raw41481step2 i j); unfold raw41481step3 raw41481step2; decide +kernel
      have hl : raw41481step3Labels = raw41481step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node937 node937Labels := by rfl

def raw41482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw41482Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 2, -2], ![0, 1, -1], ![2, 0, -2]]
def raw41482step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41482step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41482step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41482step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41482step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41482 raw41482Labels = mixedMoment B node932 node932Labels := by
  calc
    mixedMoment B raw41482 raw41482Labels = mixedMoment B raw41482step0 raw41482step0Labels := by
      have hz : ∀ j, raw41482 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41482step0 = (fun i j => raw41482 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41482step0 raw41482; decide +kernel
      have hl : raw41482step0Labels = raw41482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41482 raw41482Labels permutation520 hz
    mixedMoment B raw41482step0 raw41482step0Labels = mixedMoment B raw41482step1 raw41482step1Labels := by
      have ha : raw41482step1 = (fun i j => raw41482step0 (permutation59 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41482step1 raw41482step0; decide +kernel
      have hl : raw41482step1Labels = raw41482step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41482step0 raw41482step0Labels permutation59 permutation6
    mixedMoment B raw41482step1 raw41482step1Labels = mixedMoment B raw41482step2 raw41482step2Labels := by
      have ha : raw41482step2 = -raw41482step1 := by apply Matrix.ext; change ∀ i j, raw41482step2 i j = -(raw41482step1 i j); unfold raw41482step2 raw41482step1; decide +kernel
      have hl : raw41482step2Labels = raw41482step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node932 node932Labels := by rfl

def raw41483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw41483Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 2, -2], ![0, 0, 0], ![2, 1, -3]]
def raw41483step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41483step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 2, -2], ![2, 1, -3]]
def raw41483step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41483step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw41483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41483step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw41483step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41483 raw41483Labels = mixedMoment B node939 node939Labels := by
  calc
    mixedMoment B raw41483 raw41483Labels = mixedMoment B raw41483step0 raw41483step0Labels := by
      have hz : ∀ j, raw41483 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41483step0 = (fun i j => raw41483 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41483step0 raw41483; decide +kernel
      have hl : raw41483step0Labels = raw41483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41483 raw41483Labels permutation520 hz
    mixedMoment B raw41483step0 raw41483step0Labels = mixedMoment B raw41483step1 raw41483step1Labels := by
      have hz : ∀ j, raw41483step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41483step1 = (fun i j => raw41483step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41483step1 raw41483step0; decide +kernel
      have hl : raw41483step1Labels = raw41483step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41483step0 raw41483step0Labels permutation104 hz
    mixedMoment B raw41483step1 raw41483step1Labels = mixedMoment B raw41483step2 raw41483step2Labels := by
      have ha : raw41483step2 = (fun i j => raw41483step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41483step2 raw41483step1; decide +kernel
      have hl : raw41483step2Labels = raw41483step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41483step1 raw41483step1Labels permutation14 permutation6
    mixedMoment B raw41483step2 raw41483step2Labels = mixedMoment B raw41483step3 raw41483step3Labels := by
      have ha : raw41483step3 = -raw41483step2 := by apply Matrix.ext; change ∀ i j, raw41483step3 i j = -(raw41483step2 i j); unfold raw41483step3 raw41483step2; decide +kernel
      have hl : raw41483step3Labels = raw41483step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node939 node939Labels := by rfl

def raw41484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw41484Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41484step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41484step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41484step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41484 raw41484Labels = mixedMoment B node929 node929Labels := by
  calc
    mixedMoment B raw41484 raw41484Labels = mixedMoment B raw41484step0 raw41484step0Labels := by
      have ha : raw41484step0 = (fun i j => raw41484 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41484step0 raw41484; decide +kernel
      have hl : raw41484step0Labels = raw41484Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41484 raw41484Labels permutation265 permutation6
    mixedMoment B raw41484step0 raw41484step0Labels = mixedMoment B raw41484step1 raw41484step1Labels := by
      have ha : raw41484step1 = -raw41484step0 := by apply Matrix.ext; change ∀ i j, raw41484step1 i j = -(raw41484step0 i j); unfold raw41484step1 raw41484step0; decide +kernel
      have hl : raw41484step1Labels = raw41484step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node929 node929Labels := by rfl

def raw41485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3]]
def raw41485Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]
def raw41485step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw41485step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41485step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41485step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41485 raw41485Labels = mixedMoment B node930 node930Labels := by
  calc
    mixedMoment B raw41485 raw41485Labels = mixedMoment B raw41485step0 raw41485step0Labels := by
      have hz : ∀ j, raw41485 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41485step0 = (fun i j => raw41485 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41485step0 raw41485; decide +kernel
      have hl : raw41485step0Labels = raw41485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41485 raw41485Labels permutation520 hz
    mixedMoment B raw41485step0 raw41485step0Labels = mixedMoment B raw41485step1 raw41485step1Labels := by
      have ha : raw41485step1 = (fun i j => raw41485step0 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41485step1 raw41485step0; decide +kernel
      have hl : raw41485step1Labels = raw41485step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41485step0 raw41485step0Labels permutation56 permutation6
    mixedMoment B raw41485step1 raw41485step1Labels = mixedMoment B raw41485step2 raw41485step2Labels := by
      have ha : raw41485step2 = -raw41485step1 := by apply Matrix.ext; change ∀ i j, raw41485step2 i j = -(raw41485step1 i j); unfold raw41485step2 raw41485step1; decide +kernel
      have hl : raw41485step2Labels = raw41485step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node930 node930Labels := by rfl

def raw41486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw41486Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![0, 0, 0], ![2, 2, -4]]
def raw41486step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41486step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -3, 4], ![0, 1, -1], ![2, 2, -4]]
def raw41486step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41486step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 0, 1], ![-4, 2, 2]]
def raw41486step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41486step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![4, -2, -2]]
def raw41486step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41486 raw41486Labels = mixedMoment B node934 node934Labels := by
  calc
    mixedMoment B raw41486 raw41486Labels = mixedMoment B raw41486step0 raw41486step0Labels := by
      have hz : ∀ j, raw41486 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41486step0 = (fun i j => raw41486 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41486step0 raw41486; decide +kernel
      have hl : raw41486step0Labels = raw41486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41486 raw41486Labels permutation520 hz
    mixedMoment B raw41486step0 raw41486step0Labels = mixedMoment B raw41486step1 raw41486step1Labels := by
      have hz : ∀ j, raw41486step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41486step1 = (fun i j => raw41486step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41486step1 raw41486step0; decide +kernel
      have hl : raw41486step1Labels = raw41486step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41486step0 raw41486step0Labels permutation104 hz
    mixedMoment B raw41486step1 raw41486step1Labels = mixedMoment B raw41486step2 raw41486step2Labels := by
      have ha : raw41486step2 = (fun i j => raw41486step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41486step2 raw41486step1; decide +kernel
      have hl : raw41486step2Labels = raw41486step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41486step1 raw41486step1Labels permutation14 permutation6
    mixedMoment B raw41486step2 raw41486step2Labels = mixedMoment B raw41486step3 raw41486step3Labels := by
      have ha : raw41486step3 = -raw41486step2 := by apply Matrix.ext; change ∀ i j, raw41486step3 i j = -(raw41486step2 i j); unfold raw41486step3 raw41486step2; decide +kernel
      have hl : raw41486step3Labels = raw41486step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node934 node934Labels := by rfl

def raw41487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw41487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![2, -1, -1]]
def raw41487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41487step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![2, -1, -1]]
def raw41487step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41487step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41487step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41487 raw41487Labels = mixedMoment B node2116 node2116Labels := by
  calc
    mixedMoment B raw41487 raw41487Labels = mixedMoment B raw41487step0 raw41487step0Labels := by
      have hz : ∀ j, raw41487 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41487step0 = (fun i j => raw41487 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41487step0 raw41487; decide +kernel
      have hl : raw41487step0Labels = raw41487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41487 raw41487Labels permutation520 hz
    mixedMoment B raw41487step0 raw41487step0Labels = mixedMoment B raw41487step1 raw41487step1Labels := by
      have hz : ∀ j, raw41487step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41487step1 = (fun i j => raw41487step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41487step1 raw41487step0; decide +kernel
      have hl : raw41487step1Labels = raw41487step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41487step0 raw41487step0Labels permutation104 hz
    mixedMoment B raw41487step1 raw41487step1Labels = mixedMoment B raw41487step2 raw41487step2Labels := by
      have ha : raw41487step2 = (fun i j => raw41487step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41487step2 raw41487step1; decide +kernel
      have hl : raw41487step2Labels = raw41487step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41487step1 raw41487step1Labels permutation24 permutation6
    _ = mixedMoment B node2116 node2116Labels := by rfl

def raw41488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw41488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![2, 0, -2]]
def raw41488step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41488step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41488 raw41488Labels = mixedMoment B node1815 node1815Labels := by
  calc
    mixedMoment B raw41488 raw41488Labels = mixedMoment B raw41488step0 raw41488step0Labels := by
      have hz : ∀ j, raw41488 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41488step0 = (fun i j => raw41488 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41488step0 raw41488; decide +kernel
      have hl : raw41488step0Labels = raw41488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41488 raw41488Labels permutation434 hz
    mixedMoment B raw41488step0 raw41488step0Labels = mixedMoment B raw41488step1 raw41488step1Labels := by
      have ha : raw41488step1 = (fun i j => raw41488step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41488step1 raw41488step0; decide +kernel
      have hl : raw41488step1Labels = raw41488step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41488step0 raw41488step0Labels permutation102 permutation6
    _ = mixedMoment B node1815 node1815Labels := by rfl

def raw41489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw41489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0]]
def raw41489step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41489 raw41489Labels = mixedMoment B node2029 node2029Labels := by
  calc
    mixedMoment B raw41489 raw41489Labels = mixedMoment B raw41489step0 raw41489step0Labels := by
      have hz : ∀ j, raw41489 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41489step0 = (fun i j => raw41489 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41489step0 raw41489; decide +kernel
      have hl : raw41489step0Labels = raw41489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41489 raw41489Labels permutation434 hz
    mixedMoment B raw41489step0 raw41489step0Labels = mixedMoment B raw41489step1 raw41489step1Labels := by
      have ha : raw41489step1 = (fun i j => raw41489step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41489step1 raw41489step0; decide +kernel
      have hl : raw41489step1Labels = raw41489step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41489step0 raw41489step0Labels permutation96 permutation6
    _ = mixedMoment B node2029 node2029Labels := by rfl

def raw41490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41490step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41490 raw41490Labels = mixedMoment B node1967 node1967Labels := by
  calc
    mixedMoment B raw41490 raw41490Labels = mixedMoment B raw41490step0 raw41490step0Labels := by
      have ha : raw41490step0 = (fun i j => raw41490 (permutation413 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41490step0 raw41490; decide +kernel
      have hl : raw41490step0Labels = raw41490Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41490 raw41490Labels permutation413 permutation6
    _ = mixedMoment B node1967 node1967Labels := by rfl

def raw41491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw41491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41491 raw41491Labels = mixedMoment B node3709 node3709Labels := by
  calc
    mixedMoment B raw41491 raw41491Labels = mixedMoment B raw41491step0 raw41491step0Labels := by
      have ha : raw41491step0 = (fun i j => raw41491 (permutation426 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41491step0 raw41491; decide +kernel
      have hl : raw41491step0Labels = raw41491Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41491 raw41491Labels permutation426 permutation6
    _ = mixedMoment B node3709 node3709Labels := by rfl

def raw41492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41492step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41492step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41492 raw41492Labels = mixedMoment B node3779 node3779Labels := by
  calc
    mixedMoment B raw41492 raw41492Labels = mixedMoment B raw41492step0 raw41492step0Labels := by
      have ha : raw41492step0 = (fun i j => raw41492 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41492step0 raw41492; decide +kernel
      have hl : raw41492step0Labels = raw41492Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41492 raw41492Labels permutation393 permutation6
    _ = mixedMoment B node3779 node3779Labels := by rfl

def raw41493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw41493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![2, 1, -3]]
def raw41493step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41493step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41493 raw41493Labels = mixedMoment B node2818 node2818Labels := by
  calc
    mixedMoment B raw41493 raw41493Labels = mixedMoment B raw41493step0 raw41493step0Labels := by
      have hz : ∀ j, raw41493 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41493step0 = (fun i j => raw41493 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41493step0 raw41493; decide +kernel
      have hl : raw41493step0Labels = raw41493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41493 raw41493Labels permutation434 hz
    mixedMoment B raw41493step0 raw41493step0Labels = mixedMoment B raw41493step1 raw41493step1Labels := by
      have ha : raw41493step1 = (fun i j => raw41493step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41493step1 raw41493step0; decide +kernel
      have hl : raw41493step1Labels = raw41493step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41493step0 raw41493step0Labels permutation144 permutation6
    _ = mixedMoment B node2818 node2818Labels := by rfl

def raw41494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw41494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0]]
def raw41494step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41494 raw41494Labels = mixedMoment B node3694 node3694Labels := by
  calc
    mixedMoment B raw41494 raw41494Labels = mixedMoment B raw41494step0 raw41494step0Labels := by
      have hz : ∀ j, raw41494 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41494step0 = (fun i j => raw41494 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41494step0 raw41494; decide +kernel
      have hl : raw41494step0Labels = raw41494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41494 raw41494Labels permutation434 hz
    mixedMoment B raw41494step0 raw41494step0Labels = mixedMoment B raw41494step1 raw41494step1Labels := by
      have ha : raw41494step1 = (fun i j => raw41494step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41494step1 raw41494step0; decide +kernel
      have hl : raw41494step1Labels = raw41494step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41494step0 raw41494step0Labels permutation96 permutation6
    _ = mixedMoment B node3694 node3694Labels := by rfl

def raw41495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw41495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41495step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41495 raw41495Labels = mixedMoment B node3672 node3672Labels := by
  calc
    mixedMoment B raw41495 raw41495Labels = mixedMoment B raw41495step0 raw41495step0Labels := by
      have ha : raw41495step0 = (fun i j => raw41495 (permutation413 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41495step0 raw41495; decide +kernel
      have hl : raw41495step0Labels = raw41495Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41495 raw41495Labels permutation413 permutation6
    _ = mixedMoment B node3672 node3672Labels := by rfl

def raw41496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 2, -4]]
def raw41496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![2, 2, -4]]
def raw41496step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41496 raw41496Labels = mixedMoment B node1139 node1139Labels := by
  calc
    mixedMoment B raw41496 raw41496Labels = mixedMoment B raw41496step0 raw41496step0Labels := by
      have hz : ∀ j, raw41496 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41496step0 = (fun i j => raw41496 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41496step0 raw41496; decide +kernel
      have hl : raw41496step0Labels = raw41496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41496 raw41496Labels permutation434 hz
    mixedMoment B raw41496step0 raw41496step0Labels = mixedMoment B raw41496step1 raw41496step1Labels := by
      have ha : raw41496step1 = (fun i j => raw41496step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41496step1 raw41496step0; decide +kernel
      have hl : raw41496step1Labels = raw41496step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41496step0 raw41496step0Labels permutation144 permutation6
    _ = mixedMoment B node1139 node1139Labels := by rfl

def raw41497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0]]
def raw41497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0]]
def raw41497step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41497 raw41497Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw41497 raw41497Labels = mixedMoment B raw41497step0 raw41497step0Labels := by
      have hz : ∀ j, raw41497 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41497step0 = (fun i j => raw41497 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41497step0 raw41497; decide +kernel
      have hl : raw41497step0Labels = raw41497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41497 raw41497Labels permutation434 hz
    mixedMoment B raw41497step0 raw41497step0Labels = mixedMoment B raw41497step1 raw41497step1Labels := by
      have ha : raw41497step1 = (fun i j => raw41497step0 (permutation120 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41497step1 raw41497step0; decide +kernel
      have hl : raw41497step1Labels = raw41497step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41497step0 raw41497step0Labels permutation120 permutation6
    _ = mixedMoment B node2489 node2489Labels := by rfl

def raw41498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1]]
def raw41498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41498 raw41498Labels = mixedMoment B node2432 node2432Labels := by
  calc
    mixedMoment B raw41498 raw41498Labels = mixedMoment B raw41498step0 raw41498step0Labels := by
      have ha : raw41498step0 = (fun i j => raw41498 (permutation551 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41498step0 raw41498; decide +kernel
      have hl : raw41498step0Labels = raw41498Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41498 raw41498Labels permutation551 permutation6
    _ = mixedMoment B node2432 node2432Labels := by rfl

def raw41499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw41499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 3, -5]]
def raw41499step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41499step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![2, 3, -5]]
def raw41499step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41499step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41499step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41499 raw41499Labels = mixedMoment B node614 node614Labels := by
  calc
    mixedMoment B raw41499 raw41499Labels = mixedMoment B raw41499step0 raw41499step0Labels := by
      have hz : ∀ j, raw41499 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41499step0 = (fun i j => raw41499 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41499step0 raw41499; decide +kernel
      have hl : raw41499step0Labels = raw41499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41499 raw41499Labels permutation434 hz
    mixedMoment B raw41499step0 raw41499step0Labels = mixedMoment B raw41499step1 raw41499step1Labels := by
      have hz : ∀ j, raw41499step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41499step1 = (fun i j => raw41499step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41499step1 raw41499step0; decide +kernel
      have hl : raw41499step1Labels = raw41499step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41499step0 raw41499step0Labels permutation80 hz
    mixedMoment B raw41499step1 raw41499step1Labels = mixedMoment B raw41499step2 raw41499step2Labels := by
      have ha : raw41499step2 = (fun i j => raw41499step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41499step2 raw41499step1; decide +kernel
      have hl : raw41499step2Labels = raw41499step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41499step1 raw41499step1Labels permutation30 permutation6
    _ = mixedMoment B node614 node614Labels := by rfl

def raw41500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0]]
def raw41500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![1, -1, 0]]
def raw41500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41500step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 3, -4], ![1, -1, 0]]
def raw41500step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41500step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41500 raw41500Labels = mixedMoment B node1050 node1050Labels := by
  calc
    mixedMoment B raw41500 raw41500Labels = mixedMoment B raw41500step0 raw41500step0Labels := by
      have hz : ∀ j, raw41500 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41500step0 = (fun i j => raw41500 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41500step0 raw41500; decide +kernel
      have hl : raw41500step0Labels = raw41500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41500 raw41500Labels permutation434 hz
    mixedMoment B raw41500step0 raw41500step0Labels = mixedMoment B raw41500step1 raw41500step1Labels := by
      have hz : ∀ j, raw41500step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41500step1 = (fun i j => raw41500step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41500step1 raw41500step0; decide +kernel
      have hl : raw41500step1Labels = raw41500step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41500step0 raw41500step0Labels permutation80 hz
    mixedMoment B raw41500step1 raw41500step1Labels = mixedMoment B raw41500step2 raw41500step2Labels := by
      have ha : raw41500step2 = (fun i j => raw41500step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41500step2 raw41500step1; decide +kernel
      have hl : raw41500step2Labels = raw41500step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41500step1 raw41500step1Labels permutation24 permutation6
    _ = mixedMoment B node1050 node1050Labels := by rfl

def raw41501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw41501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 3, -4], ![1, 0, -1]]
def raw41501step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41501 raw41501Labels = mixedMoment B node933 node933Labels := by
  calc
    mixedMoment B raw41501 raw41501Labels = mixedMoment B raw41501step0 raw41501step0Labels := by
      have hz : ∀ j, raw41501 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41501step0 = (fun i j => raw41501 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41501step0 raw41501; decide +kernel
      have hl : raw41501step0Labels = raw41501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41501 raw41501Labels permutation346 hz
    mixedMoment B raw41501step0 raw41501step0Labels = mixedMoment B raw41501step1 raw41501step1Labels := by
      have ha : raw41501step1 = (fun i j => raw41501step0 (permutation126 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41501step1 raw41501step0; decide +kernel
      have hl : raw41501step1Labels = raw41501step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41501step0 raw41501step0Labels permutation126 permutation6
    _ = mixedMoment B node933 node933Labels := by rfl

def raw41502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2]]
def raw41502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 2, -3], ![1, 1, -2]]
def raw41502step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw41502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41502 raw41502Labels = mixedMoment B node2342 node2342Labels := by
  calc
    mixedMoment B raw41502 raw41502Labels = mixedMoment B raw41502step0 raw41502step0Labels := by
      have hz : ∀ j, raw41502 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41502step0 = (fun i j => raw41502 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41502step0 raw41502; decide +kernel
      have hl : raw41502step0Labels = raw41502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41502 raw41502Labels permutation346 hz
    mixedMoment B raw41502step0 raw41502step0Labels = mixedMoment B raw41502step1 raw41502step1Labels := by
      have ha : raw41502step1 = (fun i j => raw41502step0 (permutation126 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41502step1 raw41502step0; decide +kernel
      have hl : raw41502step1Labels = raw41502step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41502step0 raw41502step0Labels permutation126 permutation6
    _ = mixedMoment B node2342 node2342Labels := by rfl

def raw41503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw41503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![2, 0, -2]]
def raw41503step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41503step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 3, -3], ![2, 0, -2]]
def raw41503step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41503step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw41503step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41503 raw41503Labels = mixedMoment B node1818 node1818Labels := by
  calc
    mixedMoment B raw41503 raw41503Labels = mixedMoment B raw41503step0 raw41503step0Labels := by
      have hz : ∀ j, raw41503 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41503step0 = (fun i j => raw41503 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41503step0 raw41503; decide +kernel
      have hl : raw41503step0Labels = raw41503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41503 raw41503Labels permutation520 hz
    mixedMoment B raw41503step0 raw41503step0Labels = mixedMoment B raw41503step1 raw41503step1Labels := by
      have hz : ∀ j, raw41503step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41503step1 = (fun i j => raw41503step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41503step1 raw41503step0; decide +kernel
      have hl : raw41503step1Labels = raw41503step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41503step0 raw41503step0Labels permutation104 hz
    mixedMoment B raw41503step1 raw41503step1Labels = mixedMoment B raw41503step2 raw41503step2Labels := by
      have ha : raw41503step2 = (fun i j => raw41503step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41503step2 raw41503step1; decide +kernel
      have hl : raw41503step2Labels = raw41503step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41503step1 raw41503step1Labels permutation24 permutation6
    _ = mixedMoment B node1818 node1818Labels := by rfl

def raw41504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw41504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![2, 0, -2]]
def raw41504step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41504step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw41504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41504step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw41504step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41504 raw41504Labels = mixedMoment B node2341 node2341Labels := by
  calc
    mixedMoment B raw41504 raw41504Labels = mixedMoment B raw41504step0 raw41504step0Labels := by
      have hz : ∀ j, raw41504 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41504step0 = (fun i j => raw41504 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41504step0 raw41504; decide +kernel
      have hl : raw41504step0Labels = raw41504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41504 raw41504Labels permutation520 hz
    mixedMoment B raw41504step0 raw41504step0Labels = mixedMoment B raw41504step1 raw41504step1Labels := by
      have ha : raw41504step1 = (fun i j => raw41504step0 (permutation59 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41504step1 raw41504step0; decide +kernel
      have hl : raw41504step1Labels = raw41504step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41504step0 raw41504step0Labels permutation59 permutation6
    mixedMoment B raw41504step1 raw41504step1Labels = mixedMoment B raw41504step2 raw41504step2Labels := by
      have ha : raw41504step2 = -raw41504step1 := by apply Matrix.ext; change ∀ i j, raw41504step2 i j = -(raw41504step1 i j); unfold raw41504step2 raw41504step1; decide +kernel
      have hl : raw41504step2Labels = raw41504step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2341 node2341Labels := by rfl

def raw41505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw41505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41505step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw41505step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41505 raw41505Labels = mixedMoment B node2330 node2330Labels := by
  calc
    mixedMoment B raw41505 raw41505Labels = mixedMoment B raw41505step0 raw41505step0Labels := by
      have ha : raw41505step0 = (fun i j => raw41505 (permutation282 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41505step0 raw41505; decide +kernel
      have hl : raw41505step0Labels = raw41505Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41505 raw41505Labels permutation282 permutation6
    mixedMoment B raw41505step0 raw41505step0Labels = mixedMoment B raw41505step1 raw41505step1Labels := by
      have ha : raw41505step1 = -raw41505step0 := by apply Matrix.ext; change ∀ i j, raw41505step1 i j = -(raw41505step0 i j); unfold raw41505step1 raw41505step0; decide +kernel
      have hl : raw41505step1Labels = raw41505step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2330 node2330Labels := by rfl

def raw41506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3]]
def raw41506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![2, 1, -3]]
def raw41506step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41506step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![2, 1, -3]]
def raw41506step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41506step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw41506step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41506step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw41506step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41506 raw41506Labels = mixedMoment B node2345 node2345Labels := by
  calc
    mixedMoment B raw41506 raw41506Labels = mixedMoment B raw41506step0 raw41506step0Labels := by
      have hz : ∀ j, raw41506 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41506step0 = (fun i j => raw41506 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41506step0 raw41506; decide +kernel
      have hl : raw41506step0Labels = raw41506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41506 raw41506Labels permutation520 hz
    mixedMoment B raw41506step0 raw41506step0Labels = mixedMoment B raw41506step1 raw41506step1Labels := by
      have hz : ∀ j, raw41506step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41506step1 = (fun i j => raw41506step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41506step1 raw41506step0; decide +kernel
      have hl : raw41506step1Labels = raw41506step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41506step0 raw41506step0Labels permutation104 hz
    mixedMoment B raw41506step1 raw41506step1Labels = mixedMoment B raw41506step2 raw41506step2Labels := by
      have ha : raw41506step2 = (fun i j => raw41506step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41506step2 raw41506step1; decide +kernel
      have hl : raw41506step2Labels = raw41506step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41506step1 raw41506step1Labels permutation14 permutation6
    mixedMoment B raw41506step2 raw41506step2Labels = mixedMoment B raw41506step3 raw41506step3Labels := by
      have ha : raw41506step3 = -raw41506step2 := by apply Matrix.ext; change ∀ i j, raw41506step3 i j = -(raw41506step2 i j); unfold raw41506step3 raw41506step2; decide +kernel
      have hl : raw41506step3Labels = raw41506step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2345 node2345Labels := by rfl

def raw41507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1]]
def raw41507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1]]
def raw41507step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw41507step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41507step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw41507step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41507 raw41507Labels = mixedMoment B node2337 node2337Labels := by
  calc
    mixedMoment B raw41507 raw41507Labels = mixedMoment B raw41507step0 raw41507step0Labels := by
      have hz : ∀ j, raw41507 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41507step0 = (fun i j => raw41507 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41507step0 raw41507; decide +kernel
      have hl : raw41507step0Labels = raw41507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41507 raw41507Labels permutation434 hz
    mixedMoment B raw41507step0 raw41507step0Labels = mixedMoment B raw41507step1 raw41507step1Labels := by
      have ha : raw41507step1 = (fun i j => raw41507step0 (permutation61 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41507step1 raw41507step0; decide +kernel
      have hl : raw41507step1Labels = raw41507step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41507step0 raw41507step0Labels permutation61 permutation6
    mixedMoment B raw41507step1 raw41507step1Labels = mixedMoment B raw41507step2 raw41507step2Labels := by
      have ha : raw41507step2 = -raw41507step1 := by apply Matrix.ext; change ∀ i j, raw41507step2 i j = -(raw41507step1 i j); unfold raw41507step2 raw41507step1; decide +kernel
      have hl : raw41507step2Labels = raw41507step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2337 node2337Labels := by rfl

def raw41508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw41508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41508step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41508 raw41508Labels = mixedMoment B node2338 node2338Labels := by
  calc
    mixedMoment B raw41508 raw41508Labels = mixedMoment B raw41508step0 raw41508step0Labels := by
      have ha : raw41508step0 = (fun i j => raw41508 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41508step0 raw41508; decide +kernel
      have hl : raw41508step0Labels = raw41508Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41508 raw41508Labels permutation265 permutation6
    mixedMoment B raw41508step0 raw41508step0Labels = mixedMoment B raw41508step1 raw41508step1Labels := by
      have ha : raw41508step1 = -raw41508step0 := by apply Matrix.ext; change ∀ i j, raw41508step1 i j = -(raw41508step0 i j); unfold raw41508step1 raw41508step0; decide +kernel
      have hl : raw41508step1Labels = raw41508step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2338 node2338Labels := by rfl

def raw41509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, 1, -3]]
def raw41509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![2, 1, -3]]
def raw41509step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw41509step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41509step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw41509step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41509 raw41509Labels = mixedMoment B node2339 node2339Labels := by
  calc
    mixedMoment B raw41509 raw41509Labels = mixedMoment B raw41509step0 raw41509step0Labels := by
      have hz : ∀ j, raw41509 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41509step0 = (fun i j => raw41509 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41509step0 raw41509; decide +kernel
      have hl : raw41509step0Labels = raw41509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41509 raw41509Labels permutation520 hz
    mixedMoment B raw41509step0 raw41509step0Labels = mixedMoment B raw41509step1 raw41509step1Labels := by
      have ha : raw41509step1 = (fun i j => raw41509step0 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41509step1 raw41509step0; decide +kernel
      have hl : raw41509step1Labels = raw41509step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41509step0 raw41509step0Labels permutation56 permutation6
    mixedMoment B raw41509step1 raw41509step1Labels = mixedMoment B raw41509step2 raw41509step2Labels := by
      have ha : raw41509step2 = -raw41509step1 := by apply Matrix.ext; change ∀ i j, raw41509step2 i j = -(raw41509step1 i j); unfold raw41509step2 raw41509step1; decide +kernel
      have hl : raw41509step2Labels = raw41509step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2339 node2339Labels := by rfl

def raw41510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 2, -4]]
def raw41510Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![2, 2, -4]]
def raw41510step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41510step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 1, -1], ![2, 2, -4]]
def raw41510step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41510step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw41510step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41510 raw41510Labels = mixedMoment B node1144 node1144Labels := by
  calc
    mixedMoment B raw41510 raw41510Labels = mixedMoment B raw41510step0 raw41510step0Labels := by
      have hz : ∀ j, raw41510 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41510step0 = (fun i j => raw41510 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41510step0 raw41510; decide +kernel
      have hl : raw41510step0Labels = raw41510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41510 raw41510Labels permutation520 hz
    mixedMoment B raw41510step0 raw41510step0Labels = mixedMoment B raw41510step1 raw41510step1Labels := by
      have hz : ∀ j, raw41510step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41510step1 = (fun i j => raw41510step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41510step1 raw41510step0; decide +kernel
      have hl : raw41510step1Labels = raw41510step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41510step0 raw41510step0Labels permutation104 hz
    mixedMoment B raw41510step1 raw41510step1Labels = mixedMoment B raw41510step2 raw41510step2Labels := by
      have ha : raw41510step2 = (fun i j => raw41510step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41510step2 raw41510step1; decide +kernel
      have hl : raw41510step2Labels = raw41510step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41510step1 raw41510step1Labels permutation30 permutation6
    _ = mixedMoment B node1144 node1144Labels := by rfl

def raw41511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1]]
def raw41511Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1]]
def raw41511step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw41511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw41511step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw41511step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41511 raw41511Labels = mixedMoment B node2334 node2334Labels := by
  calc
    mixedMoment B raw41511 raw41511Labels = mixedMoment B raw41511step0 raw41511step0Labels := by
      have hz : ∀ j, raw41511 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41511step0 = (fun i j => raw41511 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41511step0 raw41511; decide +kernel
      have hl : raw41511step0Labels = raw41511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41511 raw41511Labels permutation434 hz
    mixedMoment B raw41511step0 raw41511step0Labels = mixedMoment B raw41511step1 raw41511step1Labels := by
      have ha : raw41511step1 = (fun i j => raw41511step0 (permutation60 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41511step1 raw41511step0; decide +kernel
      have hl : raw41511step1Labels = raw41511step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41511step0 raw41511step0Labels permutation60 permutation6
    mixedMoment B raw41511step1 raw41511step1Labels = mixedMoment B raw41511step2 raw41511step2Labels := by
      have ha : raw41511step2 = -raw41511step1 := by apply Matrix.ext; change ∀ i j, raw41511step2 i j = -(raw41511step1 i j); unfold raw41511step2 raw41511step1; decide +kernel
      have hl : raw41511step2Labels = raw41511step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2334 node2334Labels := by rfl

def raw41512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 3, -5]]
def raw41512Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 3, -5]]
def raw41512step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41512step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 0, 0], ![2, 3, -5]]
def raw41512step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41512step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![2, 3, -5]]
def raw41512step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41512step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw41512step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41512 raw41512Labels = mixedMoment B node619 node619Labels := by
  calc
    mixedMoment B raw41512 raw41512Labels = mixedMoment B raw41512step0 raw41512step0Labels := by
      have hz : ∀ j, raw41512 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41512step0 = (fun i j => raw41512 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41512step0 raw41512; decide +kernel
      have hl : raw41512step0Labels = raw41512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41512 raw41512Labels permutation520 hz
    mixedMoment B raw41512step0 raw41512step0Labels = mixedMoment B raw41512step1 raw41512step1Labels := by
      have hz : ∀ j, raw41512step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41512step1 = (fun i j => raw41512step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41512step1 raw41512step0; decide +kernel
      have hl : raw41512step1Labels = raw41512step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41512step0 raw41512step0Labels permutation104 hz
    mixedMoment B raw41512step1 raw41512step1Labels = mixedMoment B raw41512step2 raw41512step2Labels := by
      have hz : ∀ j, raw41512step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41512step2 = (fun i j => raw41512step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41512step2 raw41512step1; decide +kernel
      have hl : raw41512step2Labels = raw41512step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41512step1 raw41512step1Labels permutation20 hz
    mixedMoment B raw41512step2 raw41512step2Labels = mixedMoment B raw41512step3 raw41512step3Labels := by
      have ha : raw41512step3 = (fun i j => raw41512step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41512step3 raw41512step2; decide +kernel
      have hl : raw41512step3Labels = raw41512step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41512step2 raw41512step2Labels permutation6 permutation6
    _ = mixedMoment B node619 node619Labels := by rfl

def raw41513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2]]
def raw41513Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![0, 0, 0], ![1, 2, -3], ![1, 1, -2]]
def raw41513step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -2, 3], ![1, 2, -3], ![1, 1, -2]]
def raw41513step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw41513step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw41513step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41513 raw41513Labels = mixedMoment B node2344 node2344Labels := by
  calc
    mixedMoment B raw41513 raw41513Labels = mixedMoment B raw41513step0 raw41513step0Labels := by
      have hz : ∀ j, raw41513 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41513step0 = (fun i j => raw41513 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41513step0 raw41513; decide +kernel
      have hl : raw41513step0Labels = raw41513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41513 raw41513Labels permutation434 hz
    mixedMoment B raw41513step0 raw41513step0Labels = mixedMoment B raw41513step1 raw41513step1Labels := by
      have hz : ∀ j, raw41513step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41513step1 = (fun i j => raw41513step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41513step1 raw41513step0; decide +kernel
      have hl : raw41513step1Labels = raw41513step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41513step0 raw41513step0Labels permutation80 hz
    mixedMoment B raw41513step1 raw41513step1Labels = mixedMoment B raw41513step2 raw41513step2Labels := by
      have ha : raw41513step2 = (fun i j => raw41513step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw41513step2 raw41513step1; decide +kernel
      have hl : raw41513step2Labels = raw41513step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41513step1 raw41513step1Labels permutation24 permutation6
    _ = mixedMoment B node2344 node2344Labels := by rfl

def raw41514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41514Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41514step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41514step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41514step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41514step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41514step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 3, 0], ![3, -3, 0]]
def raw41514step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41514step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw41514step4Labels : Fin 2 → Fin 2 := ![1, 1]

def raw41514step5 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw41514step5Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical41514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41514 raw41514Labels = mixedMoment B node2 node2Labels := by
  calc
    mixedMoment B raw41514 raw41514Labels = mixedMoment B raw41514step0 raw41514step0Labels := by
      have hz : ∀ j, raw41514 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41514step0 = (fun i j => raw41514 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41514step0 raw41514; decide +kernel
      have hl : raw41514step0Labels = raw41514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41514 raw41514Labels permutation520 hz
    mixedMoment B raw41514step0 raw41514step0Labels = mixedMoment B raw41514step1 raw41514step1Labels := by
      have hz : ∀ j, raw41514step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41514step1 = (fun i j => raw41514step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41514step1 raw41514step0; decide +kernel
      have hl : raw41514step1Labels = raw41514step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41514step0 raw41514step0Labels permutation104 hz
    mixedMoment B raw41514step1 raw41514step1Labels = mixedMoment B raw41514step2 raw41514step2Labels := by
      have hz : ∀ j, raw41514step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41514step2 = (fun i j => raw41514step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41514step2 raw41514step1; decide +kernel
      have hl : raw41514step2Labels = raw41514step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41514step1 raw41514step1Labels permutation20 hz
    mixedMoment B raw41514step2 raw41514step2Labels = mixedMoment B raw41514step3 raw41514step3Labels := by
      have hz : ∀ j, raw41514step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw41514step3 = (fun i j => raw41514step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw41514step3 raw41514step2; decide +kernel
      have hl : raw41514step3Labels = raw41514step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41514step2 raw41514step2Labels permutation4 hz
    mixedMoment B raw41514step3 raw41514step3Labels = mixedMoment B raw41514step4 raw41514step4Labels := by
      have hz : ∀ i, raw41514step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw41514step4 = (fun i j => raw41514step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw41514step4 raw41514step3; decide +kernel
      have hl : raw41514step4Labels = (fun j => raw41514step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw41514step3 raw41514step3Labels permutation6 hz
    mixedMoment B raw41514step4 raw41514step4Labels = mixedMoment B raw41514step5 raw41514step5Labels := by
      have ha : raw41514step5 = raw41514step4 := by apply Matrix.ext; unfold raw41514step5 raw41514step4; decide +kernel
      have hl : raw41514step4Labels = labelEmbedding0 ∘ raw41514step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41514step4 raw41514step4Labels raw41514step5Labels labelEmbedding0 hl
    _ = mixedMoment B node2 node2Labels := by rfl

def raw41515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41515Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41515step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41515step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41515step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41515step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41515step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 3, 0], ![3, -3, 0]]
def raw41515step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41515step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw41515step4Labels : Fin 2 → Fin 3 := ![1, 2]

def raw41515step5 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw41515step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical41515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41515 raw41515Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw41515 raw41515Labels = mixedMoment B raw41515step0 raw41515step0Labels := by
      have hz : ∀ j, raw41515 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41515step0 = (fun i j => raw41515 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41515step0 raw41515; decide +kernel
      have hl : raw41515step0Labels = raw41515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41515 raw41515Labels permutation520 hz
    mixedMoment B raw41515step0 raw41515step0Labels = mixedMoment B raw41515step1 raw41515step1Labels := by
      have hz : ∀ j, raw41515step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41515step1 = (fun i j => raw41515step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41515step1 raw41515step0; decide +kernel
      have hl : raw41515step1Labels = raw41515step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41515step0 raw41515step0Labels permutation104 hz
    mixedMoment B raw41515step1 raw41515step1Labels = mixedMoment B raw41515step2 raw41515step2Labels := by
      have hz : ∀ j, raw41515step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41515step2 = (fun i j => raw41515step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41515step2 raw41515step1; decide +kernel
      have hl : raw41515step2Labels = raw41515step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41515step1 raw41515step1Labels permutation20 hz
    mixedMoment B raw41515step2 raw41515step2Labels = mixedMoment B raw41515step3 raw41515step3Labels := by
      have hz : ∀ j, raw41515step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw41515step3 = (fun i j => raw41515step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw41515step3 raw41515step2; decide +kernel
      have hl : raw41515step3Labels = raw41515step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41515step2 raw41515step2Labels permutation4 hz
    mixedMoment B raw41515step3 raw41515step3Labels = mixedMoment B raw41515step4 raw41515step4Labels := by
      have hz : ∀ i, raw41515step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw41515step4 = (fun i j => raw41515step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw41515step4 raw41515step3; decide +kernel
      have hl : raw41515step4Labels = (fun j => raw41515step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw41515step3 raw41515step3Labels permutation6 hz
    mixedMoment B raw41515step4 raw41515step4Labels = mixedMoment B raw41515step5 raw41515step5Labels := by
      have ha : raw41515step5 = raw41515step4 := by apply Matrix.ext; unfold raw41515step5 raw41515step4; decide +kernel
      have hl : raw41515step4Labels = labelEmbedding3 ∘ raw41515step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41515step4 raw41515step4Labels raw41515step5Labels labelEmbedding3 hl
    _ = mixedMoment B node4085 node4085Labels := by rfl

def raw41516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41516Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41516step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41516step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41516step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41516step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41516step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw41516step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41516step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw41516step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41516 raw41516Labels = mixedMoment B node3114 node3114Labels := by
  calc
    mixedMoment B raw41516 raw41516Labels = mixedMoment B raw41516step0 raw41516step0Labels := by
      have hz : ∀ j, raw41516 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41516step0 = (fun i j => raw41516 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41516step0 raw41516; decide +kernel
      have hl : raw41516step0Labels = raw41516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41516 raw41516Labels permutation434 hz
    mixedMoment B raw41516step0 raw41516step0Labels = mixedMoment B raw41516step1 raw41516step1Labels := by
      have hz : ∀ j, raw41516step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41516step1 = (fun i j => raw41516step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41516step1 raw41516step0; decide +kernel
      have hl : raw41516step1Labels = raw41516step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41516step0 raw41516step0Labels permutation80 hz
    mixedMoment B raw41516step1 raw41516step1Labels = mixedMoment B raw41516step2 raw41516step2Labels := by
      have hz : ∀ j, raw41516step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41516step2 = (fun i j => raw41516step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41516step2 raw41516step1; decide +kernel
      have hl : raw41516step2Labels = raw41516step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41516step1 raw41516step1Labels permutation14 hz
    mixedMoment B raw41516step2 raw41516step2Labels = mixedMoment B raw41516step3 raw41516step3Labels := by
      have ha : raw41516step3 = (fun i j => raw41516step2 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41516step3 raw41516step2; decide +kernel
      have hl : raw41516step3Labels = raw41516step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41516step2 raw41516step2Labels permutation7 permutation4
    mixedMoment B raw41516step3 raw41516step3Labels = mixedMoment B raw41516step4 raw41516step4Labels := by
      have ha : raw41516step4 = raw41516step3 := by apply Matrix.ext; unfold raw41516step4 raw41516step3; decide +kernel
      have hl : raw41516step3Labels = labelEmbedding1 ∘ raw41516step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41516step3 raw41516step3Labels raw41516step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3114 node3114Labels := by rfl

def raw41517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41517Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41517step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41517step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41517step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41517step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41517step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41517step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw41517step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41517step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw41517step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41517step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw41517step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41517 raw41517Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw41517 raw41517Labels = mixedMoment B raw41517step0 raw41517step0Labels := by
      have hz : ∀ j, raw41517 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41517step0 = (fun i j => raw41517 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41517step0 raw41517; decide +kernel
      have hl : raw41517step0Labels = raw41517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41517 raw41517Labels permutation434 hz
    mixedMoment B raw41517step0 raw41517step0Labels = mixedMoment B raw41517step1 raw41517step1Labels := by
      have hz : ∀ j, raw41517step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41517step1 = (fun i j => raw41517step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41517step1 raw41517step0; decide +kernel
      have hl : raw41517step1Labels = raw41517step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41517step0 raw41517step0Labels permutation80 hz
    mixedMoment B raw41517step1 raw41517step1Labels = mixedMoment B raw41517step2 raw41517step2Labels := by
      have hz : ∀ j, raw41517step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41517step2 = (fun i j => raw41517step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41517step2 raw41517step1; decide +kernel
      have hl : raw41517step2Labels = raw41517step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41517step1 raw41517step1Labels permutation14 hz
    mixedMoment B raw41517step2 raw41517step2Labels = mixedMoment B raw41517step3 raw41517step3Labels := by
      have ha : raw41517step3 = (fun i j => raw41517step2 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41517step3 raw41517step2; decide +kernel
      have hl : raw41517step3Labels = raw41517step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41517step2 raw41517step2Labels permutation2 permutation5
    mixedMoment B raw41517step3 raw41517step3Labels = mixedMoment B raw41517step4 raw41517step4Labels := by
      have ha : raw41517step4 = -raw41517step3 := by apply Matrix.ext; change ∀ i j, raw41517step4 i j = -(raw41517step3 i j); unfold raw41517step4 raw41517step3; decide +kernel
      have hl : raw41517step4Labels = raw41517step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41517step4 raw41517step4Labels = mixedMoment B raw41517step5 raw41517step5Labels := by
      have ha : raw41517step5 = raw41517step4 := by apply Matrix.ext; unfold raw41517step5 raw41517step4; decide +kernel
      have hl : raw41517step4Labels = labelEmbedding9 ∘ raw41517step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41517step4 raw41517step4Labels raw41517step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

def raw41518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41518Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41518step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41518step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41518step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41518step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41518step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41518step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw41518step3Labels : Fin 2 → Fin 2 := ![1, 1]

def raw41518step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw41518step4Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical41518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41518 raw41518Labels = mixedMoment B node1 node1Labels := by
  calc
    mixedMoment B raw41518 raw41518Labels = mixedMoment B raw41518step0 raw41518step0Labels := by
      have hz : ∀ j, raw41518 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41518step0 = (fun i j => raw41518 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41518step0 raw41518; decide +kernel
      have hl : raw41518step0Labels = raw41518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41518 raw41518Labels permutation434 hz
    mixedMoment B raw41518step0 raw41518step0Labels = mixedMoment B raw41518step1 raw41518step1Labels := by
      have hz : ∀ j, raw41518step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41518step1 = (fun i j => raw41518step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41518step1 raw41518step0; decide +kernel
      have hl : raw41518step1Labels = raw41518step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41518step0 raw41518step0Labels permutation80 hz
    mixedMoment B raw41518step1 raw41518step1Labels = mixedMoment B raw41518step2 raw41518step2Labels := by
      have hz : ∀ j, raw41518step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41518step2 = (fun i j => raw41518step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41518step2 raw41518step1; decide +kernel
      have hl : raw41518step2Labels = raw41518step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41518step1 raw41518step1Labels permutation14 hz
    mixedMoment B raw41518step2 raw41518step2Labels = mixedMoment B raw41518step3 raw41518step3Labels := by
      have hz : ∀ i, raw41518step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw41518step3 = (fun i j => raw41518step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw41518step3 raw41518step2; decide +kernel
      have hl : raw41518step3Labels = (fun j => raw41518step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw41518step2 raw41518step2Labels permutation6 hz
    mixedMoment B raw41518step3 raw41518step3Labels = mixedMoment B raw41518step4 raw41518step4Labels := by
      have ha : raw41518step4 = raw41518step3 := by apply Matrix.ext; unfold raw41518step4 raw41518step3; decide +kernel
      have hl : raw41518step3Labels = labelEmbedding0 ∘ raw41518step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41518step3 raw41518step3Labels raw41518step4Labels labelEmbedding0 hl
    _ = mixedMoment B node1 node1Labels := by rfl

def raw41519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41519Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41519step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41519step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41519step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41519step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41519step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw41519step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw41519step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw41519step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical41519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41519 raw41519Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw41519 raw41519Labels = mixedMoment B raw41519step0 raw41519step0Labels := by
      have hz : ∀ j, raw41519 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41519step0 = (fun i j => raw41519 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41519step0 raw41519; decide +kernel
      have hl : raw41519step0Labels = raw41519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41519 raw41519Labels permutation434 hz
    mixedMoment B raw41519step0 raw41519step0Labels = mixedMoment B raw41519step1 raw41519step1Labels := by
      have hz : ∀ j, raw41519step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41519step1 = (fun i j => raw41519step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41519step1 raw41519step0; decide +kernel
      have hl : raw41519step1Labels = raw41519step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41519step0 raw41519step0Labels permutation80 hz
    mixedMoment B raw41519step1 raw41519step1Labels = mixedMoment B raw41519step2 raw41519step2Labels := by
      have hz : ∀ j, raw41519step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41519step2 = (fun i j => raw41519step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41519step2 raw41519step1; decide +kernel
      have hl : raw41519step2Labels = raw41519step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41519step1 raw41519step1Labels permutation14 hz
    mixedMoment B raw41519step2 raw41519step2Labels = mixedMoment B raw41519step3 raw41519step3Labels := by
      have hz : ∀ i, raw41519step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw41519step3 = (fun i j => raw41519step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw41519step3 raw41519step2; decide +kernel
      have hl : raw41519step3Labels = (fun j => raw41519step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw41519step2 raw41519step2Labels permutation6 hz
    mixedMoment B raw41519step3 raw41519step3Labels = mixedMoment B raw41519step4 raw41519step4Labels := by
      have ha : raw41519step4 = raw41519step3 := by apply Matrix.ext; unfold raw41519step4 raw41519step3; decide +kernel
      have hl : raw41519step3Labels = labelEmbedding3 ∘ raw41519step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41519step3 raw41519step3Labels raw41519step4Labels labelEmbedding3 hl
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw41520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41520Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41520step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41520step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41520step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41520step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41520step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41520step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41520 raw41520Labels = mixedMoment B node3231 node3231Labels := by
  calc
    mixedMoment B raw41520 raw41520Labels = mixedMoment B raw41520step0 raw41520step0Labels := by
      have hz : ∀ j, raw41520 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41520step0 = (fun i j => raw41520 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41520step0 raw41520; decide +kernel
      have hl : raw41520step0Labels = raw41520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41520 raw41520Labels permutation434 hz
    mixedMoment B raw41520step0 raw41520step0Labels = mixedMoment B raw41520step1 raw41520step1Labels := by
      have hz : ∀ j, raw41520step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41520step1 = (fun i j => raw41520step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41520step1 raw41520step0; decide +kernel
      have hl : raw41520step1Labels = raw41520step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41520step0 raw41520step0Labels permutation80 hz
    mixedMoment B raw41520step1 raw41520step1Labels = mixedMoment B raw41520step2 raw41520step2Labels := by
      have hz : ∀ j, raw41520step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41520step2 = (fun i j => raw41520step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41520step2 raw41520step1; decide +kernel
      have hl : raw41520step2Labels = raw41520step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41520step1 raw41520step1Labels permutation14 hz
    mixedMoment B raw41520step2 raw41520step2Labels = mixedMoment B raw41520step3 raw41520step3Labels := by
      have ha : raw41520step3 = raw41520step2 := by apply Matrix.ext; unfold raw41520step3 raw41520step2; decide +kernel
      have hl : raw41520step2Labels = labelEmbedding1 ∘ raw41520step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41520step2 raw41520step2Labels raw41520step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3231 node3231Labels := by rfl

def raw41521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41521Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41521step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41521step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41521step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41521step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41521step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41521step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw41521step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41521step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw41521step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41521 raw41521Labels = mixedMoment B node4901 node4901Labels := by
  calc
    mixedMoment B raw41521 raw41521Labels = mixedMoment B raw41521step0 raw41521step0Labels := by
      have hz : ∀ j, raw41521 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41521step0 = (fun i j => raw41521 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41521step0 raw41521; decide +kernel
      have hl : raw41521step0Labels = raw41521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41521 raw41521Labels permutation434 hz
    mixedMoment B raw41521step0 raw41521step0Labels = mixedMoment B raw41521step1 raw41521step1Labels := by
      have hz : ∀ j, raw41521step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41521step1 = (fun i j => raw41521step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41521step1 raw41521step0; decide +kernel
      have hl : raw41521step1Labels = raw41521step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41521step0 raw41521step0Labels permutation80 hz
    mixedMoment B raw41521step1 raw41521step1Labels = mixedMoment B raw41521step2 raw41521step2Labels := by
      have hz : ∀ j, raw41521step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41521step2 = (fun i j => raw41521step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41521step2 raw41521step1; decide +kernel
      have hl : raw41521step2Labels = raw41521step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41521step1 raw41521step1Labels permutation14 hz
    mixedMoment B raw41521step2 raw41521step2Labels = mixedMoment B raw41521step3 raw41521step3Labels := by
      have ha : raw41521step3 = (fun i j => raw41521step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41521step3 raw41521step2; decide +kernel
      have hl : raw41521step3Labels = raw41521step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41521step2 raw41521step2Labels permutation2 permutation3
    mixedMoment B raw41521step3 raw41521step3Labels = mixedMoment B raw41521step4 raw41521step4Labels := by
      have ha : raw41521step4 = raw41521step3 := by apply Matrix.ext; unfold raw41521step4 raw41521step3; decide +kernel
      have hl : raw41521step3Labels = labelEmbedding7 ∘ raw41521step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41521step3 raw41521step3Labels raw41521step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4901 node4901Labels := by rfl

def raw41522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41522Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41522step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41522step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41522step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41522step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41522step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw41522step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41522step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw41522step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41522 raw41522Labels = mixedMoment B node2778 node2778Labels := by
  calc
    mixedMoment B raw41522 raw41522Labels = mixedMoment B raw41522step0 raw41522step0Labels := by
      have hz : ∀ j, raw41522 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41522step0 = (fun i j => raw41522 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41522step0 raw41522; decide +kernel
      have hl : raw41522step0Labels = raw41522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41522 raw41522Labels permutation434 hz
    mixedMoment B raw41522step0 raw41522step0Labels = mixedMoment B raw41522step1 raw41522step1Labels := by
      have hz : ∀ j, raw41522step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41522step1 = (fun i j => raw41522step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41522step1 raw41522step0; decide +kernel
      have hl : raw41522step1Labels = raw41522step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41522step0 raw41522step0Labels permutation80 hz
    mixedMoment B raw41522step1 raw41522step1Labels = mixedMoment B raw41522step2 raw41522step2Labels := by
      have hz : ∀ j, raw41522step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41522step2 = (fun i j => raw41522step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41522step2 raw41522step1; decide +kernel
      have hl : raw41522step2Labels = raw41522step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41522step1 raw41522step1Labels permutation14 hz
    mixedMoment B raw41522step2 raw41522step2Labels = mixedMoment B raw41522step3 raw41522step3Labels := by
      have ha : raw41522step3 = (fun i j => raw41522step2 (permutation5 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41522step3 raw41522step2; decide +kernel
      have hl : raw41522step3Labels = raw41522step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41522step2 raw41522step2Labels permutation5 permutation4
    mixedMoment B raw41522step3 raw41522step3Labels = mixedMoment B raw41522step4 raw41522step4Labels := by
      have ha : raw41522step4 = raw41522step3 := by apply Matrix.ext; unfold raw41522step4 raw41522step3; decide +kernel
      have hl : raw41522step3Labels = labelEmbedding1 ∘ raw41522step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41522step3 raw41522step3Labels raw41522step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2778 node2778Labels := by rfl

def raw41523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41523Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41523step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41523step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41523step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41523step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41523step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw41523step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41523step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw41523step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41523step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw41523step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41523 raw41523Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw41523 raw41523Labels = mixedMoment B raw41523step0 raw41523step0Labels := by
      have hz : ∀ j, raw41523 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41523step0 = (fun i j => raw41523 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41523step0 raw41523; decide +kernel
      have hl : raw41523step0Labels = raw41523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41523 raw41523Labels permutation434 hz
    mixedMoment B raw41523step0 raw41523step0Labels = mixedMoment B raw41523step1 raw41523step1Labels := by
      have hz : ∀ j, raw41523step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41523step1 = (fun i j => raw41523step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41523step1 raw41523step0; decide +kernel
      have hl : raw41523step1Labels = raw41523step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41523step0 raw41523step0Labels permutation80 hz
    mixedMoment B raw41523step1 raw41523step1Labels = mixedMoment B raw41523step2 raw41523step2Labels := by
      have hz : ∀ j, raw41523step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41523step2 = (fun i j => raw41523step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41523step2 raw41523step1; decide +kernel
      have hl : raw41523step2Labels = raw41523step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41523step1 raw41523step1Labels permutation14 hz
    mixedMoment B raw41523step2 raw41523step2Labels = mixedMoment B raw41523step3 raw41523step3Labels := by
      have ha : raw41523step3 = (fun i j => raw41523step2 (permutation3 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41523step3 raw41523step2; decide +kernel
      have hl : raw41523step3Labels = raw41523step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41523step2 raw41523step2Labels permutation3 permutation5
    mixedMoment B raw41523step3 raw41523step3Labels = mixedMoment B raw41523step4 raw41523step4Labels := by
      have ha : raw41523step4 = -raw41523step3 := by apply Matrix.ext; change ∀ i j, raw41523step4 i j = -(raw41523step3 i j); unfold raw41523step4 raw41523step3; decide +kernel
      have hl : raw41523step4Labels = raw41523step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41523step4 raw41523step4Labels = mixedMoment B raw41523step5 raw41523step5Labels := by
      have ha : raw41523step5 = raw41523step4 := by apply Matrix.ext; unfold raw41523step5 raw41523step4; decide +kernel
      have hl : raw41523step4Labels = labelEmbedding9 ∘ raw41523step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41523step4 raw41523step4Labels raw41523step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

def raw41524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41524Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41524step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41524step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41524step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41524step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41524step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41524 raw41524Labels = mixedMoment B node3230 node3230Labels := by
  calc
    mixedMoment B raw41524 raw41524Labels = mixedMoment B raw41524step0 raw41524step0Labels := by
      have hz : ∀ j, raw41524 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41524step0 = (fun i j => raw41524 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41524step0 raw41524; decide +kernel
      have hl : raw41524step0Labels = raw41524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41524 raw41524Labels permutation346 hz
    mixedMoment B raw41524step0 raw41524step0Labels = mixedMoment B raw41524step1 raw41524step1Labels := by
      have hz : ∀ j, raw41524step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41524step1 = (fun i j => raw41524step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41524step1 raw41524step0; decide +kernel
      have hl : raw41524step1Labels = raw41524step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41524step0 raw41524step0Labels permutation56 hz
    mixedMoment B raw41524step1 raw41524step1Labels = mixedMoment B raw41524step2 raw41524step2Labels := by
      have ha : raw41524step2 = raw41524step1 := by apply Matrix.ext; unfold raw41524step2 raw41524step1; decide +kernel
      have hl : raw41524step1Labels = labelEmbedding1 ∘ raw41524step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41524step1 raw41524step1Labels raw41524step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3230 node3230Labels := by rfl

def raw41525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41525Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41525step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41525step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41525step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41525step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41525step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41525 raw41525Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw41525 raw41525Labels = mixedMoment B raw41525step0 raw41525step0Labels := by
      have hz : ∀ j, raw41525 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41525step0 = (fun i j => raw41525 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41525step0 raw41525; decide +kernel
      have hl : raw41525step0Labels = raw41525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41525 raw41525Labels permutation346 hz
    mixedMoment B raw41525step0 raw41525step0Labels = mixedMoment B raw41525step1 raw41525step1Labels := by
      have hz : ∀ j, raw41525step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41525step1 = (fun i j => raw41525step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41525step1 raw41525step0; decide +kernel
      have hl : raw41525step1Labels = raw41525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41525step0 raw41525step0Labels permutation56 hz
    mixedMoment B raw41525step1 raw41525step1Labels = mixedMoment B raw41525step2 raw41525step2Labels := by
      have ha : raw41525step2 = (fun i j => raw41525step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41525step2 raw41525step1; decide +kernel
      have hl : raw41525step2Labels = raw41525step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41525step1 raw41525step1Labels permutation8 permutation3
    mixedMoment B raw41525step2 raw41525step2Labels = mixedMoment B raw41525step3 raw41525step3Labels := by
      have ha : raw41525step3 = raw41525step2 := by apply Matrix.ext; unfold raw41525step3 raw41525step2; decide +kernel
      have hl : raw41525step2Labels = labelEmbedding7 ∘ raw41525step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41525step2 raw41525step2Labels raw41525step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4894 node4894Labels := by rfl

def raw41526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41526Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41526step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41526step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41526step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41526step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41526 raw41526Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw41526 raw41526Labels = mixedMoment B raw41526step0 raw41526step0Labels := by
      have hz : ∀ j, raw41526 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41526step0 = (fun i j => raw41526 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41526step0 raw41526; decide +kernel
      have hl : raw41526step0Labels = raw41526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41526 raw41526Labels permutation346 hz
    mixedMoment B raw41526step0 raw41526step0Labels = mixedMoment B raw41526step1 raw41526step1Labels := by
      have hz : ∀ j, raw41526step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41526step1 = (fun i j => raw41526step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41526step1 raw41526step0; decide +kernel
      have hl : raw41526step1Labels = raw41526step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41526step0 raw41526step0Labels permutation56 hz
    mixedMoment B raw41526step1 raw41526step1Labels = mixedMoment B raw41526step2 raw41526step2Labels := by
      have ha : raw41526step2 = raw41526step1 := by apply Matrix.ext; unfold raw41526step2 raw41526step1; decide +kernel
      have hl : raw41526step1Labels = labelEmbedding1 ∘ raw41526step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41526step1 raw41526step1Labels raw41526step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3229 node3229Labels := by rfl

def raw41527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41527Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41527step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41527step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41527step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41527step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41527step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41527step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41527 raw41527Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw41527 raw41527Labels = mixedMoment B raw41527step0 raw41527step0Labels := by
      have hz : ∀ j, raw41527 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41527step0 = (fun i j => raw41527 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41527step0 raw41527; decide +kernel
      have hl : raw41527step0Labels = raw41527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41527 raw41527Labels permutation346 hz
    mixedMoment B raw41527step0 raw41527step0Labels = mixedMoment B raw41527step1 raw41527step1Labels := by
      have hz : ∀ j, raw41527step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41527step1 = (fun i j => raw41527step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41527step1 raw41527step0; decide +kernel
      have hl : raw41527step1Labels = raw41527step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41527step0 raw41527step0Labels permutation56 hz
    mixedMoment B raw41527step1 raw41527step1Labels = mixedMoment B raw41527step2 raw41527step2Labels := by
      have ha : raw41527step2 = (fun i j => raw41527step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41527step2 raw41527step1; decide +kernel
      have hl : raw41527step2Labels = raw41527step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41527step1 raw41527step1Labels permutation8 permutation3
    mixedMoment B raw41527step2 raw41527step2Labels = mixedMoment B raw41527step3 raw41527step3Labels := by
      have ha : raw41527step3 = raw41527step2 := by apply Matrix.ext; unfold raw41527step3 raw41527step2; decide +kernel
      have hl : raw41527step2Labels = labelEmbedding7 ∘ raw41527step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41527step2 raw41527step2Labels raw41527step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw41528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41528Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41528step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41528step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41528step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41528step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw41528step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41528step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw41528step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41528step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw41528step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41528 raw41528Labels = mixedMoment B node3225 node3225Labels := by
  calc
    mixedMoment B raw41528 raw41528Labels = mixedMoment B raw41528step0 raw41528step0Labels := by
      have hz : ∀ j, raw41528 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41528step0 = (fun i j => raw41528 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41528step0 raw41528; decide +kernel
      have hl : raw41528step0Labels = raw41528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41528 raw41528Labels permutation346 hz
    mixedMoment B raw41528step0 raw41528step0Labels = mixedMoment B raw41528step1 raw41528step1Labels := by
      have hz : ∀ j, raw41528step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41528step1 = (fun i j => raw41528step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41528step1 raw41528step0; decide +kernel
      have hl : raw41528step1Labels = raw41528step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41528step0 raw41528step0Labels permutation56 hz
    mixedMoment B raw41528step1 raw41528step1Labels = mixedMoment B raw41528step2 raw41528step2Labels := by
      have ha : raw41528step2 = (fun i j => raw41528step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41528step2 raw41528step1; decide +kernel
      have hl : raw41528step2Labels = raw41528step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41528step1 raw41528step1Labels permutation12 permutation4
    mixedMoment B raw41528step2 raw41528step2Labels = mixedMoment B raw41528step3 raw41528step3Labels := by
      have ha : raw41528step3 = -raw41528step2 := by apply Matrix.ext; change ∀ i j, raw41528step3 i j = -(raw41528step2 i j); unfold raw41528step3 raw41528step2; decide +kernel
      have hl : raw41528step3Labels = raw41528step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41528step3 raw41528step3Labels = mixedMoment B raw41528step4 raw41528step4Labels := by
      have ha : raw41528step4 = raw41528step3 := by apply Matrix.ext; unfold raw41528step4 raw41528step3; decide +kernel
      have hl : raw41528step3Labels = labelEmbedding1 ∘ raw41528step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41528step3 raw41528step3Labels raw41528step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3225 node3225Labels := by rfl

def raw41529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41529Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41529step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41529step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41529step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41529step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41529step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41529step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41529 raw41529Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw41529 raw41529Labels = mixedMoment B raw41529step0 raw41529step0Labels := by
      have hz : ∀ j, raw41529 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41529step0 = (fun i j => raw41529 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41529step0 raw41529; decide +kernel
      have hl : raw41529step0Labels = raw41529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41529 raw41529Labels permutation346 hz
    mixedMoment B raw41529step0 raw41529step0Labels = mixedMoment B raw41529step1 raw41529step1Labels := by
      have hz : ∀ j, raw41529step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41529step1 = (fun i j => raw41529step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41529step1 raw41529step0; decide +kernel
      have hl : raw41529step1Labels = raw41529step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41529step0 raw41529step0Labels permutation56 hz
    mixedMoment B raw41529step1 raw41529step1Labels = mixedMoment B raw41529step2 raw41529step2Labels := by
      have ha : raw41529step2 = (fun i j => raw41529step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41529step2 raw41529step1; decide +kernel
      have hl : raw41529step2Labels = raw41529step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41529step1 raw41529step1Labels permutation8 permutation3
    mixedMoment B raw41529step2 raw41529step2Labels = mixedMoment B raw41529step3 raw41529step3Labels := by
      have ha : raw41529step3 = raw41529step2 := by apply Matrix.ext; unfold raw41529step3 raw41529step2; decide +kernel
      have hl : raw41529step2Labels = labelEmbedding7 ∘ raw41529step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41529step2 raw41529step2Labels raw41529step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw41530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41530Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41530step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41530step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41530step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41530step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41530 raw41530Labels = mixedMoment B node3224 node3224Labels := by
  calc
    mixedMoment B raw41530 raw41530Labels = mixedMoment B raw41530step0 raw41530step0Labels := by
      have hz : ∀ j, raw41530 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41530step0 = (fun i j => raw41530 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41530step0 raw41530; decide +kernel
      have hl : raw41530step0Labels = raw41530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41530 raw41530Labels permutation346 hz
    mixedMoment B raw41530step0 raw41530step0Labels = mixedMoment B raw41530step1 raw41530step1Labels := by
      have hz : ∀ j, raw41530step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41530step1 = (fun i j => raw41530step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41530step1 raw41530step0; decide +kernel
      have hl : raw41530step1Labels = raw41530step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41530step0 raw41530step0Labels permutation56 hz
    mixedMoment B raw41530step1 raw41530step1Labels = mixedMoment B raw41530step2 raw41530step2Labels := by
      have ha : raw41530step2 = raw41530step1 := by apply Matrix.ext; unfold raw41530step2 raw41530step1; decide +kernel
      have hl : raw41530step1Labels = labelEmbedding1 ∘ raw41530step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41530step1 raw41530step1Labels raw41530step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3224 node3224Labels := by rfl

def raw41531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41531Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41531step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41531step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41531step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41531step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41531step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41531step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41531 raw41531Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw41531 raw41531Labels = mixedMoment B raw41531step0 raw41531step0Labels := by
      have hz : ∀ j, raw41531 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41531step0 = (fun i j => raw41531 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41531step0 raw41531; decide +kernel
      have hl : raw41531step0Labels = raw41531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41531 raw41531Labels permutation346 hz
    mixedMoment B raw41531step0 raw41531step0Labels = mixedMoment B raw41531step1 raw41531step1Labels := by
      have hz : ∀ j, raw41531step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41531step1 = (fun i j => raw41531step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41531step1 raw41531step0; decide +kernel
      have hl : raw41531step1Labels = raw41531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41531step0 raw41531step0Labels permutation56 hz
    mixedMoment B raw41531step1 raw41531step1Labels = mixedMoment B raw41531step2 raw41531step2Labels := by
      have ha : raw41531step2 = (fun i j => raw41531step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41531step2 raw41531step1; decide +kernel
      have hl : raw41531step2Labels = raw41531step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41531step1 raw41531step1Labels permutation8 permutation3
    mixedMoment B raw41531step2 raw41531step2Labels = mixedMoment B raw41531step3 raw41531step3Labels := by
      have ha : raw41531step3 = raw41531step2 := by apply Matrix.ext; unfold raw41531step3 raw41531step2; decide +kernel
      have hl : raw41531step2Labels = labelEmbedding7 ∘ raw41531step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41531step2 raw41531step2Labels raw41531step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

def raw41532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41532Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41532step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41532step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41532step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41532step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw41532step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41532step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw41532step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41532 raw41532Labels = mixedMoment B node2755 node2755Labels := by
  calc
    mixedMoment B raw41532 raw41532Labels = mixedMoment B raw41532step0 raw41532step0Labels := by
      have hz : ∀ j, raw41532 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41532step0 = (fun i j => raw41532 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41532step0 raw41532; decide +kernel
      have hl : raw41532step0Labels = raw41532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41532 raw41532Labels permutation346 hz
    mixedMoment B raw41532step0 raw41532step0Labels = mixedMoment B raw41532step1 raw41532step1Labels := by
      have hz : ∀ j, raw41532step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41532step1 = (fun i j => raw41532step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41532step1 raw41532step0; decide +kernel
      have hl : raw41532step1Labels = raw41532step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41532step0 raw41532step0Labels permutation56 hz
    mixedMoment B raw41532step1 raw41532step1Labels = mixedMoment B raw41532step2 raw41532step2Labels := by
      have ha : raw41532step2 = (fun i j => raw41532step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41532step2 raw41532step1; decide +kernel
      have hl : raw41532step2Labels = raw41532step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41532step1 raw41532step1Labels permutation29 permutation4
    mixedMoment B raw41532step2 raw41532step2Labels = mixedMoment B raw41532step3 raw41532step3Labels := by
      have ha : raw41532step3 = raw41532step2 := by apply Matrix.ext; unfold raw41532step3 raw41532step2; decide +kernel
      have hl : raw41532step2Labels = labelEmbedding1 ∘ raw41532step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41532step2 raw41532step2Labels raw41532step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2755 node2755Labels := by rfl

def raw41533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41533Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41533step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41533step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41533step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41533step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw41533step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41533step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw41533step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41533step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw41533step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41533 raw41533Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw41533 raw41533Labels = mixedMoment B raw41533step0 raw41533step0Labels := by
      have hz : ∀ j, raw41533 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41533step0 = (fun i j => raw41533 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41533step0 raw41533; decide +kernel
      have hl : raw41533step0Labels = raw41533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41533 raw41533Labels permutation346 hz
    mixedMoment B raw41533step0 raw41533step0Labels = mixedMoment B raw41533step1 raw41533step1Labels := by
      have hz : ∀ j, raw41533step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41533step1 = (fun i j => raw41533step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41533step1 raw41533step0; decide +kernel
      have hl : raw41533step1Labels = raw41533step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41533step0 raw41533step0Labels permutation56 hz
    mixedMoment B raw41533step1 raw41533step1Labels = mixedMoment B raw41533step2 raw41533step2Labels := by
      have ha : raw41533step2 = (fun i j => raw41533step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41533step2 raw41533step1; decide +kernel
      have hl : raw41533step2Labels = raw41533step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41533step1 raw41533step1Labels permutation8 permutation5
    mixedMoment B raw41533step2 raw41533step2Labels = mixedMoment B raw41533step3 raw41533step3Labels := by
      have ha : raw41533step3 = -raw41533step2 := by apply Matrix.ext; change ∀ i j, raw41533step3 i j = -(raw41533step2 i j); unfold raw41533step3 raw41533step2; decide +kernel
      have hl : raw41533step3Labels = raw41533step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41533step3 raw41533step3Labels = mixedMoment B raw41533step4 raw41533step4Labels := by
      have ha : raw41533step4 = raw41533step3 := by apply Matrix.ext; unfold raw41533step4 raw41533step3; decide +kernel
      have hl : raw41533step3Labels = labelEmbedding9 ∘ raw41533step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41533step3 raw41533step3Labels raw41533step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw41534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41534Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41534step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41534step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41534step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1]]
def raw41534step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41534step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41534step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41534step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41534step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41534 raw41534Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw41534 raw41534Labels = mixedMoment B raw41534step0 raw41534step0Labels := by
      have hz : ∀ j, raw41534 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41534step0 = (fun i j => raw41534 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41534step0 raw41534; decide +kernel
      have hl : raw41534step0Labels = raw41534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41534 raw41534Labels permutation346 hz
    mixedMoment B raw41534step0 raw41534step0Labels = mixedMoment B raw41534step1 raw41534step1Labels := by
      have hz : ∀ j, raw41534step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41534step1 = (fun i j => raw41534step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41534step1 raw41534step0; decide +kernel
      have hl : raw41534step1Labels = raw41534step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41534step0 raw41534step0Labels permutation56 hz
    mixedMoment B raw41534step1 raw41534step1Labels = mixedMoment B raw41534step2 raw41534step2Labels := by
      have ha : raw41534step2 = (fun i j => raw41534step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41534step2 raw41534step1; decide +kernel
      have hl : raw41534step2Labels = raw41534step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41534step1 raw41534step1Labels permutation8 permutation4
    mixedMoment B raw41534step2 raw41534step2Labels = mixedMoment B raw41534step3 raw41534step3Labels := by
      have ha : raw41534step3 = -raw41534step2 := by apply Matrix.ext; change ∀ i j, raw41534step3 i j = -(raw41534step2 i j); unfold raw41534step3 raw41534step2; decide +kernel
      have hl : raw41534step3Labels = raw41534step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41534step3 raw41534step3Labels = mixedMoment B raw41534step4 raw41534step4Labels := by
      have ha : raw41534step4 = raw41534step3 := by apply Matrix.ext; unfold raw41534step4 raw41534step3; decide +kernel
      have hl : raw41534step3Labels = labelEmbedding1 ∘ raw41534step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41534step3 raw41534step3Labels raw41534step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3229 node3229Labels := by rfl

def raw41535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41535Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41535step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41535step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41535step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41535step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41535step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41535step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41535step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41535step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41535step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41535 raw41535Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw41535 raw41535Labels = mixedMoment B raw41535step0 raw41535step0Labels := by
      have hz : ∀ j, raw41535 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41535step0 = (fun i j => raw41535 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41535step0 raw41535; decide +kernel
      have hl : raw41535step0Labels = raw41535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41535 raw41535Labels permutation346 hz
    mixedMoment B raw41535step0 raw41535step0Labels = mixedMoment B raw41535step1 raw41535step1Labels := by
      have hz : ∀ j, raw41535step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41535step1 = (fun i j => raw41535step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41535step1 raw41535step0; decide +kernel
      have hl : raw41535step1Labels = raw41535step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41535step0 raw41535step0Labels permutation56 hz
    mixedMoment B raw41535step1 raw41535step1Labels = mixedMoment B raw41535step2 raw41535step2Labels := by
      have ha : raw41535step2 = (fun i j => raw41535step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41535step2 raw41535step1; decide +kernel
      have hl : raw41535step2Labels = raw41535step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41535step1 raw41535step1Labels permutation8 permutation5
    mixedMoment B raw41535step2 raw41535step2Labels = mixedMoment B raw41535step3 raw41535step3Labels := by
      have ha : raw41535step3 = -raw41535step2 := by apply Matrix.ext; change ∀ i j, raw41535step3 i j = -(raw41535step2 i j); unfold raw41535step3 raw41535step2; decide +kernel
      have hl : raw41535step3Labels = raw41535step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41535step3 raw41535step3Labels = mixedMoment B raw41535step4 raw41535step4Labels := by
      have ha : raw41535step4 = raw41535step3 := by apply Matrix.ext; unfold raw41535step4 raw41535step3; decide +kernel
      have hl : raw41535step3Labels = labelEmbedding9 ∘ raw41535step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41535step3 raw41535step3Labels raw41535step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw41536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41536Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41536step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41536step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41536step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41536step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw41536step2Labels : Fin 2 → Fin 2 := ![1, 1]

def raw41536step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw41536step3Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical41536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41536 raw41536Labels = mixedMoment B node0 node0Labels := by
  calc
    mixedMoment B raw41536 raw41536Labels = mixedMoment B raw41536step0 raw41536step0Labels := by
      have hz : ∀ j, raw41536 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41536step0 = (fun i j => raw41536 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41536step0 raw41536; decide +kernel
      have hl : raw41536step0Labels = raw41536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41536 raw41536Labels permutation346 hz
    mixedMoment B raw41536step0 raw41536step0Labels = mixedMoment B raw41536step1 raw41536step1Labels := by
      have hz : ∀ j, raw41536step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41536step1 = (fun i j => raw41536step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41536step1 raw41536step0; decide +kernel
      have hl : raw41536step1Labels = raw41536step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41536step0 raw41536step0Labels permutation56 hz
    mixedMoment B raw41536step1 raw41536step1Labels = mixedMoment B raw41536step2 raw41536step2Labels := by
      have hz : ∀ i, raw41536step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw41536step2 = (fun i j => raw41536step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw41536step2 raw41536step1; decide +kernel
      have hl : raw41536step2Labels = (fun j => raw41536step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw41536step1 raw41536step1Labels permutation6 hz
    mixedMoment B raw41536step2 raw41536step2Labels = mixedMoment B raw41536step3 raw41536step3Labels := by
      have ha : raw41536step3 = raw41536step2 := by apply Matrix.ext; unfold raw41536step3 raw41536step2; decide +kernel
      have hl : raw41536step2Labels = labelEmbedding0 ∘ raw41536step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41536step2 raw41536step2Labels raw41536step3Labels labelEmbedding0 hl
    _ = mixedMoment B node0 node0Labels := by rfl

def raw41537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41537Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41537step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41537step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41537step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41537step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw41537step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw41537step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw41537step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical41537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41537 raw41537Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw41537 raw41537Labels = mixedMoment B raw41537step0 raw41537step0Labels := by
      have hz : ∀ j, raw41537 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41537step0 = (fun i j => raw41537 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41537step0 raw41537; decide +kernel
      have hl : raw41537step0Labels = raw41537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41537 raw41537Labels permutation346 hz
    mixedMoment B raw41537step0 raw41537step0Labels = mixedMoment B raw41537step1 raw41537step1Labels := by
      have hz : ∀ j, raw41537step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41537step1 = (fun i j => raw41537step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41537step1 raw41537step0; decide +kernel
      have hl : raw41537step1Labels = raw41537step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41537step0 raw41537step0Labels permutation56 hz
    mixedMoment B raw41537step1 raw41537step1Labels = mixedMoment B raw41537step2 raw41537step2Labels := by
      have hz : ∀ i, raw41537step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw41537step2 = (fun i j => raw41537step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw41537step2 raw41537step1; decide +kernel
      have hl : raw41537step2Labels = (fun j => raw41537step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw41537step1 raw41537step1Labels permutation6 hz
    mixedMoment B raw41537step2 raw41537step2Labels = mixedMoment B raw41537step3 raw41537step3Labels := by
      have ha : raw41537step3 = raw41537step2 := by apply Matrix.ext; unfold raw41537step3 raw41537step2; decide +kernel
      have hl : raw41537step2Labels = labelEmbedding3 ∘ raw41537step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41537step2 raw41537step2Labels raw41537step3Labels labelEmbedding3 hl
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw41538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41538Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41538step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw41538step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41538step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41538step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41538step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41538step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41538 raw41538Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw41538 raw41538Labels = mixedMoment B raw41538step0 raw41538step0Labels := by
      have hz : ∀ j, raw41538 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41538step0 = (fun i j => raw41538 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41538step0 raw41538; decide +kernel
      have hl : raw41538step0Labels = raw41538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41538 raw41538Labels permutation265 hz
    mixedMoment B raw41538step0 raw41538step0Labels = mixedMoment B raw41538step1 raw41538step1Labels := by
      have ha : raw41538step1 = (fun i j => raw41538step0 (permutation54 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41538step1 raw41538step0; decide +kernel
      have hl : raw41538step1Labels = raw41538step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41538step0 raw41538step0Labels permutation54 permutation4
    mixedMoment B raw41538step1 raw41538step1Labels = mixedMoment B raw41538step2 raw41538step2Labels := by
      have ha : raw41538step2 = -raw41538step1 := by apply Matrix.ext; change ∀ i j, raw41538step2 i j = -(raw41538step1 i j); unfold raw41538step2 raw41538step1; decide +kernel
      have hl : raw41538step2Labels = raw41538step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41538step2 raw41538step2Labels = mixedMoment B raw41538step3 raw41538step3Labels := by
      have ha : raw41538step3 = raw41538step2 := by apply Matrix.ext; unfold raw41538step3 raw41538step2; decide +kernel
      have hl : raw41538step2Labels = labelEmbedding1 ∘ raw41538step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41538step2 raw41538step2Labels raw41538step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3223 node3223Labels := by rfl

def raw41539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41539Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41539step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41539step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41539step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41539step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41539 raw41539Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw41539 raw41539Labels = mixedMoment B raw41539step0 raw41539step0Labels := by
      have hz : ∀ j, raw41539 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41539step0 = (fun i j => raw41539 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41539step0 raw41539; decide +kernel
      have hl : raw41539step0Labels = raw41539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41539 raw41539Labels permutation265 hz
    mixedMoment B raw41539step0 raw41539step0Labels = mixedMoment B raw41539step1 raw41539step1Labels := by
      have ha : raw41539step1 = (fun i j => raw41539step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41539step1 raw41539step0; decide +kernel
      have hl : raw41539step1Labels = raw41539step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41539step0 raw41539step0Labels permutation32 permutation3
    mixedMoment B raw41539step1 raw41539step1Labels = mixedMoment B raw41539step2 raw41539step2Labels := by
      have ha : raw41539step2 = raw41539step1 := by apply Matrix.ext; unfold raw41539step2 raw41539step1; decide +kernel
      have hl : raw41539step1Labels = labelEmbedding7 ∘ raw41539step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41539step1 raw41539step1Labels raw41539step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw41540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41540Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41540step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41540step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41540step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw41540step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41540step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw41540step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41540 raw41540Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw41540 raw41540Labels = mixedMoment B raw41540step0 raw41540step0Labels := by
      have hz : ∀ j, raw41540 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41540step0 = (fun i j => raw41540 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41540step0 raw41540; decide +kernel
      have hl : raw41540step0Labels = raw41540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41540 raw41540Labels permutation265 hz
    mixedMoment B raw41540step0 raw41540step0Labels = mixedMoment B raw41540step1 raw41540step1Labels := by
      have ha : raw41540step1 = (fun i j => raw41540step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41540step1 raw41540step0; decide +kernel
      have hl : raw41540step1Labels = raw41540step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41540step0 raw41540step0Labels permutation40 permutation4
    mixedMoment B raw41540step1 raw41540step1Labels = mixedMoment B raw41540step2 raw41540step2Labels := by
      have ha : raw41540step2 = -raw41540step1 := by apply Matrix.ext; change ∀ i j, raw41540step2 i j = -(raw41540step1 i j); unfold raw41540step2 raw41540step1; decide +kernel
      have hl : raw41540step2Labels = raw41540step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41540step2 raw41540step2Labels = mixedMoment B raw41540step3 raw41540step3Labels := by
      have ha : raw41540step3 = raw41540step2 := by apply Matrix.ext; unfold raw41540step3 raw41540step2; decide +kernel
      have hl : raw41540step2Labels = labelEmbedding1 ∘ raw41540step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41540step2 raw41540step2Labels raw41540step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3227 node3227Labels := by rfl

def raw41541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41541Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41541step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw41541step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41541step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41541step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41541step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41541step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41541 raw41541Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw41541 raw41541Labels = mixedMoment B raw41541step0 raw41541step0Labels := by
      have hz : ∀ j, raw41541 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41541step0 = (fun i j => raw41541 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41541step0 raw41541; decide +kernel
      have hl : raw41541step0Labels = raw41541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41541 raw41541Labels permutation265 hz
    mixedMoment B raw41541step0 raw41541step0Labels = mixedMoment B raw41541step1 raw41541step1Labels := by
      have ha : raw41541step1 = (fun i j => raw41541step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41541step1 raw41541step0; decide +kernel
      have hl : raw41541step1Labels = raw41541step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41541step0 raw41541step0Labels permutation40 permutation5
    mixedMoment B raw41541step1 raw41541step1Labels = mixedMoment B raw41541step2 raw41541step2Labels := by
      have ha : raw41541step2 = -raw41541step1 := by apply Matrix.ext; change ∀ i j, raw41541step2 i j = -(raw41541step1 i j); unfold raw41541step2 raw41541step1; decide +kernel
      have hl : raw41541step2Labels = raw41541step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41541step2 raw41541step2Labels = mixedMoment B raw41541step3 raw41541step3Labels := by
      have ha : raw41541step3 = raw41541step2 := by apply Matrix.ext; unfold raw41541step3 raw41541step2; decide +kernel
      have hl : raw41541step2Labels = labelEmbedding9 ∘ raw41541step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41541step2 raw41541step2Labels raw41541step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw41542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41542Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41542step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41542step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41542step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41542step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41542 raw41542Labels = mixedMoment B node3228 node3228Labels := by
  calc
    mixedMoment B raw41542 raw41542Labels = mixedMoment B raw41542step0 raw41542step0Labels := by
      have hz : ∀ j, raw41542 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41542step0 = (fun i j => raw41542 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41542step0 raw41542; decide +kernel
      have hl : raw41542step0Labels = raw41542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41542 raw41542Labels permutation265 hz
    mixedMoment B raw41542step0 raw41542step0Labels = mixedMoment B raw41542step1 raw41542step1Labels := by
      have ha : raw41542step1 = (fun i j => raw41542step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41542step1 raw41542step0; decide +kernel
      have hl : raw41542step1Labels = raw41542step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41542step0 raw41542step0Labels permutation35 permutation2
    mixedMoment B raw41542step1 raw41542step1Labels = mixedMoment B raw41542step2 raw41542step2Labels := by
      have ha : raw41542step2 = raw41542step1 := by apply Matrix.ext; unfold raw41542step2 raw41542step1; decide +kernel
      have hl : raw41542step1Labels = labelEmbedding1 ∘ raw41542step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41542step1 raw41542step1Labels raw41542step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3228 node3228Labels := by rfl

def raw41543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41543Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41543step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41543step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41543step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41543 raw41543Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw41543 raw41543Labels = mixedMoment B raw41543step0 raw41543step0Labels := by
      have hz : ∀ j, raw41543 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41543step0 = (fun i j => raw41543 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41543step0 raw41543; decide +kernel
      have hl : raw41543step0Labels = raw41543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41543 raw41543Labels permutation265 hz
    mixedMoment B raw41543step0 raw41543step0Labels = mixedMoment B raw41543step1 raw41543step1Labels := by
      have ha : raw41543step1 = (fun i j => raw41543step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41543step1 raw41543step0; decide +kernel
      have hl : raw41543step1Labels = raw41543step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41543step0 raw41543step0Labels permutation32 permutation3
    mixedMoment B raw41543step1 raw41543step1Labels = mixedMoment B raw41543step2 raw41543step2Labels := by
      have ha : raw41543step2 = raw41543step1 := by apply Matrix.ext; unfold raw41543step2 raw41543step1; decide +kernel
      have hl : raw41543step1Labels = labelEmbedding7 ∘ raw41543step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41543step1 raw41543step1Labels raw41543step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4893 node4893Labels := by rfl

def raw41544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41544Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41544step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41544step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41544step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41544step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41544 raw41544Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw41544 raw41544Labels = mixedMoment B raw41544step0 raw41544step0Labels := by
      have hz : ∀ j, raw41544 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41544step0 = (fun i j => raw41544 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41544step0 raw41544; decide +kernel
      have hl : raw41544step0Labels = raw41544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41544 raw41544Labels permutation265 hz
    mixedMoment B raw41544step0 raw41544step0Labels = mixedMoment B raw41544step1 raw41544step1Labels := by
      have ha : raw41544step1 = (fun i j => raw41544step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41544step1 raw41544step0; decide +kernel
      have hl : raw41544step1Labels = raw41544step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41544step0 raw41544step0Labels permutation36 permutation2
    mixedMoment B raw41544step1 raw41544step1Labels = mixedMoment B raw41544step2 raw41544step2Labels := by
      have ha : raw41544step2 = raw41544step1 := by apply Matrix.ext; unfold raw41544step2 raw41544step1; decide +kernel
      have hl : raw41544step1Labels = labelEmbedding1 ∘ raw41544step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41544step1 raw41544step1Labels raw41544step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3223 node3223Labels := by rfl

def raw41545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41545Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41545step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41545step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw41545step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41545step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41545step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41545step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41545step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41545 raw41545Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw41545 raw41545Labels = mixedMoment B raw41545step0 raw41545step0Labels := by
      have hz : ∀ j, raw41545 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41545step0 = (fun i j => raw41545 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41545step0 raw41545; decide +kernel
      have hl : raw41545step0Labels = raw41545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41545 raw41545Labels permutation265 hz
    mixedMoment B raw41545step0 raw41545step0Labels = mixedMoment B raw41545step1 raw41545step1Labels := by
      have ha : raw41545step1 = (fun i j => raw41545step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41545step1 raw41545step0; decide +kernel
      have hl : raw41545step1Labels = raw41545step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41545step0 raw41545step0Labels permutation41 permutation5
    mixedMoment B raw41545step1 raw41545step1Labels = mixedMoment B raw41545step2 raw41545step2Labels := by
      have ha : raw41545step2 = -raw41545step1 := by apply Matrix.ext; change ∀ i j, raw41545step2 i j = -(raw41545step1 i j); unfold raw41545step2 raw41545step1; decide +kernel
      have hl : raw41545step2Labels = raw41545step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41545step2 raw41545step2Labels = mixedMoment B raw41545step3 raw41545step3Labels := by
      have ha : raw41545step3 = raw41545step2 := by apply Matrix.ext; unfold raw41545step3 raw41545step2; decide +kernel
      have hl : raw41545step2Labels = labelEmbedding9 ∘ raw41545step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41545step2 raw41545step2Labels raw41545step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw41546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41546Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41546step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41546step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41546step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41546 raw41546Labels = mixedMoment B node3226 node3226Labels := by
  calc
    mixedMoment B raw41546 raw41546Labels = mixedMoment B raw41546step0 raw41546step0Labels := by
      have ha : raw41546step0 = (fun i j => raw41546 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41546step0 raw41546; decide +kernel
      have hl : raw41546step0Labels = raw41546Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41546 raw41546Labels permutation156 permutation2
    mixedMoment B raw41546step0 raw41546step0Labels = mixedMoment B raw41546step1 raw41546step1Labels := by
      have ha : raw41546step1 = raw41546step0 := by apply Matrix.ext; unfold raw41546step1 raw41546step0; decide +kernel
      have hl : raw41546step0Labels = labelEmbedding1 ∘ raw41546step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41546step0 raw41546step0Labels raw41546step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3226 node3226Labels := by rfl

def raw41547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41547Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41547step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41547step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41547 raw41547Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw41547 raw41547Labels = mixedMoment B raw41547step0 raw41547step0Labels := by
      have ha : raw41547step0 = (fun i j => raw41547 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41547step0 raw41547; decide +kernel
      have hl : raw41547step0Labels = raw41547Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41547 raw41547Labels permutation152 permutation3
    mixedMoment B raw41547step0 raw41547step0Labels = mixedMoment B raw41547step1 raw41547step1Labels := by
      have ha : raw41547step1 = raw41547step0 := by apply Matrix.ext; unfold raw41547step1 raw41547step0; decide +kernel
      have hl : raw41547step0Labels = labelEmbedding7 ∘ raw41547step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41547step0 raw41547step0Labels raw41547step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4887 node4887Labels := by rfl

def raw41548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41548Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41548step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41548step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw41548step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41548step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw41548step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41548step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw41548step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41548 raw41548Labels = mixedMoment B node3114 node3114Labels := by
  calc
    mixedMoment B raw41548 raw41548Labels = mixedMoment B raw41548step0 raw41548step0Labels := by
      have hz : ∀ j, raw41548 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41548step0 = (fun i j => raw41548 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41548step0 raw41548; decide +kernel
      have hl : raw41548step0Labels = raw41548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41548 raw41548Labels permutation520 hz
    mixedMoment B raw41548step0 raw41548step0Labels = mixedMoment B raw41548step1 raw41548step1Labels := by
      have hz : ∀ j, raw41548step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41548step1 = (fun i j => raw41548step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41548step1 raw41548step0; decide +kernel
      have hl : raw41548step1Labels = raw41548step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41548step0 raw41548step0Labels permutation104 hz
    mixedMoment B raw41548step1 raw41548step1Labels = mixedMoment B raw41548step2 raw41548step2Labels := by
      have hz : ∀ j, raw41548step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41548step2 = (fun i j => raw41548step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41548step2 raw41548step1; decide +kernel
      have hl : raw41548step2Labels = raw41548step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41548step1 raw41548step1Labels permutation20 hz
    mixedMoment B raw41548step2 raw41548step2Labels = mixedMoment B raw41548step3 raw41548step3Labels := by
      have ha : raw41548step3 = raw41548step2 := by apply Matrix.ext; unfold raw41548step3 raw41548step2; decide +kernel
      have hl : raw41548step2Labels = labelEmbedding1 ∘ raw41548step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41548step2 raw41548step2Labels raw41548step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3114 node3114Labels := by rfl

def raw41549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41549Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw41549step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw41549step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41549step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw41549step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41549step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw41549step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41549step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw41549step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41549step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw41549step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41549 raw41549Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw41549 raw41549Labels = mixedMoment B raw41549step0 raw41549step0Labels := by
      have hz : ∀ j, raw41549 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw41549step0 = (fun i j => raw41549 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw41549step0 raw41549; decide +kernel
      have hl : raw41549step0Labels = raw41549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41549 raw41549Labels permutation520 hz
    mixedMoment B raw41549step0 raw41549step0Labels = mixedMoment B raw41549step1 raw41549step1Labels := by
      have hz : ∀ j, raw41549step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw41549step1 = (fun i j => raw41549step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw41549step1 raw41549step0; decide +kernel
      have hl : raw41549step1Labels = raw41549step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41549step0 raw41549step0Labels permutation104 hz
    mixedMoment B raw41549step1 raw41549step1Labels = mixedMoment B raw41549step2 raw41549step2Labels := by
      have hz : ∀ j, raw41549step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw41549step2 = (fun i j => raw41549step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw41549step2 raw41549step1; decide +kernel
      have hl : raw41549step2Labels = raw41549step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41549step1 raw41549step1Labels permutation20 hz
    mixedMoment B raw41549step2 raw41549step2Labels = mixedMoment B raw41549step3 raw41549step3Labels := by
      have ha : raw41549step3 = (fun i j => raw41549step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41549step3 raw41549step2; decide +kernel
      have hl : raw41549step3Labels = raw41549step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41549step2 raw41549step2Labels permutation7 permutation3
    mixedMoment B raw41549step3 raw41549step3Labels = mixedMoment B raw41549step4 raw41549step4Labels := by
      have ha : raw41549step4 = -raw41549step3 := by apply Matrix.ext; change ∀ i j, raw41549step4 i j = -(raw41549step3 i j); unfold raw41549step4 raw41549step3; decide +kernel
      have hl : raw41549step4Labels = raw41549step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41549step4 raw41549step4Labels = mixedMoment B raw41549step5 raw41549step5Labels := by
      have ha : raw41549step5 = raw41549step4 := by apply Matrix.ext; unfold raw41549step5 raw41549step4; decide +kernel
      have hl : raw41549step4Labels = labelEmbedding7 ∘ raw41549step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41549step4 raw41549step4Labels raw41549step5Labels labelEmbedding7 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

def raw41550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41550Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41550step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41550step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41550step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41550step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41550 raw41550Labels = mixedMoment B node3113 node3113Labels := by
  calc
    mixedMoment B raw41550 raw41550Labels = mixedMoment B raw41550step0 raw41550step0Labels := by
      have hz : ∀ j, raw41550 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41550step0 = (fun i j => raw41550 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41550step0 raw41550; decide +kernel
      have hl : raw41550step0Labels = raw41550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41550 raw41550Labels permutation434 hz
    mixedMoment B raw41550step0 raw41550step0Labels = mixedMoment B raw41550step1 raw41550step1Labels := by
      have hz : ∀ j, raw41550step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41550step1 = (fun i j => raw41550step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41550step1 raw41550step0; decide +kernel
      have hl : raw41550step1Labels = raw41550step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41550step0 raw41550step0Labels permutation80 hz
    mixedMoment B raw41550step1 raw41550step1Labels = mixedMoment B raw41550step2 raw41550step2Labels := by
      have ha : raw41550step2 = raw41550step1 := by apply Matrix.ext; unfold raw41550step2 raw41550step1; decide +kernel
      have hl : raw41550step1Labels = labelEmbedding1 ∘ raw41550step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41550step1 raw41550step1Labels raw41550step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3113 node3113Labels := by rfl

def raw41551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41551Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw41551step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41551step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41551step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41551step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41551step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41551step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41551 raw41551Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw41551 raw41551Labels = mixedMoment B raw41551step0 raw41551step0Labels := by
      have hz : ∀ j, raw41551 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41551step0 = (fun i j => raw41551 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41551step0 raw41551; decide +kernel
      have hl : raw41551step0Labels = raw41551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41551 raw41551Labels permutation434 hz
    mixedMoment B raw41551step0 raw41551step0Labels = mixedMoment B raw41551step1 raw41551step1Labels := by
      have hz : ∀ j, raw41551step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41551step1 = (fun i j => raw41551step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41551step1 raw41551step0; decide +kernel
      have hl : raw41551step1Labels = raw41551step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41551step0 raw41551step0Labels permutation80 hz
    mixedMoment B raw41551step1 raw41551step1Labels = mixedMoment B raw41551step2 raw41551step2Labels := by
      have ha : raw41551step2 = (fun i j => raw41551step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41551step2 raw41551step1; decide +kernel
      have hl : raw41551step2Labels = raw41551step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41551step1 raw41551step1Labels permutation8 permutation3
    mixedMoment B raw41551step2 raw41551step2Labels = mixedMoment B raw41551step3 raw41551step3Labels := by
      have ha : raw41551step3 = raw41551step2 := by apply Matrix.ext; unfold raw41551step3 raw41551step2; decide +kernel
      have hl : raw41551step2Labels = labelEmbedding7 ∘ raw41551step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41551step2 raw41551step2Labels raw41551step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5272 node5272Labels := by rfl

def raw41552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41552Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41552step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41552step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41552step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41552step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41552 raw41552Labels = mixedMoment B node3112 node3112Labels := by
  calc
    mixedMoment B raw41552 raw41552Labels = mixedMoment B raw41552step0 raw41552step0Labels := by
      have hz : ∀ j, raw41552 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41552step0 = (fun i j => raw41552 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41552step0 raw41552; decide +kernel
      have hl : raw41552step0Labels = raw41552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41552 raw41552Labels permutation434 hz
    mixedMoment B raw41552step0 raw41552step0Labels = mixedMoment B raw41552step1 raw41552step1Labels := by
      have hz : ∀ j, raw41552step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41552step1 = (fun i j => raw41552step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41552step1 raw41552step0; decide +kernel
      have hl : raw41552step1Labels = raw41552step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41552step0 raw41552step0Labels permutation80 hz
    mixedMoment B raw41552step1 raw41552step1Labels = mixedMoment B raw41552step2 raw41552step2Labels := by
      have ha : raw41552step2 = raw41552step1 := by apply Matrix.ext; unfold raw41552step2 raw41552step1; decide +kernel
      have hl : raw41552step1Labels = labelEmbedding1 ∘ raw41552step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41552step1 raw41552step1Labels raw41552step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3112 node3112Labels := by rfl

def raw41553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41553Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw41553step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41553step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw41553step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41553step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw41553step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41553step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw41553step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41553 raw41553Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw41553 raw41553Labels = mixedMoment B raw41553step0 raw41553step0Labels := by
      have hz : ∀ j, raw41553 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41553step0 = (fun i j => raw41553 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41553step0 raw41553; decide +kernel
      have hl : raw41553step0Labels = raw41553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41553 raw41553Labels permutation434 hz
    mixedMoment B raw41553step0 raw41553step0Labels = mixedMoment B raw41553step1 raw41553step1Labels := by
      have hz : ∀ j, raw41553step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41553step1 = (fun i j => raw41553step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41553step1 raw41553step0; decide +kernel
      have hl : raw41553step1Labels = raw41553step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41553step0 raw41553step0Labels permutation80 hz
    mixedMoment B raw41553step1 raw41553step1Labels = mixedMoment B raw41553step2 raw41553step2Labels := by
      have ha : raw41553step2 = (fun i j => raw41553step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41553step2 raw41553step1; decide +kernel
      have hl : raw41553step2Labels = raw41553step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41553step1 raw41553step1Labels permutation8 permutation3
    mixedMoment B raw41553step2 raw41553step2Labels = mixedMoment B raw41553step3 raw41553step3Labels := by
      have ha : raw41553step3 = raw41553step2 := by apply Matrix.ext; unfold raw41553step3 raw41553step2; decide +kernel
      have hl : raw41553step2Labels = labelEmbedding7 ∘ raw41553step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41553step2 raw41553step2Labels raw41553step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw41554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41554Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41554step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41554step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41554step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41554 raw41554Labels = mixedMoment B node3110 node3110Labels := by
  calc
    mixedMoment B raw41554 raw41554Labels = mixedMoment B raw41554step0 raw41554step0Labels := by
      have hz : ∀ j, raw41554 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41554step0 = (fun i j => raw41554 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41554step0 raw41554; decide +kernel
      have hl : raw41554step0Labels = raw41554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41554 raw41554Labels permutation434 hz
    mixedMoment B raw41554step0 raw41554step0Labels = mixedMoment B raw41554step1 raw41554step1Labels := by
      have hz : ∀ j, raw41554step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41554step1 = (fun i j => raw41554step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41554step1 raw41554step0; decide +kernel
      have hl : raw41554step1Labels = raw41554step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41554step0 raw41554step0Labels permutation80 hz
    mixedMoment B raw41554step1 raw41554step1Labels = mixedMoment B raw41554step2 raw41554step2Labels := by
      have ha : raw41554step2 = raw41554step1 := by apply Matrix.ext; unfold raw41554step2 raw41554step1; decide +kernel
      have hl : raw41554step1Labels = labelEmbedding1 ∘ raw41554step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41554step1 raw41554step1Labels raw41554step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3110 node3110Labels := by rfl

def raw41555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41555Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw41555step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw41555step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41555step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41555step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41555step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw41555step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41555 raw41555Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw41555 raw41555Labels = mixedMoment B raw41555step0 raw41555step0Labels := by
      have hz : ∀ j, raw41555 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41555step0 = (fun i j => raw41555 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41555step0 raw41555; decide +kernel
      have hl : raw41555step0Labels = raw41555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41555 raw41555Labels permutation434 hz
    mixedMoment B raw41555step0 raw41555step0Labels = mixedMoment B raw41555step1 raw41555step1Labels := by
      have hz : ∀ j, raw41555step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41555step1 = (fun i j => raw41555step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41555step1 raw41555step0; decide +kernel
      have hl : raw41555step1Labels = raw41555step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41555step0 raw41555step0Labels permutation80 hz
    mixedMoment B raw41555step1 raw41555step1Labels = mixedMoment B raw41555step2 raw41555step2Labels := by
      have ha : raw41555step2 = (fun i j => raw41555step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41555step2 raw41555step1; decide +kernel
      have hl : raw41555step2Labels = raw41555step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41555step1 raw41555step1Labels permutation8 permutation3
    mixedMoment B raw41555step2 raw41555step2Labels = mixedMoment B raw41555step3 raw41555step3Labels := by
      have ha : raw41555step3 = raw41555step2 := by apply Matrix.ext; unfold raw41555step3 raw41555step2; decide +kernel
      have hl : raw41555step2Labels = labelEmbedding7 ∘ raw41555step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41555step2 raw41555step2Labels raw41555step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw41556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41556Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41556step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41556step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41556step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41556step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw41556step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41556step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw41556step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41556 raw41556Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw41556 raw41556Labels = mixedMoment B raw41556step0 raw41556step0Labels := by
      have hz : ∀ j, raw41556 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41556step0 = (fun i j => raw41556 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41556step0 raw41556; decide +kernel
      have hl : raw41556step0Labels = raw41556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41556 raw41556Labels permutation434 hz
    mixedMoment B raw41556step0 raw41556step0Labels = mixedMoment B raw41556step1 raw41556step1Labels := by
      have hz : ∀ j, raw41556step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41556step1 = (fun i j => raw41556step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41556step1 raw41556step0; decide +kernel
      have hl : raw41556step1Labels = raw41556step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41556step0 raw41556step0Labels permutation80 hz
    mixedMoment B raw41556step1 raw41556step1Labels = mixedMoment B raw41556step2 raw41556step2Labels := by
      have ha : raw41556step2 = (fun i j => raw41556step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41556step2 raw41556step1; decide +kernel
      have hl : raw41556step2Labels = raw41556step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41556step1 raw41556step1Labels permutation25 permutation4
    mixedMoment B raw41556step2 raw41556step2Labels = mixedMoment B raw41556step3 raw41556step3Labels := by
      have ha : raw41556step3 = raw41556step2 := by apply Matrix.ext; unfold raw41556step3 raw41556step2; decide +kernel
      have hl : raw41556step2Labels = labelEmbedding1 ∘ raw41556step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41556step2 raw41556step2Labels raw41556step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2777 node2777Labels := by rfl

def raw41557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41557Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw41557step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw41557step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41557step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41557step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41557step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41557step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41557 raw41557Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw41557 raw41557Labels = mixedMoment B raw41557step0 raw41557step0Labels := by
      have hz : ∀ j, raw41557 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41557step0 = (fun i j => raw41557 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41557step0 raw41557; decide +kernel
      have hl : raw41557step0Labels = raw41557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41557 raw41557Labels permutation434 hz
    mixedMoment B raw41557step0 raw41557step0Labels = mixedMoment B raw41557step1 raw41557step1Labels := by
      have hz : ∀ j, raw41557step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41557step1 = (fun i j => raw41557step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41557step1 raw41557step0; decide +kernel
      have hl : raw41557step1Labels = raw41557step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41557step0 raw41557step0Labels permutation80 hz
    mixedMoment B raw41557step1 raw41557step1Labels = mixedMoment B raw41557step2 raw41557step2Labels := by
      have ha : raw41557step2 = (fun i j => raw41557step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41557step2 raw41557step1; decide +kernel
      have hl : raw41557step2Labels = raw41557step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41557step1 raw41557step1Labels permutation8 permutation3
    mixedMoment B raw41557step2 raw41557step2Labels = mixedMoment B raw41557step3 raw41557step3Labels := by
      have ha : raw41557step3 = raw41557step2 := by apply Matrix.ext; unfold raw41557step3 raw41557step2; decide +kernel
      have hl : raw41557step2Labels = labelEmbedding7 ∘ raw41557step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41557step2 raw41557step2Labels raw41557step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw41558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41558Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41558step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41558step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41558step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41558step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41558 raw41558Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw41558 raw41558Labels = mixedMoment B raw41558step0 raw41558step0Labels := by
      have hz : ∀ j, raw41558 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41558step0 = (fun i j => raw41558 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41558step0 raw41558; decide +kernel
      have hl : raw41558step0Labels = raw41558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41558 raw41558Labels permutation346 hz
    mixedMoment B raw41558step0 raw41558step0Labels = mixedMoment B raw41558step1 raw41558step1Labels := by
      have ha : raw41558step1 = (fun i j => raw41558step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41558step1 raw41558step0; decide +kernel
      have hl : raw41558step1Labels = raw41558step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41558step0 raw41558step0Labels permutation38 permutation2
    mixedMoment B raw41558step1 raw41558step1Labels = mixedMoment B raw41558step2 raw41558step2Labels := by
      have ha : raw41558step2 = raw41558step1 := by apply Matrix.ext; unfold raw41558step2 raw41558step1; decide +kernel
      have hl : raw41558step1Labels = labelEmbedding1 ∘ raw41558step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41558step1 raw41558step1Labels raw41558step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw41559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41559Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw41559step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41559step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41559step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41559step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41559 raw41559Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw41559 raw41559Labels = mixedMoment B raw41559step0 raw41559step0Labels := by
      have hz : ∀ j, raw41559 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41559step0 = (fun i j => raw41559 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41559step0 raw41559; decide +kernel
      have hl : raw41559step0Labels = raw41559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41559 raw41559Labels permutation346 hz
    mixedMoment B raw41559step0 raw41559step0Labels = mixedMoment B raw41559step1 raw41559step1Labels := by
      have ha : raw41559step1 = (fun i j => raw41559step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41559step1 raw41559step0; decide +kernel
      have hl : raw41559step1Labels = raw41559step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41559step0 raw41559step0Labels permutation32 permutation3
    mixedMoment B raw41559step1 raw41559step1Labels = mixedMoment B raw41559step2 raw41559step2Labels := by
      have ha : raw41559step2 = raw41559step1 := by apply Matrix.ext; unfold raw41559step2 raw41559step1; decide +kernel
      have hl : raw41559step1Labels = labelEmbedding7 ∘ raw41559step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41559step1 raw41559step1Labels raw41559step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw41560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41560Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41560step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41560step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41560step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41560step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41560 raw41560Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw41560 raw41560Labels = mixedMoment B raw41560step0 raw41560step0Labels := by
      have hz : ∀ j, raw41560 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41560step0 = (fun i j => raw41560 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41560step0 raw41560; decide +kernel
      have hl : raw41560step0Labels = raw41560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41560 raw41560Labels permutation346 hz
    mixedMoment B raw41560step0 raw41560step0Labels = mixedMoment B raw41560step1 raw41560step1Labels := by
      have ha : raw41560step1 = (fun i j => raw41560step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41560step1 raw41560step0; decide +kernel
      have hl : raw41560step1Labels = raw41560step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41560step0 raw41560step0Labels permutation38 permutation2
    mixedMoment B raw41560step1 raw41560step1Labels = mixedMoment B raw41560step2 raw41560step2Labels := by
      have ha : raw41560step2 = raw41560step1 := by apply Matrix.ext; unfold raw41560step2 raw41560step1; decide +kernel
      have hl : raw41560step1Labels = labelEmbedding1 ∘ raw41560step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41560step1 raw41560step1Labels raw41560step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw41561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41561Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41561step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41561step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41561step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41561step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41561 raw41561Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw41561 raw41561Labels = mixedMoment B raw41561step0 raw41561step0Labels := by
      have hz : ∀ j, raw41561 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41561step0 = (fun i j => raw41561 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41561step0 raw41561; decide +kernel
      have hl : raw41561step0Labels = raw41561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41561 raw41561Labels permutation346 hz
    mixedMoment B raw41561step0 raw41561step0Labels = mixedMoment B raw41561step1 raw41561step1Labels := by
      have ha : raw41561step1 = (fun i j => raw41561step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41561step1 raw41561step0; decide +kernel
      have hl : raw41561step1Labels = raw41561step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41561step0 raw41561step0Labels permutation32 permutation3
    mixedMoment B raw41561step1 raw41561step1Labels = mixedMoment B raw41561step2 raw41561step2Labels := by
      have ha : raw41561step2 = raw41561step1 := by apply Matrix.ext; unfold raw41561step2 raw41561step1; decide +kernel
      have hl : raw41561step1Labels = labelEmbedding7 ∘ raw41561step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41561step1 raw41561step1Labels raw41561step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw41562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41562Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41562step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41562step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41562step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41562step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41562 raw41562Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw41562 raw41562Labels = mixedMoment B raw41562step0 raw41562step0Labels := by
      have hz : ∀ j, raw41562 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41562step0 = (fun i j => raw41562 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41562step0 raw41562; decide +kernel
      have hl : raw41562step0Labels = raw41562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41562 raw41562Labels permutation346 hz
    mixedMoment B raw41562step0 raw41562step0Labels = mixedMoment B raw41562step1 raw41562step1Labels := by
      have ha : raw41562step1 = (fun i j => raw41562step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41562step1 raw41562step0; decide +kernel
      have hl : raw41562step1Labels = raw41562step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41562step0 raw41562step0Labels permutation38 permutation2
    mixedMoment B raw41562step1 raw41562step1Labels = mixedMoment B raw41562step2 raw41562step2Labels := by
      have ha : raw41562step2 = raw41562step1 := by apply Matrix.ext; unfold raw41562step2 raw41562step1; decide +kernel
      have hl : raw41562step1Labels = labelEmbedding1 ∘ raw41562step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41562step1 raw41562step1Labels raw41562step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw41563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41563Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41563step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41563step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41563step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw41563step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41563 raw41563Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw41563 raw41563Labels = mixedMoment B raw41563step0 raw41563step0Labels := by
      have hz : ∀ j, raw41563 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41563step0 = (fun i j => raw41563 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41563step0 raw41563; decide +kernel
      have hl : raw41563step0Labels = raw41563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41563 raw41563Labels permutation346 hz
    mixedMoment B raw41563step0 raw41563step0Labels = mixedMoment B raw41563step1 raw41563step1Labels := by
      have ha : raw41563step1 = (fun i j => raw41563step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41563step1 raw41563step0; decide +kernel
      have hl : raw41563step1Labels = raw41563step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41563step0 raw41563step0Labels permutation32 permutation3
    mixedMoment B raw41563step1 raw41563step1Labels = mixedMoment B raw41563step2 raw41563step2Labels := by
      have ha : raw41563step2 = raw41563step1 := by apply Matrix.ext; unfold raw41563step2 raw41563step1; decide +kernel
      have hl : raw41563step1Labels = labelEmbedding7 ∘ raw41563step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41563step1 raw41563step1Labels raw41563step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw41564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41564Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41564step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41564step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41564step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41564 raw41564Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw41564 raw41564Labels = mixedMoment B raw41564step0 raw41564step0Labels := by
      have hz : ∀ j, raw41564 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41564step0 = (fun i j => raw41564 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41564step0 raw41564; decide +kernel
      have hl : raw41564step0Labels = raw41564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41564 raw41564Labels permutation346 hz
    mixedMoment B raw41564step0 raw41564step0Labels = mixedMoment B raw41564step1 raw41564step1Labels := by
      have ha : raw41564step1 = (fun i j => raw41564step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41564step1 raw41564step0; decide +kernel
      have hl : raw41564step1Labels = raw41564step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41564step0 raw41564step0Labels permutation38 permutation2
    mixedMoment B raw41564step1 raw41564step1Labels = mixedMoment B raw41564step2 raw41564step2Labels := by
      have ha : raw41564step2 = raw41564step1 := by apply Matrix.ext; unfold raw41564step2 raw41564step1; decide +kernel
      have hl : raw41564step1Labels = labelEmbedding1 ∘ raw41564step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41564step1 raw41564step1Labels raw41564step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw41565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41565Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41565step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41565step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41565step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41565step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41565 raw41565Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw41565 raw41565Labels = mixedMoment B raw41565step0 raw41565step0Labels := by
      have hz : ∀ j, raw41565 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41565step0 = (fun i j => raw41565 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41565step0 raw41565; decide +kernel
      have hl : raw41565step0Labels = raw41565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41565 raw41565Labels permutation346 hz
    mixedMoment B raw41565step0 raw41565step0Labels = mixedMoment B raw41565step1 raw41565step1Labels := by
      have ha : raw41565step1 = (fun i j => raw41565step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41565step1 raw41565step0; decide +kernel
      have hl : raw41565step1Labels = raw41565step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41565step0 raw41565step0Labels permutation32 permutation3
    mixedMoment B raw41565step1 raw41565step1Labels = mixedMoment B raw41565step2 raw41565step2Labels := by
      have ha : raw41565step2 = raw41565step1 := by apply Matrix.ext; unfold raw41565step2 raw41565step1; decide +kernel
      have hl : raw41565step1Labels = labelEmbedding7 ∘ raw41565step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41565step1 raw41565step1Labels raw41565step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw41566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41566Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41566step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41566step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41566step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw41566step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41566 raw41566Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw41566 raw41566Labels = mixedMoment B raw41566step0 raw41566step0Labels := by
      have hz : ∀ j, raw41566 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41566step0 = (fun i j => raw41566 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41566step0 raw41566; decide +kernel
      have hl : raw41566step0Labels = raw41566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41566 raw41566Labels permutation346 hz
    mixedMoment B raw41566step0 raw41566step0Labels = mixedMoment B raw41566step1 raw41566step1Labels := by
      have ha : raw41566step1 = (fun i j => raw41566step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41566step1 raw41566step0; decide +kernel
      have hl : raw41566step1Labels = raw41566step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41566step0 raw41566step0Labels permutation145 permutation4
    mixedMoment B raw41566step1 raw41566step1Labels = mixedMoment B raw41566step2 raw41566step2Labels := by
      have ha : raw41566step2 = raw41566step1 := by apply Matrix.ext; unfold raw41566step2 raw41566step1; decide +kernel
      have hl : raw41566step1Labels = labelEmbedding1 ∘ raw41566step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41566step1 raw41566step1Labels raw41566step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2754 node2754Labels := by rfl

def raw41567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41567Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw41567step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41567step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41567step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41567step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41567 raw41567Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw41567 raw41567Labels = mixedMoment B raw41567step0 raw41567step0Labels := by
      have hz : ∀ j, raw41567 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41567step0 = (fun i j => raw41567 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41567step0 raw41567; decide +kernel
      have hl : raw41567step0Labels = raw41567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41567 raw41567Labels permutation346 hz
    mixedMoment B raw41567step0 raw41567step0Labels = mixedMoment B raw41567step1 raw41567step1Labels := by
      have ha : raw41567step1 = (fun i j => raw41567step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41567step1 raw41567step0; decide +kernel
      have hl : raw41567step1Labels = raw41567step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41567step0 raw41567step0Labels permutation32 permutation3
    mixedMoment B raw41567step1 raw41567step1Labels = mixedMoment B raw41567step2 raw41567step2Labels := by
      have ha : raw41567step2 = raw41567step1 := by apply Matrix.ext; unfold raw41567step2 raw41567step1; decide +kernel
      have hl : raw41567step1Labels = labelEmbedding7 ∘ raw41567step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41567step1 raw41567step1Labels raw41567step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw41568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41568Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41568step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41568step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41568step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41568step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41568 raw41568Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw41568 raw41568Labels = mixedMoment B raw41568step0 raw41568step0Labels := by
      have hz : ∀ j, raw41568 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41568step0 = (fun i j => raw41568 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41568step0 raw41568; decide +kernel
      have hl : raw41568step0Labels = raw41568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41568 raw41568Labels permutation346 hz
    mixedMoment B raw41568step0 raw41568step0Labels = mixedMoment B raw41568step1 raw41568step1Labels := by
      have ha : raw41568step1 = (fun i j => raw41568step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41568step1 raw41568step0; decide +kernel
      have hl : raw41568step1Labels = raw41568step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41568step0 raw41568step0Labels permutation37 permutation2
    mixedMoment B raw41568step1 raw41568step1Labels = mixedMoment B raw41568step2 raw41568step2Labels := by
      have ha : raw41568step2 = raw41568step1 := by apply Matrix.ext; unfold raw41568step2 raw41568step1; decide +kernel
      have hl : raw41568step1Labels = labelEmbedding1 ∘ raw41568step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41568step1 raw41568step1Labels raw41568step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw41569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41569Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41569step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41569step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41569step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41569step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41569 raw41569Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw41569 raw41569Labels = mixedMoment B raw41569step0 raw41569step0Labels := by
      have hz : ∀ j, raw41569 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41569step0 = (fun i j => raw41569 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41569step0 raw41569; decide +kernel
      have hl : raw41569step0Labels = raw41569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41569 raw41569Labels permutation346 hz
    mixedMoment B raw41569step0 raw41569step0Labels = mixedMoment B raw41569step1 raw41569step1Labels := by
      have ha : raw41569step1 = (fun i j => raw41569step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41569step1 raw41569step0; decide +kernel
      have hl : raw41569step1Labels = raw41569step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41569step0 raw41569step0Labels permutation32 permutation3
    mixedMoment B raw41569step1 raw41569step1Labels = mixedMoment B raw41569step2 raw41569step2Labels := by
      have ha : raw41569step2 = raw41569step1 := by apply Matrix.ext; unfold raw41569step2 raw41569step1; decide +kernel
      have hl : raw41569step1Labels = labelEmbedding7 ∘ raw41569step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41569step1 raw41569step1Labels raw41569step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw41570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41570Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41570step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41570 raw41570Labels = mixedMoment B node3111 node3111Labels := by
  calc
    mixedMoment B raw41570 raw41570Labels = mixedMoment B raw41570step0 raw41570step0Labels := by
      have hz : ∀ j, raw41570 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41570step0 = (fun i j => raw41570 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41570step0 raw41570; decide +kernel
      have hl : raw41570step0Labels = raw41570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41570 raw41570Labels permutation346 hz
    mixedMoment B raw41570step0 raw41570step0Labels = mixedMoment B raw41570step1 raw41570step1Labels := by
      have ha : raw41570step1 = raw41570step0 := by apply Matrix.ext; unfold raw41570step1 raw41570step0; decide +kernel
      have hl : raw41570step0Labels = labelEmbedding1 ∘ raw41570step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41570step0 raw41570step0Labels raw41570step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3111 node3111Labels := by rfl

def raw41571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41571Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41571step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41571step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41571step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41571step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41571 raw41571Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw41571 raw41571Labels = mixedMoment B raw41571step0 raw41571step0Labels := by
      have hz : ∀ j, raw41571 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41571step0 = (fun i j => raw41571 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41571step0 raw41571; decide +kernel
      have hl : raw41571step0Labels = raw41571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41571 raw41571Labels permutation346 hz
    mixedMoment B raw41571step0 raw41571step0Labels = mixedMoment B raw41571step1 raw41571step1Labels := by
      have ha : raw41571step1 = (fun i j => raw41571step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41571step1 raw41571step0; decide +kernel
      have hl : raw41571step1Labels = raw41571step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41571step0 raw41571step0Labels permutation32 permutation3
    mixedMoment B raw41571step1 raw41571step1Labels = mixedMoment B raw41571step2 raw41571step2Labels := by
      have ha : raw41571step2 = raw41571step1 := by apply Matrix.ext; unfold raw41571step2 raw41571step1; decide +kernel
      have hl : raw41571step1Labels = labelEmbedding7 ∘ raw41571step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41571step1 raw41571step1Labels raw41571step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5273 node5273Labels := by rfl

def raw41572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41572Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41572step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41572step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41572 raw41572Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw41572 raw41572Labels = mixedMoment B raw41572step0 raw41572step0Labels := by
      have ha : raw41572step0 = (fun i j => raw41572 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41572step0 raw41572; decide +kernel
      have hl : raw41572step0Labels = raw41572Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41572 raw41572Labels permutation182 permutation2
    mixedMoment B raw41572step0 raw41572step0Labels = mixedMoment B raw41572step1 raw41572step1Labels := by
      have ha : raw41572step1 = raw41572step0 := by apply Matrix.ext; unfold raw41572step1 raw41572step0; decide +kernel
      have hl : raw41572step0Labels = labelEmbedding1 ∘ raw41572step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41572step0 raw41572step0Labels raw41572step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3064 node3064Labels := by rfl

def raw41573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41573Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41573step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41573step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw41573step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41573 raw41573Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw41573 raw41573Labels = mixedMoment B raw41573step0 raw41573step0Labels := by
      have ha : raw41573step0 = (fun i j => raw41573 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41573step0 raw41573; decide +kernel
      have hl : raw41573step0Labels = raw41573Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41573 raw41573Labels permutation152 permutation3
    mixedMoment B raw41573step0 raw41573step0Labels = mixedMoment B raw41573step1 raw41573step1Labels := by
      have ha : raw41573step1 = raw41573step0 := by apply Matrix.ext; unfold raw41573step1 raw41573step0; decide +kernel
      have hl : raw41573step0Labels = labelEmbedding7 ∘ raw41573step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41573step0 raw41573step0Labels raw41573step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw41574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41574Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41574step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41574step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41574 raw41574Labels = mixedMoment B node3085 node3085Labels := by
  calc
    mixedMoment B raw41574 raw41574Labels = mixedMoment B raw41574step0 raw41574step0Labels := by
      have ha : raw41574step0 = (fun i j => raw41574 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41574step0 raw41574; decide +kernel
      have hl : raw41574step0Labels = raw41574Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41574 raw41574Labels permutation180 permutation2
    mixedMoment B raw41574step0 raw41574step0Labels = mixedMoment B raw41574step1 raw41574step1Labels := by
      have ha : raw41574step1 = raw41574step0 := by apply Matrix.ext; unfold raw41574step1 raw41574step0; decide +kernel
      have hl : raw41574step0Labels = labelEmbedding1 ∘ raw41574step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41574step0 raw41574step0Labels raw41574step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3085 node3085Labels := by rfl

def raw41575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41575Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41575step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41575step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41575step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41575 raw41575Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw41575 raw41575Labels = mixedMoment B raw41575step0 raw41575step0Labels := by
      have ha : raw41575step0 = (fun i j => raw41575 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41575step0 raw41575; decide +kernel
      have hl : raw41575step0Labels = raw41575Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41575 raw41575Labels permutation152 permutation3
    mixedMoment B raw41575step0 raw41575step0Labels = mixedMoment B raw41575step1 raw41575step1Labels := by
      have ha : raw41575step1 = raw41575step0 := by apply Matrix.ext; unfold raw41575step1 raw41575step0; decide +kernel
      have hl : raw41575step0Labels = labelEmbedding7 ∘ raw41575step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41575step0 raw41575step0Labels raw41575step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5256 node5256Labels := by rfl

def raw41576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41576Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41576step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41576step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41576 raw41576Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw41576 raw41576Labels = mixedMoment B raw41576step0 raw41576step0Labels := by
      have ha : raw41576step0 = (fun i j => raw41576 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41576step0 raw41576; decide +kernel
      have hl : raw41576step0Labels = raw41576Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41576 raw41576Labels permutation179 permutation2
    mixedMoment B raw41576step0 raw41576step0Labels = mixedMoment B raw41576step1 raw41576step1Labels := by
      have ha : raw41576step1 = raw41576step0 := by apply Matrix.ext; unfold raw41576step1 raw41576step0; decide +kernel
      have hl : raw41576step0Labels = labelEmbedding1 ∘ raw41576step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41576step0 raw41576step0Labels raw41576step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3087 node3087Labels := by rfl

def raw41577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41577Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41577step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41577step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41577step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41577 raw41577Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw41577 raw41577Labels = mixedMoment B raw41577step0 raw41577step0Labels := by
      have ha : raw41577step0 = (fun i j => raw41577 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41577step0 raw41577; decide +kernel
      have hl : raw41577step0Labels = raw41577Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41577 raw41577Labels permutation152 permutation3
    mixedMoment B raw41577step0 raw41577step0Labels = mixedMoment B raw41577step1 raw41577step1Labels := by
      have ha : raw41577step1 = raw41577step0 := by apply Matrix.ext; unfold raw41577step1 raw41577step0; decide +kernel
      have hl : raw41577step0Labels = labelEmbedding7 ∘ raw41577step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41577step0 raw41577step0Labels raw41577step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw41578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41578Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41578step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41578step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41578step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41578 raw41578Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw41578 raw41578Labels = mixedMoment B raw41578step0 raw41578step0Labels := by
      have ha : raw41578step0 = (fun i j => raw41578 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41578step0 raw41578; decide +kernel
      have hl : raw41578step0Labels = raw41578Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41578 raw41578Labels permutation180 permutation2
    mixedMoment B raw41578step0 raw41578step0Labels = mixedMoment B raw41578step1 raw41578step1Labels := by
      have ha : raw41578step1 = raw41578step0 := by apply Matrix.ext; unfold raw41578step1 raw41578step0; decide +kernel
      have hl : raw41578step0Labels = labelEmbedding1 ∘ raw41578step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41578step0 raw41578step0Labels raw41578step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3037 node3037Labels := by rfl

def raw41579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw41579Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41579step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41579step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41579step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41579 raw41579Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw41579 raw41579Labels = mixedMoment B raw41579step0 raw41579step0Labels := by
      have ha : raw41579step0 = (fun i j => raw41579 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41579step0 raw41579; decide +kernel
      have hl : raw41579step0Labels = raw41579Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41579 raw41579Labels permutation152 permutation3
    mixedMoment B raw41579step0 raw41579step0Labels = mixedMoment B raw41579step1 raw41579step1Labels := by
      have ha : raw41579step1 = raw41579step0 := by apply Matrix.ext; unfold raw41579step1 raw41579step0; decide +kernel
      have hl : raw41579step0Labels = labelEmbedding7 ∘ raw41579step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41579step0 raw41579step0Labels raw41579step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw41580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41580Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41580step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41580step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41580step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41580step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw41580step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41580step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw41580step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41580 raw41580Labels = mixedMoment B node3125 node3125Labels := by
  calc
    mixedMoment B raw41580 raw41580Labels = mixedMoment B raw41580step0 raw41580step0Labels := by
      have hz : ∀ j, raw41580 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41580step0 = (fun i j => raw41580 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41580step0 raw41580; decide +kernel
      have hl : raw41580step0Labels = raw41580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41580 raw41580Labels permutation434 hz
    mixedMoment B raw41580step0 raw41580step0Labels = mixedMoment B raw41580step1 raw41580step1Labels := by
      have hz : ∀ j, raw41580step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41580step1 = (fun i j => raw41580step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41580step1 raw41580step0; decide +kernel
      have hl : raw41580step1Labels = raw41580step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41580step0 raw41580step0Labels permutation80 hz
    mixedMoment B raw41580step1 raw41580step1Labels = mixedMoment B raw41580step2 raw41580step2Labels := by
      have hz : ∀ j, raw41580step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41580step2 = (fun i j => raw41580step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41580step2 raw41580step1; decide +kernel
      have hl : raw41580step2Labels = raw41580step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41580step1 raw41580step1Labels permutation14 hz
    mixedMoment B raw41580step2 raw41580step2Labels = mixedMoment B raw41580step3 raw41580step3Labels := by
      have ha : raw41580step3 = raw41580step2 := by apply Matrix.ext; unfold raw41580step3 raw41580step2; decide +kernel
      have hl : raw41580step2Labels = labelEmbedding1 ∘ raw41580step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41580step2 raw41580step2Labels raw41580step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3125 node3125Labels := by rfl

def raw41581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41581Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41581step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw41581step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41581step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw41581step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41581step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw41581step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41581step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw41581step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41581 raw41581Labels = mixedMoment B node5305 node5305Labels := by
  calc
    mixedMoment B raw41581 raw41581Labels = mixedMoment B raw41581step0 raw41581step0Labels := by
      have hz : ∀ j, raw41581 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41581step0 = (fun i j => raw41581 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41581step0 raw41581; decide +kernel
      have hl : raw41581step0Labels = raw41581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41581 raw41581Labels permutation434 hz
    mixedMoment B raw41581step0 raw41581step0Labels = mixedMoment B raw41581step1 raw41581step1Labels := by
      have hz : ∀ j, raw41581step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41581step1 = (fun i j => raw41581step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41581step1 raw41581step0; decide +kernel
      have hl : raw41581step1Labels = raw41581step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41581step0 raw41581step0Labels permutation80 hz
    mixedMoment B raw41581step1 raw41581step1Labels = mixedMoment B raw41581step2 raw41581step2Labels := by
      have hz : ∀ j, raw41581step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41581step2 = (fun i j => raw41581step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41581step2 raw41581step1; decide +kernel
      have hl : raw41581step2Labels = raw41581step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41581step1 raw41581step1Labels permutation14 hz
    mixedMoment B raw41581step2 raw41581step2Labels = mixedMoment B raw41581step3 raw41581step3Labels := by
      have ha : raw41581step3 = (fun i j => raw41581step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41581step3 raw41581step2; decide +kernel
      have hl : raw41581step3Labels = raw41581step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41581step2 raw41581step2Labels permutation2 permutation3
    mixedMoment B raw41581step3 raw41581step3Labels = mixedMoment B raw41581step4 raw41581step4Labels := by
      have ha : raw41581step4 = raw41581step3 := by apply Matrix.ext; unfold raw41581step4 raw41581step3; decide +kernel
      have hl : raw41581step3Labels = labelEmbedding7 ∘ raw41581step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41581step3 raw41581step3Labels raw41581step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5305 node5305Labels := by rfl

def raw41582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41582Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41582step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41582step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41582step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41582step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![2, 1, -3]]
def raw41582step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41582step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw41582step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41582step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw41582step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41582 raw41582Labels = mixedMoment B node2789 node2789Labels := by
  calc
    mixedMoment B raw41582 raw41582Labels = mixedMoment B raw41582step0 raw41582step0Labels := by
      have hz : ∀ j, raw41582 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41582step0 = (fun i j => raw41582 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41582step0 raw41582; decide +kernel
      have hl : raw41582step0Labels = raw41582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41582 raw41582Labels permutation434 hz
    mixedMoment B raw41582step0 raw41582step0Labels = mixedMoment B raw41582step1 raw41582step1Labels := by
      have hz : ∀ j, raw41582step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41582step1 = (fun i j => raw41582step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41582step1 raw41582step0; decide +kernel
      have hl : raw41582step1Labels = raw41582step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41582step0 raw41582step0Labels permutation80 hz
    mixedMoment B raw41582step1 raw41582step1Labels = mixedMoment B raw41582step2 raw41582step2Labels := by
      have hz : ∀ j, raw41582step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41582step2 = (fun i j => raw41582step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41582step2 raw41582step1; decide +kernel
      have hl : raw41582step2Labels = raw41582step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41582step1 raw41582step1Labels permutation14 hz
    mixedMoment B raw41582step2 raw41582step2Labels = mixedMoment B raw41582step3 raw41582step3Labels := by
      have ha : raw41582step3 = (fun i j => raw41582step2 (permutation5 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41582step3 raw41582step2; decide +kernel
      have hl : raw41582step3Labels = raw41582step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41582step2 raw41582step2Labels permutation5 permutation4
    mixedMoment B raw41582step3 raw41582step3Labels = mixedMoment B raw41582step4 raw41582step4Labels := by
      have ha : raw41582step4 = raw41582step3 := by apply Matrix.ext; unfold raw41582step4 raw41582step3; decide +kernel
      have hl : raw41582step3Labels = labelEmbedding1 ∘ raw41582step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41582step3 raw41582step3Labels raw41582step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2789 node2789Labels := by rfl

def raw41583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41583Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41583step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41583step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw41583step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41583step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![2, 1, -3]]
def raw41583step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41583step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw41583step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41583step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw41583step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41583 raw41583Labels = mixedMoment B node5311 node5311Labels := by
  calc
    mixedMoment B raw41583 raw41583Labels = mixedMoment B raw41583step0 raw41583step0Labels := by
      have hz : ∀ j, raw41583 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw41583step0 = (fun i j => raw41583 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw41583step0 raw41583; decide +kernel
      have hl : raw41583step0Labels = raw41583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41583 raw41583Labels permutation434 hz
    mixedMoment B raw41583step0 raw41583step0Labels = mixedMoment B raw41583step1 raw41583step1Labels := by
      have hz : ∀ j, raw41583step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw41583step1 = (fun i j => raw41583step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw41583step1 raw41583step0; decide +kernel
      have hl : raw41583step1Labels = raw41583step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41583step0 raw41583step0Labels permutation80 hz
    mixedMoment B raw41583step1 raw41583step1Labels = mixedMoment B raw41583step2 raw41583step2Labels := by
      have hz : ∀ j, raw41583step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw41583step2 = (fun i j => raw41583step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw41583step2 raw41583step1; decide +kernel
      have hl : raw41583step2Labels = raw41583step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41583step1 raw41583step1Labels permutation14 hz
    mixedMoment B raw41583step2 raw41583step2Labels = mixedMoment B raw41583step3 raw41583step3Labels := by
      have ha : raw41583step3 = (fun i j => raw41583step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41583step3 raw41583step2; decide +kernel
      have hl : raw41583step3Labels = raw41583step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41583step2 raw41583step2Labels permutation2 permutation3
    mixedMoment B raw41583step3 raw41583step3Labels = mixedMoment B raw41583step4 raw41583step4Labels := by
      have ha : raw41583step4 = raw41583step3 := by apply Matrix.ext; unfold raw41583step4 raw41583step3; decide +kernel
      have hl : raw41583step3Labels = labelEmbedding7 ∘ raw41583step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41583step3 raw41583step3Labels raw41583step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5311 node5311Labels := by rfl

def raw41584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41584Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41584step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41584step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41584step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41584step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41584 raw41584Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw41584 raw41584Labels = mixedMoment B raw41584step0 raw41584step0Labels := by
      have hz : ∀ j, raw41584 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41584step0 = (fun i j => raw41584 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41584step0 raw41584; decide +kernel
      have hl : raw41584step0Labels = raw41584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41584 raw41584Labels permutation346 hz
    mixedMoment B raw41584step0 raw41584step0Labels = mixedMoment B raw41584step1 raw41584step1Labels := by
      have hz : ∀ j, raw41584step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41584step1 = (fun i j => raw41584step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41584step1 raw41584step0; decide +kernel
      have hl : raw41584step1Labels = raw41584step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41584step0 raw41584step0Labels permutation56 hz
    mixedMoment B raw41584step1 raw41584step1Labels = mixedMoment B raw41584step2 raw41584step2Labels := by
      have ha : raw41584step2 = raw41584step1 := by apply Matrix.ext; unfold raw41584step2 raw41584step1; decide +kernel
      have hl : raw41584step1Labels = labelEmbedding1 ∘ raw41584step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41584step1 raw41584step1Labels raw41584step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3103 node3103Labels := by rfl

def raw41585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41585Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41585step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw41585step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41585step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41585step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41585step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw41585step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41585 raw41585Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw41585 raw41585Labels = mixedMoment B raw41585step0 raw41585step0Labels := by
      have hz : ∀ j, raw41585 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41585step0 = (fun i j => raw41585 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41585step0 raw41585; decide +kernel
      have hl : raw41585step0Labels = raw41585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41585 raw41585Labels permutation346 hz
    mixedMoment B raw41585step0 raw41585step0Labels = mixedMoment B raw41585step1 raw41585step1Labels := by
      have hz : ∀ j, raw41585step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41585step1 = (fun i j => raw41585step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41585step1 raw41585step0; decide +kernel
      have hl : raw41585step1Labels = raw41585step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41585step0 raw41585step0Labels permutation56 hz
    mixedMoment B raw41585step1 raw41585step1Labels = mixedMoment B raw41585step2 raw41585step2Labels := by
      have ha : raw41585step2 = (fun i j => raw41585step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41585step2 raw41585step1; decide +kernel
      have hl : raw41585step2Labels = raw41585step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41585step1 raw41585step1Labels permutation8 permutation3
    mixedMoment B raw41585step2 raw41585step2Labels = mixedMoment B raw41585step3 raw41585step3Labels := by
      have ha : raw41585step3 = raw41585step2 := by apply Matrix.ext; unfold raw41585step3 raw41585step2; decide +kernel
      have hl : raw41585step2Labels = labelEmbedding7 ∘ raw41585step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41585step2 raw41585step2Labels raw41585step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw41586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41586Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41586step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41586step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41586step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41586 raw41586Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw41586 raw41586Labels = mixedMoment B raw41586step0 raw41586step0Labels := by
      have hz : ∀ j, raw41586 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41586step0 = (fun i j => raw41586 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41586step0 raw41586; decide +kernel
      have hl : raw41586step0Labels = raw41586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41586 raw41586Labels permutation346 hz
    mixedMoment B raw41586step0 raw41586step0Labels = mixedMoment B raw41586step1 raw41586step1Labels := by
      have hz : ∀ j, raw41586step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41586step1 = (fun i j => raw41586step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41586step1 raw41586step0; decide +kernel
      have hl : raw41586step1Labels = raw41586step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41586step0 raw41586step0Labels permutation56 hz
    mixedMoment B raw41586step1 raw41586step1Labels = mixedMoment B raw41586step2 raw41586step2Labels := by
      have ha : raw41586step2 = raw41586step1 := by apply Matrix.ext; unfold raw41586step2 raw41586step1; decide +kernel
      have hl : raw41586step1Labels = labelEmbedding1 ∘ raw41586step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41586step1 raw41586step1Labels raw41586step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw41587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41587Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41587step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41587step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw41587step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41587step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41587step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41587step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41587step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41587 raw41587Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw41587 raw41587Labels = mixedMoment B raw41587step0 raw41587step0Labels := by
      have hz : ∀ j, raw41587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41587step0 = (fun i j => raw41587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41587step0 raw41587; decide +kernel
      have hl : raw41587step0Labels = raw41587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41587 raw41587Labels permutation346 hz
    mixedMoment B raw41587step0 raw41587step0Labels = mixedMoment B raw41587step1 raw41587step1Labels := by
      have hz : ∀ j, raw41587step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41587step1 = (fun i j => raw41587step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41587step1 raw41587step0; decide +kernel
      have hl : raw41587step1Labels = raw41587step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41587step0 raw41587step0Labels permutation56 hz
    mixedMoment B raw41587step1 raw41587step1Labels = mixedMoment B raw41587step2 raw41587step2Labels := by
      have ha : raw41587step2 = (fun i j => raw41587step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41587step2 raw41587step1; decide +kernel
      have hl : raw41587step2Labels = raw41587step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41587step1 raw41587step1Labels permutation8 permutation3
    mixedMoment B raw41587step2 raw41587step2Labels = mixedMoment B raw41587step3 raw41587step3Labels := by
      have ha : raw41587step3 = raw41587step2 := by apply Matrix.ext; unfold raw41587step3 raw41587step2; decide +kernel
      have hl : raw41587step2Labels = labelEmbedding7 ∘ raw41587step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41587step2 raw41587step2Labels raw41587step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw41588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41588Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41588step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41588step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41588step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41588step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41588step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41588 raw41588Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw41588 raw41588Labels = mixedMoment B raw41588step0 raw41588step0Labels := by
      have hz : ∀ j, raw41588 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41588step0 = (fun i j => raw41588 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41588step0 raw41588; decide +kernel
      have hl : raw41588step0Labels = raw41588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41588 raw41588Labels permutation346 hz
    mixedMoment B raw41588step0 raw41588step0Labels = mixedMoment B raw41588step1 raw41588step1Labels := by
      have hz : ∀ j, raw41588step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41588step1 = (fun i j => raw41588step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41588step1 raw41588step0; decide +kernel
      have hl : raw41588step1Labels = raw41588step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41588step0 raw41588step0Labels permutation56 hz
    mixedMoment B raw41588step1 raw41588step1Labels = mixedMoment B raw41588step2 raw41588step2Labels := by
      have ha : raw41588step2 = raw41588step1 := by apply Matrix.ext; unfold raw41588step2 raw41588step1; decide +kernel
      have hl : raw41588step1Labels = labelEmbedding1 ∘ raw41588step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41588step1 raw41588step1Labels raw41588step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3052 node3052Labels := by rfl

def raw41589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41589Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41589step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41589step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw41589step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41589step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41589step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41589step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw41589step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41589 raw41589Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw41589 raw41589Labels = mixedMoment B raw41589step0 raw41589step0Labels := by
      have hz : ∀ j, raw41589 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41589step0 = (fun i j => raw41589 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41589step0 raw41589; decide +kernel
      have hl : raw41589step0Labels = raw41589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41589 raw41589Labels permutation346 hz
    mixedMoment B raw41589step0 raw41589step0Labels = mixedMoment B raw41589step1 raw41589step1Labels := by
      have hz : ∀ j, raw41589step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41589step1 = (fun i j => raw41589step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41589step1 raw41589step0; decide +kernel
      have hl : raw41589step1Labels = raw41589step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41589step0 raw41589step0Labels permutation56 hz
    mixedMoment B raw41589step1 raw41589step1Labels = mixedMoment B raw41589step2 raw41589step2Labels := by
      have ha : raw41589step2 = (fun i j => raw41589step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41589step2 raw41589step1; decide +kernel
      have hl : raw41589step2Labels = raw41589step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41589step1 raw41589step1Labels permutation30 permutation7
    mixedMoment B raw41589step2 raw41589step2Labels = mixedMoment B raw41589step3 raw41589step3Labels := by
      have ha : raw41589step3 = raw41589step2 := by apply Matrix.ext; unfold raw41589step3 raw41589step2; decide +kernel
      have hl : raw41589step2Labels = labelEmbedding6 ∘ raw41589step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41589step2 raw41589step2Labels raw41589step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw41590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41590Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41590step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41590step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41590step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41590step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41590step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41590step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41590 raw41590Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw41590 raw41590Labels = mixedMoment B raw41590step0 raw41590step0Labels := by
      have hz : ∀ j, raw41590 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41590step0 = (fun i j => raw41590 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41590step0 raw41590; decide +kernel
      have hl : raw41590step0Labels = raw41590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41590 raw41590Labels permutation346 hz
    mixedMoment B raw41590step0 raw41590step0Labels = mixedMoment B raw41590step1 raw41590step1Labels := by
      have hz : ∀ j, raw41590step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41590step1 = (fun i j => raw41590step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41590step1 raw41590step0; decide +kernel
      have hl : raw41590step1Labels = raw41590step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41590step0 raw41590step0Labels permutation56 hz
    mixedMoment B raw41590step1 raw41590step1Labels = mixedMoment B raw41590step2 raw41590step2Labels := by
      have ha : raw41590step2 = (fun i j => raw41590step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41590step2 raw41590step1; decide +kernel
      have hl : raw41590step2Labels = raw41590step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41590step1 raw41590step1Labels permutation31 permutation4
    mixedMoment B raw41590step2 raw41590step2Labels = mixedMoment B raw41590step3 raw41590step3Labels := by
      have ha : raw41590step3 = raw41590step2 := by apply Matrix.ext; unfold raw41590step3 raw41590step2; decide +kernel
      have hl : raw41590step2Labels = labelEmbedding1 ∘ raw41590step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41590step2 raw41590step2Labels raw41590step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw41591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41591Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41591step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41591step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw41591step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41591step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41591step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw41591step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw41591step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41591 raw41591Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw41591 raw41591Labels = mixedMoment B raw41591step0 raw41591step0Labels := by
      have hz : ∀ j, raw41591 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41591step0 = (fun i j => raw41591 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41591step0 raw41591; decide +kernel
      have hl : raw41591step0Labels = raw41591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41591 raw41591Labels permutation346 hz
    mixedMoment B raw41591step0 raw41591step0Labels = mixedMoment B raw41591step1 raw41591step1Labels := by
      have hz : ∀ j, raw41591step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41591step1 = (fun i j => raw41591step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41591step1 raw41591step0; decide +kernel
      have hl : raw41591step1Labels = raw41591step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41591step0 raw41591step0Labels permutation56 hz
    mixedMoment B raw41591step1 raw41591step1Labels = mixedMoment B raw41591step2 raw41591step2Labels := by
      have ha : raw41591step2 = (fun i j => raw41591step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41591step2 raw41591step1; decide +kernel
      have hl : raw41591step2Labels = raw41591step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41591step1 raw41591step1Labels permutation31 permutation4
    mixedMoment B raw41591step2 raw41591step2Labels = mixedMoment B raw41591step3 raw41591step3Labels := by
      have ha : raw41591step3 = raw41591step2 := by apply Matrix.ext; unfold raw41591step3 raw41591step2; decide +kernel
      have hl : raw41591step2Labels = labelEmbedding10 ∘ raw41591step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41591step2 raw41591step2Labels raw41591step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw41592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41592Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41592step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41592step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41592step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41592step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41592step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41592step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41592 raw41592Labels = mixedMoment B node3119 node3119Labels := by
  calc
    mixedMoment B raw41592 raw41592Labels = mixedMoment B raw41592step0 raw41592step0Labels := by
      have hz : ∀ j, raw41592 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41592step0 = (fun i j => raw41592 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41592step0 raw41592; decide +kernel
      have hl : raw41592step0Labels = raw41592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41592 raw41592Labels permutation346 hz
    mixedMoment B raw41592step0 raw41592step0Labels = mixedMoment B raw41592step1 raw41592step1Labels := by
      have hz : ∀ j, raw41592step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41592step1 = (fun i j => raw41592step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41592step1 raw41592step0; decide +kernel
      have hl : raw41592step1Labels = raw41592step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41592step0 raw41592step0Labels permutation56 hz
    mixedMoment B raw41592step1 raw41592step1Labels = mixedMoment B raw41592step2 raw41592step2Labels := by
      have ha : raw41592step2 = (fun i j => raw41592step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41592step2 raw41592step1; decide +kernel
      have hl : raw41592step2Labels = raw41592step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41592step1 raw41592step1Labels permutation13 permutation2
    mixedMoment B raw41592step2 raw41592step2Labels = mixedMoment B raw41592step3 raw41592step3Labels := by
      have ha : raw41592step3 = raw41592step2 := by apply Matrix.ext; unfold raw41592step3 raw41592step2; decide +kernel
      have hl : raw41592step2Labels = labelEmbedding1 ∘ raw41592step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41592step2 raw41592step2Labels raw41592step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3119 node3119Labels := by rfl

def raw41593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41593Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41593step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41593step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw41593step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41593step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41593step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41593step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41593step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41593 raw41593Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw41593 raw41593Labels = mixedMoment B raw41593step0 raw41593step0Labels := by
      have hz : ∀ j, raw41593 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41593step0 = (fun i j => raw41593 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41593step0 raw41593; decide +kernel
      have hl : raw41593step0Labels = raw41593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41593 raw41593Labels permutation346 hz
    mixedMoment B raw41593step0 raw41593step0Labels = mixedMoment B raw41593step1 raw41593step1Labels := by
      have hz : ∀ j, raw41593step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw41593step1 = (fun i j => raw41593step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw41593step1 raw41593step0; decide +kernel
      have hl : raw41593step1Labels = raw41593step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41593step0 raw41593step0Labels permutation56 hz
    mixedMoment B raw41593step1 raw41593step1Labels = mixedMoment B raw41593step2 raw41593step2Labels := by
      have ha : raw41593step2 = (fun i j => raw41593step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41593step2 raw41593step1; decide +kernel
      have hl : raw41593step2Labels = raw41593step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41593step1 raw41593step1Labels permutation8 permutation3
    mixedMoment B raw41593step2 raw41593step2Labels = mixedMoment B raw41593step3 raw41593step3Labels := by
      have ha : raw41593step3 = raw41593step2 := by apply Matrix.ext; unfold raw41593step3 raw41593step2; decide +kernel
      have hl : raw41593step2Labels = labelEmbedding7 ∘ raw41593step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41593step2 raw41593step2Labels raw41593step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw41594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41594Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41594step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41594step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41594 raw41594Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw41594 raw41594Labels = mixedMoment B raw41594step0 raw41594step0Labels := by
      have hz : ∀ j, raw41594 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41594step0 = (fun i j => raw41594 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41594step0 raw41594; decide +kernel
      have hl : raw41594step0Labels = raw41594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41594 raw41594Labels permutation265 hz
    mixedMoment B raw41594step0 raw41594step0Labels = mixedMoment B raw41594step1 raw41594step1Labels := by
      have ha : raw41594step1 = raw41594step0 := by apply Matrix.ext; unfold raw41594step1 raw41594step0; decide +kernel
      have hl : raw41594step0Labels = labelEmbedding1 ∘ raw41594step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41594step0 raw41594step0Labels raw41594step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw41595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41595Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw41595step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41595step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw41595step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw41595step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41595 raw41595Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw41595 raw41595Labels = mixedMoment B raw41595step0 raw41595step0Labels := by
      have hz : ∀ j, raw41595 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41595step0 = (fun i j => raw41595 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41595step0 raw41595; decide +kernel
      have hl : raw41595step0Labels = raw41595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41595 raw41595Labels permutation265 hz
    mixedMoment B raw41595step0 raw41595step0Labels = mixedMoment B raw41595step1 raw41595step1Labels := by
      have ha : raw41595step1 = (fun i j => raw41595step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw41595step1 raw41595step0; decide +kernel
      have hl : raw41595step1Labels = raw41595step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41595step0 raw41595step0Labels permutation149 permutation7
    mixedMoment B raw41595step1 raw41595step1Labels = mixedMoment B raw41595step2 raw41595step2Labels := by
      have ha : raw41595step2 = raw41595step1 := by apply Matrix.ext; unfold raw41595step2 raw41595step1; decide +kernel
      have hl : raw41595step1Labels = labelEmbedding6 ∘ raw41595step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41595step1 raw41595step1Labels raw41595step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw41596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41596Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41596step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41596step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41596step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw41596step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41596 raw41596Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw41596 raw41596Labels = mixedMoment B raw41596step0 raw41596step0Labels := by
      have hz : ∀ j, raw41596 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41596step0 = (fun i j => raw41596 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41596step0 raw41596; decide +kernel
      have hl : raw41596step0Labels = raw41596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41596 raw41596Labels permutation265 hz
    mixedMoment B raw41596step0 raw41596step0Labels = mixedMoment B raw41596step1 raw41596step1Labels := by
      have ha : raw41596step1 = (fun i j => raw41596step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41596step1 raw41596step0; decide +kernel
      have hl : raw41596step1Labels = raw41596step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41596step0 raw41596step0Labels permutation37 permutation2
    mixedMoment B raw41596step1 raw41596step1Labels = mixedMoment B raw41596step2 raw41596step2Labels := by
      have ha : raw41596step2 = raw41596step1 := by apply Matrix.ext; unfold raw41596step2 raw41596step1; decide +kernel
      have hl : raw41596step1Labels = labelEmbedding1 ∘ raw41596step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41596step1 raw41596step1Labels raw41596step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw41597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41597Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw41597step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41597step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41597step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw41597step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41597 raw41597Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw41597 raw41597Labels = mixedMoment B raw41597step0 raw41597step0Labels := by
      have hz : ∀ j, raw41597 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41597step0 = (fun i j => raw41597 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41597step0 raw41597; decide +kernel
      have hl : raw41597step0Labels = raw41597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41597 raw41597Labels permutation265 hz
    mixedMoment B raw41597step0 raw41597step0Labels = mixedMoment B raw41597step1 raw41597step1Labels := by
      have ha : raw41597step1 = (fun i j => raw41597step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41597step1 raw41597step0; decide +kernel
      have hl : raw41597step1Labels = raw41597step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41597step0 raw41597step0Labels permutation32 permutation3
    mixedMoment B raw41597step1 raw41597step1Labels = mixedMoment B raw41597step2 raw41597step2Labels := by
      have ha : raw41597step2 = raw41597step1 := by apply Matrix.ext; unfold raw41597step2 raw41597step1; decide +kernel
      have hl : raw41597step1Labels = labelEmbedding7 ∘ raw41597step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41597step1 raw41597step1Labels raw41597step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw41598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41598Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41598step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41598step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41598step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw41598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41598 raw41598Labels = mixedMoment B node3099 node3099Labels := by
  calc
    mixedMoment B raw41598 raw41598Labels = mixedMoment B raw41598step0 raw41598step0Labels := by
      have hz : ∀ j, raw41598 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41598step0 = (fun i j => raw41598 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41598step0 raw41598; decide +kernel
      have hl : raw41598step0Labels = raw41598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41598 raw41598Labels permutation265 hz
    mixedMoment B raw41598step0 raw41598step0Labels = mixedMoment B raw41598step1 raw41598step1Labels := by
      have ha : raw41598step1 = (fun i j => raw41598step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw41598step1 raw41598step0; decide +kernel
      have hl : raw41598step1Labels = raw41598step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41598step0 raw41598step0Labels permutation35 permutation2
    mixedMoment B raw41598step1 raw41598step1Labels = mixedMoment B raw41598step2 raw41598step2Labels := by
      have ha : raw41598step2 = raw41598step1 := by apply Matrix.ext; unfold raw41598step2 raw41598step1; decide +kernel
      have hl : raw41598step1Labels = labelEmbedding1 ∘ raw41598step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41598step1 raw41598step1Labels raw41598step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3099 node3099Labels := by rfl

def raw41599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41599Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw41599step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41599step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw41599step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw41599step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41599 raw41599Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw41599 raw41599Labels = mixedMoment B raw41599step0 raw41599step0Labels := by
      have hz : ∀ j, raw41599 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw41599step0 = (fun i j => raw41599 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw41599step0 raw41599; decide +kernel
      have hl : raw41599step0Labels = raw41599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41599 raw41599Labels permutation265 hz
    mixedMoment B raw41599step0 raw41599step0Labels = mixedMoment B raw41599step1 raw41599step1Labels := by
      have ha : raw41599step1 = (fun i j => raw41599step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw41599step1 raw41599step0; decide +kernel
      have hl : raw41599step1Labels = raw41599step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41599step0 raw41599step0Labels permutation32 permutation3
    mixedMoment B raw41599step1 raw41599step1Labels = mixedMoment B raw41599step2 raw41599step2Labels := by
      have ha : raw41599step2 = raw41599step1 := by apply Matrix.ext; unfold raw41599step2 raw41599step1; decide +kernel
      have hl : raw41599step1Labels = labelEmbedding7 ∘ raw41599step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41599step1 raw41599step1Labels raw41599step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
