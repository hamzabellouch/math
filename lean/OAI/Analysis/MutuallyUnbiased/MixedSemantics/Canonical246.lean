import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw31488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31488step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1], ![-1, -1, 2]]
def raw31488step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31488step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw31488step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31488 raw31488Labels = mixedMoment B node3108 node3108Labels := by
  calc
    mixedMoment B raw31488 raw31488Labels = mixedMoment B raw31488step0 raw31488step0Labels := by
      have hz : ∀ j, raw31488 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31488step0 = (fun i j => raw31488 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31488step0 raw31488; decide +kernel
      have hl : raw31488step0Labels = raw31488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31488 raw31488Labels permutation434 hz
    mixedMoment B raw31488step0 raw31488step0Labels = mixedMoment B raw31488step1 raw31488step1Labels := by
      have ha : raw31488step1 = (fun i j => raw31488step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31488step1 raw31488step0; decide +kernel
      have hl : raw31488step1Labels = raw31488step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31488step0 raw31488step0Labels permutation35 permutation6
    mixedMoment B raw31488step1 raw31488step1Labels = mixedMoment B raw31488step2 raw31488step2Labels := by
      have ha : raw31488step2 = -raw31488step1 := by apply Matrix.ext; change ∀ i j, raw31488step2 i j = -(raw31488step1 i j); unfold raw31488step2 raw31488step1; decide +kernel
      have hl : raw31488step2Labels = raw31488step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3108 node3108Labels := by rfl

def raw31489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1], ![-1, 0, 1]]
def raw31489step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31489step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw31489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31489 raw31489Labels = mixedMoment B node3104 node3104Labels := by
  calc
    mixedMoment B raw31489 raw31489Labels = mixedMoment B raw31489step0 raw31489step0Labels := by
      have ha : raw31489step0 = (fun i j => raw31489 (permutation161 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31489step0 raw31489; decide +kernel
      have hl : raw31489step0Labels = raw31489Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31489 raw31489Labels permutation161 permutation6
    mixedMoment B raw31489step0 raw31489step0Labels = mixedMoment B raw31489step1 raw31489step1Labels := by
      have ha : raw31489step1 = -raw31489step0 := by apply Matrix.ext; change ∀ i j, raw31489step1 i j = -(raw31489step0 i j); unfold raw31489step1 raw31489step0; decide +kernel
      have hl : raw31489step1Labels = raw31489step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3104 node3104Labels := by rfl

def raw31490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31490step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw31490step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31490step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw31490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31490 raw31490Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw31490 raw31490Labels = mixedMoment B raw31490step0 raw31490step0Labels := by
      have hz : ∀ j, raw31490 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31490step0 = (fun i j => raw31490 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31490step0 raw31490; decide +kernel
      have hl : raw31490step0Labels = raw31490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31490 raw31490Labels permutation434 hz
    mixedMoment B raw31490step0 raw31490step0Labels = mixedMoment B raw31490step1 raw31490step1Labels := by
      have ha : raw31490step1 = (fun i j => raw31490step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31490step1 raw31490step0; decide +kernel
      have hl : raw31490step1Labels = raw31490step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31490step0 raw31490step0Labels permutation37 permutation6
    mixedMoment B raw31490step1 raw31490step1Labels = mixedMoment B raw31490step2 raw31490step2Labels := by
      have ha : raw31490step2 = -raw31490step1 := by apply Matrix.ext; change ∀ i j, raw31490step2 i j = -(raw31490step1 i j); unfold raw31490step2 raw31490step1; decide +kernel
      have hl : raw31490step2Labels = raw31490step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw31491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31491step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw31491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31491step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw31491step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31491 raw31491Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw31491 raw31491Labels = mixedMoment B raw31491step0 raw31491step0Labels := by
      have hz : ∀ j, raw31491 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31491step0 = (fun i j => raw31491 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31491step0 raw31491; decide +kernel
      have hl : raw31491step0Labels = raw31491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31491 raw31491Labels permutation434 hz
    mixedMoment B raw31491step0 raw31491step0Labels = mixedMoment B raw31491step1 raw31491step1Labels := by
      have ha : raw31491step1 = (fun i j => raw31491step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31491step1 raw31491step0; decide +kernel
      have hl : raw31491step1Labels = raw31491step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31491step0 raw31491step0Labels permutation35 permutation6
    mixedMoment B raw31491step1 raw31491step1Labels = mixedMoment B raw31491step2 raw31491step2Labels := by
      have ha : raw31491step2 = -raw31491step1 := by apply Matrix.ext; change ∀ i j, raw31491step2 i j = -(raw31491step1 i j); unfold raw31491step2 raw31491step1; decide +kernel
      have hl : raw31491step2Labels = raw31491step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw31492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31492step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31492step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31492step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31492step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31492step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31492 raw31492Labels = mixedMoment B node1420 node1420Labels := by
  calc
    mixedMoment B raw31492 raw31492Labels = mixedMoment B raw31492step0 raw31492step0Labels := by
      have hz : ∀ j, raw31492 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31492step0 = (fun i j => raw31492 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31492step0 raw31492; decide +kernel
      have hl : raw31492step0Labels = raw31492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31492 raw31492Labels permutation434 hz
    mixedMoment B raw31492step0 raw31492step0Labels = mixedMoment B raw31492step1 raw31492step1Labels := by
      have hz : ∀ j, raw31492step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31492step1 = (fun i j => raw31492step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31492step1 raw31492step0; decide +kernel
      have hl : raw31492step1Labels = raw31492step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31492step0 raw31492step0Labels permutation56 hz
    mixedMoment B raw31492step1 raw31492step1Labels = mixedMoment B raw31492step2 raw31492step2Labels := by
      have ha : raw31492step2 = (fun i j => raw31492step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31492step2 raw31492step1; decide +kernel
      have hl : raw31492step2Labels = raw31492step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31492step1 raw31492step1Labels permutation8 permutation3
    _ = mixedMoment B node1420 node1420Labels := by rfl

def raw31493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31493step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31493step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31493step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31493step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw31493step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31493 raw31493Labels = mixedMoment B node3188 node3188Labels := by
  calc
    mixedMoment B raw31493 raw31493Labels = mixedMoment B raw31493step0 raw31493step0Labels := by
      have hz : ∀ j, raw31493 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31493step0 = (fun i j => raw31493 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31493step0 raw31493; decide +kernel
      have hl : raw31493step0Labels = raw31493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31493 raw31493Labels permutation434 hz
    mixedMoment B raw31493step0 raw31493step0Labels = mixedMoment B raw31493step1 raw31493step1Labels := by
      have hz : ∀ j, raw31493step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31493step1 = (fun i j => raw31493step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31493step1 raw31493step0; decide +kernel
      have hl : raw31493step1Labels = raw31493step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31493step0 raw31493step0Labels permutation56 hz
    mixedMoment B raw31493step1 raw31493step1Labels = mixedMoment B raw31493step2 raw31493step2Labels := by
      have ha : raw31493step2 = (fun i j => raw31493step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31493step2 raw31493step1; decide +kernel
      have hl : raw31493step2Labels = raw31493step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31493step1 raw31493step1Labels permutation8 permutation3
    _ = mixedMoment B node3188 node3188Labels := by rfl

def raw31494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31494step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31494 raw31494Labels = mixedMoment B node3207 node3207Labels := by
  calc
    mixedMoment B raw31494 raw31494Labels = mixedMoment B raw31494step0 raw31494step0Labels := by
      have hz : ∀ j, raw31494 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw31494step0 = (fun i j => raw31494 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw31494step0 raw31494; decide +kernel
      have hl : raw31494step0Labels = raw31494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31494 raw31494Labels permutation265 hz
    mixedMoment B raw31494step0 raw31494step0Labels = mixedMoment B raw31494step1 raw31494step1Labels := by
      have ha : raw31494step1 = (fun i j => raw31494step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31494step1 raw31494step0; decide +kernel
      have hl : raw31494step1Labels = raw31494step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31494step0 raw31494step0Labels permutation38 permutation3
    _ = mixedMoment B node3207 node3207Labels := by rfl

def raw31495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31495step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31495step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31495step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31495step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw31495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31495 raw31495Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw31495 raw31495Labels = mixedMoment B raw31495step0 raw31495step0Labels := by
      have hz : ∀ j, raw31495 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31495step0 = (fun i j => raw31495 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31495step0 raw31495; decide +kernel
      have hl : raw31495step0Labels = raw31495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31495 raw31495Labels permutation434 hz
    mixedMoment B raw31495step0 raw31495step0Labels = mixedMoment B raw31495step1 raw31495step1Labels := by
      have hz : ∀ j, raw31495step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31495step1 = (fun i j => raw31495step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31495step1 raw31495step0; decide +kernel
      have hl : raw31495step1Labels = raw31495step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31495step0 raw31495step0Labels permutation56 hz
    mixedMoment B raw31495step1 raw31495step1Labels = mixedMoment B raw31495step2 raw31495step2Labels := by
      have ha : raw31495step2 = (fun i j => raw31495step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31495step2 raw31495step1; decide +kernel
      have hl : raw31495step2Labels = raw31495step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31495step1 raw31495step1Labels permutation8 permutation3
    _ = mixedMoment B node3229 node3229Labels := by rfl

def raw31496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31496step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31496step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31496step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31496step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw31496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31496 raw31496Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw31496 raw31496Labels = mixedMoment B raw31496step0 raw31496step0Labels := by
      have hz : ∀ j, raw31496 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31496step0 = (fun i j => raw31496 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31496step0 raw31496; decide +kernel
      have hl : raw31496step0Labels = raw31496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31496 raw31496Labels permutation434 hz
    mixedMoment B raw31496step0 raw31496step0Labels = mixedMoment B raw31496step1 raw31496step1Labels := by
      have hz : ∀ j, raw31496step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31496step1 = (fun i j => raw31496step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31496step1 raw31496step0; decide +kernel
      have hl : raw31496step1Labels = raw31496step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31496step0 raw31496step0Labels permutation56 hz
    mixedMoment B raw31496step1 raw31496step1Labels = mixedMoment B raw31496step2 raw31496step2Labels := by
      have ha : raw31496step2 = (fun i j => raw31496step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31496step2 raw31496step1; decide +kernel
      have hl : raw31496step2Labels = raw31496step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31496step1 raw31496step1Labels permutation9 permutation3
    _ = mixedMoment B node3229 node3229Labels := by rfl

def raw31497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31497step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31497 raw31497Labels = mixedMoment B node1344 node1344Labels := by
  calc
    mixedMoment B raw31497 raw31497Labels = mixedMoment B raw31497step0 raw31497step0Labels := by
      have hz : ∀ j, raw31497 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31497step0 = (fun i j => raw31497 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31497step0 raw31497; decide +kernel
      have hl : raw31497step0Labels = raw31497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31497 raw31497Labels permutation434 hz
    mixedMoment B raw31497step0 raw31497step0Labels = mixedMoment B raw31497step1 raw31497step1Labels := by
      have ha : raw31497step1 = (fun i j => raw31497step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31497step1 raw31497step0; decide +kernel
      have hl : raw31497step1Labels = raw31497step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31497step0 raw31497step0Labels permutation32 permutation3
    _ = mixedMoment B node1344 node1344Labels := by rfl

def raw31498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31498step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31498 raw31498Labels = mixedMoment B node3142 node3142Labels := by
  calc
    mixedMoment B raw31498 raw31498Labels = mixedMoment B raw31498step0 raw31498step0Labels := by
      have hz : ∀ j, raw31498 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31498step0 = (fun i j => raw31498 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31498step0 raw31498; decide +kernel
      have hl : raw31498step0Labels = raw31498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31498 raw31498Labels permutation434 hz
    mixedMoment B raw31498step0 raw31498step0Labels = mixedMoment B raw31498step1 raw31498step1Labels := by
      have ha : raw31498step1 = (fun i j => raw31498step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31498step1 raw31498step0; decide +kernel
      have hl : raw31498step1Labels = raw31498step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31498step0 raw31498step0Labels permutation32 permutation3
    _ = mixedMoment B node3142 node3142Labels := by rfl

def raw31499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31499 raw31499Labels = mixedMoment B node3191 node3191Labels := by
  calc
    mixedMoment B raw31499 raw31499Labels = mixedMoment B raw31499step0 raw31499step0Labels := by
      have ha : raw31499step0 = (fun i j => raw31499 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31499step0 raw31499; decide +kernel
      have hl : raw31499step0Labels = raw31499Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31499 raw31499Labels permutation158 permutation3
    _ = mixedMoment B node3191 node3191Labels := by rfl

def raw31500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw31500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31500 raw31500Labels = mixedMoment B node3213 node3213Labels := by
  calc
    mixedMoment B raw31500 raw31500Labels = mixedMoment B raw31500step0 raw31500step0Labels := by
      have hz : ∀ j, raw31500 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31500step0 = (fun i j => raw31500 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31500step0 raw31500; decide +kernel
      have hl : raw31500step0Labels = raw31500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31500 raw31500Labels permutation434 hz
    mixedMoment B raw31500step0 raw31500step0Labels = mixedMoment B raw31500step1 raw31500step1Labels := by
      have ha : raw31500step1 = (fun i j => raw31500step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31500step1 raw31500step0; decide +kernel
      have hl : raw31500step1Labels = raw31500step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31500step0 raw31500step0Labels permutation32 permutation3
    _ = mixedMoment B node3213 node3213Labels := by rfl

def raw31501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31501step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw31501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31501 raw31501Labels = mixedMoment B node3213 node3213Labels := by
  calc
    mixedMoment B raw31501 raw31501Labels = mixedMoment B raw31501step0 raw31501step0Labels := by
      have hz : ∀ j, raw31501 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31501step0 = (fun i j => raw31501 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31501step0 raw31501; decide +kernel
      have hl : raw31501step0Labels = raw31501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31501 raw31501Labels permutation434 hz
    mixedMoment B raw31501step0 raw31501step0Labels = mixedMoment B raw31501step1 raw31501step1Labels := by
      have ha : raw31501step1 = (fun i j => raw31501step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31501step1 raw31501step0; decide +kernel
      have hl : raw31501step1Labels = raw31501step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31501step0 raw31501step0Labels permutation33 permutation3
    _ = mixedMoment B node3213 node3213Labels := by rfl

def raw31502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31502 raw31502Labels = mixedMoment B node1331 node1331Labels := by
  calc
    mixedMoment B raw31502 raw31502Labels = mixedMoment B raw31502step0 raw31502step0Labels := by
      have ha : raw31502step0 = (fun i j => raw31502 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31502step0 raw31502; decide +kernel
      have hl : raw31502step0Labels = raw31502Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31502 raw31502Labels permutation152 permutation3
    _ = mixedMoment B node1331 node1331Labels := by rfl

def raw31503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31503 raw31503Labels = mixedMoment B node3135 node3135Labels := by
  calc
    mixedMoment B raw31503 raw31503Labels = mixedMoment B raw31503step0 raw31503step0Labels := by
      have ha : raw31503step0 = (fun i j => raw31503 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31503step0 raw31503; decide +kernel
      have hl : raw31503step0Labels = raw31503Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31503 raw31503Labels permutation152 permutation3
    _ = mixedMoment B node3135 node3135Labels := by rfl

def raw31504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31504 raw31504Labels = mixedMoment B node3164 node3164Labels := by
  calc
    mixedMoment B raw31504 raw31504Labels = mixedMoment B raw31504step0 raw31504step0Labels := by
      have ha : raw31504step0 = (fun i j => raw31504 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31504step0 raw31504; decide +kernel
      have hl : raw31504step0Labels = raw31504Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31504 raw31504Labels permutation176 permutation3
    _ = mixedMoment B node3164 node3164Labels := by rfl

def raw31505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31505 raw31505Labels = mixedMoment B node3204 node3204Labels := by
  calc
    mixedMoment B raw31505 raw31505Labels = mixedMoment B raw31505step0 raw31505step0Labels := by
      have ha : raw31505step0 = (fun i j => raw31505 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31505step0 raw31505; decide +kernel
      have hl : raw31505step0Labels = raw31505Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31505 raw31505Labels permutation154 permutation3
    _ = mixedMoment B node3204 node3204Labels := by rfl

def raw31506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31506 raw31506Labels = mixedMoment B node3204 node3204Labels := by
  calc
    mixedMoment B raw31506 raw31506Labels = mixedMoment B raw31506step0 raw31506step0Labels := by
      have ha : raw31506step0 = (fun i j => raw31506 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31506step0 raw31506; decide +kernel
      have hl : raw31506step0Labels = raw31506Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31506 raw31506Labels permutation156 permutation3
    _ = mixedMoment B node3204 node3204Labels := by rfl

def raw31507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31507step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw31507step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31507 raw31507Labels = mixedMoment B node1333 node1333Labels := by
  calc
    mixedMoment B raw31507 raw31507Labels = mixedMoment B raw31507step0 raw31507step0Labels := by
      have hz : ∀ j, raw31507 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31507step0 = (fun i j => raw31507 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31507step0 raw31507; decide +kernel
      have hl : raw31507step0Labels = raw31507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31507 raw31507Labels permutation434 hz
    mixedMoment B raw31507step0 raw31507step0Labels = mixedMoment B raw31507step1 raw31507step1Labels := by
      have ha : raw31507step1 = (fun i j => raw31507step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31507step1 raw31507step0; decide +kernel
      have hl : raw31507step1Labels = raw31507step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31507step0 raw31507step0Labels permutation33 permutation3
    _ = mixedMoment B node1333 node1333Labels := by rfl

def raw31508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31508step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw31508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31508step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31508 raw31508Labels = mixedMoment B node2327 node2327Labels := by
  calc
    mixedMoment B raw31508 raw31508Labels = mixedMoment B raw31508step0 raw31508step0Labels := by
      have hz : ∀ j, raw31508 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31508step0 = (fun i j => raw31508 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31508step0 raw31508; decide +kernel
      have hl : raw31508step0Labels = raw31508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31508 raw31508Labels permutation434 hz
    mixedMoment B raw31508step0 raw31508step0Labels = mixedMoment B raw31508step1 raw31508step1Labels := by
      have ha : raw31508step1 = (fun i j => raw31508step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31508step1 raw31508step0; decide +kernel
      have hl : raw31508step1Labels = raw31508step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31508step0 raw31508step0Labels permutation127 permutation3
    mixedMoment B raw31508step1 raw31508step1Labels = mixedMoment B raw31508step2 raw31508step2Labels := by
      have ha : raw31508step2 = -raw31508step1 := by apply Matrix.ext; change ∀ i j, raw31508step2 i j = -(raw31508step1 i j); unfold raw31508step2 raw31508step1; decide +kernel
      have hl : raw31508step2Labels = raw31508step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2327 node2327Labels := by rfl

def raw31509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31509step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw31509step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31509step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31509step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31509 raw31509Labels = mixedMoment B node2340 node2340Labels := by
  calc
    mixedMoment B raw31509 raw31509Labels = mixedMoment B raw31509step0 raw31509step0Labels := by
      have hz : ∀ j, raw31509 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31509step0 = (fun i j => raw31509 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31509step0 raw31509; decide +kernel
      have hl : raw31509step0Labels = raw31509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31509 raw31509Labels permutation434 hz
    mixedMoment B raw31509step0 raw31509step0Labels = mixedMoment B raw31509step1 raw31509step1Labels := by
      have ha : raw31509step1 = (fun i j => raw31509step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31509step1 raw31509step0; decide +kernel
      have hl : raw31509step1Labels = raw31509step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31509step0 raw31509step0Labels permutation125 permutation3
    mixedMoment B raw31509step1 raw31509step1Labels = mixedMoment B raw31509step2 raw31509step2Labels := by
      have ha : raw31509step2 = -raw31509step1 := by apply Matrix.ext; change ∀ i j, raw31509step2 i j = -(raw31509step1 i j); unfold raw31509step2 raw31509step1; decide +kernel
      have hl : raw31509step2Labels = raw31509step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2340 node2340Labels := by rfl

def raw31510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31510Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31510step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31510step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31510step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31510 raw31510Labels = mixedMoment B node2323 node2323Labels := by
  calc
    mixedMoment B raw31510 raw31510Labels = mixedMoment B raw31510step0 raw31510step0Labels := by
      have ha : raw31510step0 = (fun i j => raw31510 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31510step0 raw31510; decide +kernel
      have hl : raw31510step0Labels = raw31510Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31510 raw31510Labels permutation582 permutation3
    mixedMoment B raw31510step0 raw31510step0Labels = mixedMoment B raw31510step1 raw31510step1Labels := by
      have ha : raw31510step1 = -raw31510step0 := by apply Matrix.ext; change ∀ i j, raw31510step1 i j = -(raw31510step0 i j); unfold raw31510step1 raw31510step0; decide +kernel
      have hl : raw31510step1Labels = raw31510step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2323 node2323Labels := by rfl

def raw31511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31511Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1], ![1, 0, -1]]
def raw31511step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31511step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31511step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31511 raw31511Labels = mixedMoment B node2574 node2574Labels := by
  calc
    mixedMoment B raw31511 raw31511Labels = mixedMoment B raw31511step0 raw31511step0Labels := by
      have hz : ∀ j, raw31511 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31511step0 = (fun i j => raw31511 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31511step0 raw31511; decide +kernel
      have hl : raw31511step0Labels = raw31511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31511 raw31511Labels permutation434 hz
    mixedMoment B raw31511step0 raw31511step0Labels = mixedMoment B raw31511step1 raw31511step1Labels := by
      have ha : raw31511step1 = (fun i j => raw31511step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31511step1 raw31511step0; decide +kernel
      have hl : raw31511step1Labels = raw31511step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31511step0 raw31511step0Labels permutation127 permutation3
    mixedMoment B raw31511step1 raw31511step1Labels = mixedMoment B raw31511step2 raw31511step2Labels := by
      have ha : raw31511step2 = -raw31511step1 := by apply Matrix.ext; change ∀ i j, raw31511step2 i j = -(raw31511step1 i j); unfold raw31511step2 raw31511step1; decide +kernel
      have hl : raw31511step2Labels = raw31511step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2574 node2574Labels := by rfl

def raw31512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31512Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31512step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31512step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw31512step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31512 raw31512Labels = mixedMoment B node1333 node1333Labels := by
  calc
    mixedMoment B raw31512 raw31512Labels = mixedMoment B raw31512step0 raw31512step0Labels := by
      have hz : ∀ j, raw31512 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31512step0 = (fun i j => raw31512 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31512step0 raw31512; decide +kernel
      have hl : raw31512step0Labels = raw31512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31512 raw31512Labels permutation434 hz
    mixedMoment B raw31512step0 raw31512step0Labels = mixedMoment B raw31512step1 raw31512step1Labels := by
      have ha : raw31512step1 = (fun i j => raw31512step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31512step1 raw31512step0; decide +kernel
      have hl : raw31512step1Labels = raw31512step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31512step0 raw31512step0Labels permutation32 permutation3
    _ = mixedMoment B node1333 node1333Labels := by rfl

def raw31513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31513Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31513step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw31513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31513step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31513step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31513 raw31513Labels = mixedMoment B node2327 node2327Labels := by
  calc
    mixedMoment B raw31513 raw31513Labels = mixedMoment B raw31513step0 raw31513step0Labels := by
      have hz : ∀ j, raw31513 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31513step0 = (fun i j => raw31513 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31513step0 raw31513; decide +kernel
      have hl : raw31513step0Labels = raw31513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31513 raw31513Labels permutation434 hz
    mixedMoment B raw31513step0 raw31513step0Labels = mixedMoment B raw31513step1 raw31513step1Labels := by
      have ha : raw31513step1 = (fun i j => raw31513step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31513step1 raw31513step0; decide +kernel
      have hl : raw31513step1Labels = raw31513step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31513step0 raw31513step0Labels permutation151 permutation3
    mixedMoment B raw31513step1 raw31513step1Labels = mixedMoment B raw31513step2 raw31513step2Labels := by
      have ha : raw31513step2 = -raw31513step1 := by apply Matrix.ext; change ∀ i j, raw31513step2 i j = -(raw31513step1 i j); unfold raw31513step2 raw31513step1; decide +kernel
      have hl : raw31513step2Labels = raw31513step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2327 node2327Labels := by rfl

def raw31514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31514Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31514step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw31514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31514step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31514step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31514 raw31514Labels = mixedMoment B node2340 node2340Labels := by
  calc
    mixedMoment B raw31514 raw31514Labels = mixedMoment B raw31514step0 raw31514step0Labels := by
      have hz : ∀ j, raw31514 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31514step0 = (fun i j => raw31514 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31514step0 raw31514; decide +kernel
      have hl : raw31514step0Labels = raw31514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31514 raw31514Labels permutation434 hz
    mixedMoment B raw31514step0 raw31514step0Labels = mixedMoment B raw31514step1 raw31514step1Labels := by
      have ha : raw31514step1 = (fun i j => raw31514step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31514step1 raw31514step0; decide +kernel
      have hl : raw31514step1Labels = raw31514step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31514step0 raw31514step0Labels permutation149 permutation3
    mixedMoment B raw31514step1 raw31514step1Labels = mixedMoment B raw31514step2 raw31514step2Labels := by
      have ha : raw31514step2 = -raw31514step1 := by apply Matrix.ext; change ∀ i j, raw31514step2 i j = -(raw31514step1 i j); unfold raw31514step2 raw31514step1; decide +kernel
      have hl : raw31514step2Labels = raw31514step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2340 node2340Labels := by rfl

def raw31515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31515Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31515step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31515step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31515 raw31515Labels = mixedMoment B node2323 node2323Labels := by
  calc
    mixedMoment B raw31515 raw31515Labels = mixedMoment B raw31515step0 raw31515step0Labels := by
      have ha : raw31515step0 = (fun i j => raw31515 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31515step0 raw31515; decide +kernel
      have hl : raw31515step0Labels = raw31515Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31515 raw31515Labels permutation680 permutation3
    mixedMoment B raw31515step0 raw31515step0Labels = mixedMoment B raw31515step1 raw31515step1Labels := by
      have ha : raw31515step1 = -raw31515step0 := by apply Matrix.ext; change ∀ i j, raw31515step1 i j = -(raw31515step0 i j); unfold raw31515step1 raw31515step0; decide +kernel
      have hl : raw31515step1Labels = raw31515step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2323 node2323Labels := by rfl

def raw31516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw31516Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw31516step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31516step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31516step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31516 raw31516Labels = mixedMoment B node2574 node2574Labels := by
  calc
    mixedMoment B raw31516 raw31516Labels = mixedMoment B raw31516step0 raw31516step0Labels := by
      have hz : ∀ j, raw31516 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31516step0 = (fun i j => raw31516 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31516step0 raw31516; decide +kernel
      have hl : raw31516step0Labels = raw31516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31516 raw31516Labels permutation434 hz
    mixedMoment B raw31516step0 raw31516step0Labels = mixedMoment B raw31516step1 raw31516step1Labels := by
      have ha : raw31516step1 = (fun i j => raw31516step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31516step1 raw31516step0; decide +kernel
      have hl : raw31516step1Labels = raw31516step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31516step0 raw31516step0Labels permutation151 permutation3
    mixedMoment B raw31516step1 raw31516step1Labels = mixedMoment B raw31516step2 raw31516step2Labels := by
      have ha : raw31516step2 = -raw31516step1 := by apply Matrix.ext; change ∀ i j, raw31516step2 i j = -(raw31516step1 i j); unfold raw31516step2 raw31516step1; decide +kernel
      have hl : raw31516step2Labels = raw31516step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2574 node2574Labels := by rfl

def raw31517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31517Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31517step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31517step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31517step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31517step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31517step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31517 raw31517Labels = mixedMoment B node2682 node2682Labels := by
  calc
    mixedMoment B raw31517 raw31517Labels = mixedMoment B raw31517step0 raw31517step0Labels := by
      have hz : ∀ j, raw31517 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31517step0 = (fun i j => raw31517 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31517step0 raw31517; decide +kernel
      have hl : raw31517step0Labels = raw31517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31517 raw31517Labels permutation434 hz
    mixedMoment B raw31517step0 raw31517step0Labels = mixedMoment B raw31517step1 raw31517step1Labels := by
      have ha : raw31517step1 = (fun i j => raw31517step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31517step1 raw31517step0; decide +kernel
      have hl : raw31517step1Labels = raw31517step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31517step0 raw31517step0Labels permutation32 permutation7
    mixedMoment B raw31517step1 raw31517step1Labels = mixedMoment B raw31517step2 raw31517step2Labels := by
      have ha : raw31517step2 = -raw31517step1 := by apply Matrix.ext; change ∀ i j, raw31517step2 i j = -(raw31517step1 i j); unfold raw31517step2 raw31517step1; decide +kernel
      have hl : raw31517step2Labels = raw31517step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31517step2 raw31517step2Labels = mixedMoment B raw31517step3 raw31517step3Labels := by
      have ha : raw31517step3 = raw31517step2 := by apply Matrix.ext; unfold raw31517step3 raw31517step2; decide +kernel
      have hl : raw31517step2Labels = labelEmbedding1 ∘ raw31517step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31517step2 raw31517step2Labels raw31517step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2682 node2682Labels := by rfl

def raw31518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31518Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31518step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31518step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31518step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31518step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31518step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31518step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31518 raw31518Labels = mixedMoment B node2736 node2736Labels := by
  calc
    mixedMoment B raw31518 raw31518Labels = mixedMoment B raw31518step0 raw31518step0Labels := by
      have hz : ∀ j, raw31518 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31518step0 = (fun i j => raw31518 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31518step0 raw31518; decide +kernel
      have hl : raw31518step0Labels = raw31518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31518 raw31518Labels permutation434 hz
    mixedMoment B raw31518step0 raw31518step0Labels = mixedMoment B raw31518step1 raw31518step1Labels := by
      have ha : raw31518step1 = (fun i j => raw31518step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31518step1 raw31518step0; decide +kernel
      have hl : raw31518step1Labels = raw31518step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31518step0 raw31518step0Labels permutation32 permutation7
    mixedMoment B raw31518step1 raw31518step1Labels = mixedMoment B raw31518step2 raw31518step2Labels := by
      have ha : raw31518step2 = -raw31518step1 := by apply Matrix.ext; change ∀ i j, raw31518step2 i j = -(raw31518step1 i j); unfold raw31518step2 raw31518step1; decide +kernel
      have hl : raw31518step2Labels = raw31518step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31518step2 raw31518step2Labels = mixedMoment B raw31518step3 raw31518step3Labels := by
      have ha : raw31518step3 = raw31518step2 := by apply Matrix.ext; unfold raw31518step3 raw31518step2; decide +kernel
      have hl : raw31518step2Labels = labelEmbedding1 ∘ raw31518step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31518step2 raw31518step2Labels raw31518step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2736 node2736Labels := by rfl

def raw31519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31519Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31519step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31519step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31519step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31519step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31519step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31519 raw31519Labels = mixedMoment B node2701 node2701Labels := by
  calc
    mixedMoment B raw31519 raw31519Labels = mixedMoment B raw31519step0 raw31519step0Labels := by
      have ha : raw31519step0 = (fun i j => raw31519 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31519step0 raw31519; decide +kernel
      have hl : raw31519step0Labels = raw31519Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31519 raw31519Labels permutation158 permutation7
    mixedMoment B raw31519step0 raw31519step0Labels = mixedMoment B raw31519step1 raw31519step1Labels := by
      have ha : raw31519step1 = -raw31519step0 := by apply Matrix.ext; change ∀ i j, raw31519step1 i j = -(raw31519step0 i j); unfold raw31519step1 raw31519step0; decide +kernel
      have hl : raw31519step1Labels = raw31519step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31519step1 raw31519step1Labels = mixedMoment B raw31519step2 raw31519step2Labels := by
      have ha : raw31519step2 = raw31519step1 := by apply Matrix.ext; unfold raw31519step2 raw31519step1; decide +kernel
      have hl : raw31519step1Labels = labelEmbedding1 ∘ raw31519step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31519step1 raw31519step1Labels raw31519step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2701 node2701Labels := by rfl

def raw31520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31520Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31520step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw31520step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31520step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31520step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31520step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31520step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31520 raw31520Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw31520 raw31520Labels = mixedMoment B raw31520step0 raw31520step0Labels := by
      have hz : ∀ j, raw31520 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31520step0 = (fun i j => raw31520 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31520step0 raw31520; decide +kernel
      have hl : raw31520step0Labels = raw31520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31520 raw31520Labels permutation434 hz
    mixedMoment B raw31520step0 raw31520step0Labels = mixedMoment B raw31520step1 raw31520step1Labels := by
      have ha : raw31520step1 = (fun i j => raw31520step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31520step1 raw31520step0; decide +kernel
      have hl : raw31520step1Labels = raw31520step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31520step0 raw31520step0Labels permutation32 permutation7
    mixedMoment B raw31520step1 raw31520step1Labels = mixedMoment B raw31520step2 raw31520step2Labels := by
      have ha : raw31520step2 = -raw31520step1 := by apply Matrix.ext; change ∀ i j, raw31520step2 i j = -(raw31520step1 i j); unfold raw31520step2 raw31520step1; decide +kernel
      have hl : raw31520step2Labels = raw31520step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31520step2 raw31520step2Labels = mixedMoment B raw31520step3 raw31520step3Labels := by
      have ha : raw31520step3 = raw31520step2 := by apply Matrix.ext; unfold raw31520step3 raw31520step2; decide +kernel
      have hl : raw31520step2Labels = labelEmbedding1 ∘ raw31520step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31520step2 raw31520step2Labels raw31520step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw31521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31521Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31521step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw31521step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31521step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31521step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31521step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31521step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31521 raw31521Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw31521 raw31521Labels = mixedMoment B raw31521step0 raw31521step0Labels := by
      have hz : ∀ j, raw31521 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31521step0 = (fun i j => raw31521 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31521step0 raw31521; decide +kernel
      have hl : raw31521step0Labels = raw31521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31521 raw31521Labels permutation434 hz
    mixedMoment B raw31521step0 raw31521step0Labels = mixedMoment B raw31521step1 raw31521step1Labels := by
      have ha : raw31521step1 = (fun i j => raw31521step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31521step1 raw31521step0; decide +kernel
      have hl : raw31521step1Labels = raw31521step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31521step0 raw31521step0Labels permutation33 permutation7
    mixedMoment B raw31521step1 raw31521step1Labels = mixedMoment B raw31521step2 raw31521step2Labels := by
      have ha : raw31521step2 = -raw31521step1 := by apply Matrix.ext; change ∀ i j, raw31521step2 i j = -(raw31521step1 i j); unfold raw31521step2 raw31521step1; decide +kernel
      have hl : raw31521step2Labels = raw31521step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31521step2 raw31521step2Labels = mixedMoment B raw31521step3 raw31521step3Labels := by
      have ha : raw31521step3 = raw31521step2 := by apply Matrix.ext; unfold raw31521step3 raw31521step2; decide +kernel
      have hl : raw31521step2Labels = labelEmbedding1 ∘ raw31521step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31521step2 raw31521step2Labels raw31521step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw31522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31522Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31522step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31522step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31522step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31522step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31522step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31522step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31522step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31522step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31522 raw31522Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw31522 raw31522Labels = mixedMoment B raw31522step0 raw31522step0Labels := by
      have hz : ∀ j, raw31522 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31522step0 = (fun i j => raw31522 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31522step0 raw31522; decide +kernel
      have hl : raw31522step0Labels = raw31522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31522 raw31522Labels permutation434 hz
    mixedMoment B raw31522step0 raw31522step0Labels = mixedMoment B raw31522step1 raw31522step1Labels := by
      have hz : ∀ j, raw31522step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31522step1 = (fun i j => raw31522step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31522step1 raw31522step0; decide +kernel
      have hl : raw31522step1Labels = raw31522step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31522step0 raw31522step0Labels permutation56 hz
    mixedMoment B raw31522step1 raw31522step1Labels = mixedMoment B raw31522step2 raw31522step2Labels := by
      have ha : raw31522step2 = (fun i j => raw31522step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31522step2 raw31522step1; decide +kernel
      have hl : raw31522step2Labels = raw31522step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31522step1 raw31522step1Labels permutation8 permutation7
    mixedMoment B raw31522step2 raw31522step2Labels = mixedMoment B raw31522step3 raw31522step3Labels := by
      have ha : raw31522step3 = -raw31522step2 := by apply Matrix.ext; change ∀ i j, raw31522step3 i j = -(raw31522step2 i j); unfold raw31522step3 raw31522step2; decide +kernel
      have hl : raw31522step3Labels = raw31522step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31522step3 raw31522step3Labels = mixedMoment B raw31522step4 raw31522step4Labels := by
      have ha : raw31522step4 = raw31522step3 := by apply Matrix.ext; unfold raw31522step4 raw31522step3; decide +kernel
      have hl : raw31522step3Labels = labelEmbedding1 ∘ raw31522step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31522step3 raw31522step3Labels raw31522step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1751 node1751Labels := by rfl

def raw31523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31523Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31523step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31523step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31523step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31523step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31523step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31523step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31523step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31523step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31523 raw31523Labels = mixedMoment B node2288 node2288Labels := by
  calc
    mixedMoment B raw31523 raw31523Labels = mixedMoment B raw31523step0 raw31523step0Labels := by
      have hz : ∀ j, raw31523 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31523step0 = (fun i j => raw31523 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31523step0 raw31523; decide +kernel
      have hl : raw31523step0Labels = raw31523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31523 raw31523Labels permutation434 hz
    mixedMoment B raw31523step0 raw31523step0Labels = mixedMoment B raw31523step1 raw31523step1Labels := by
      have hz : ∀ j, raw31523step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31523step1 = (fun i j => raw31523step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31523step1 raw31523step0; decide +kernel
      have hl : raw31523step1Labels = raw31523step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31523step0 raw31523step0Labels permutation56 hz
    mixedMoment B raw31523step1 raw31523step1Labels = mixedMoment B raw31523step2 raw31523step2Labels := by
      have ha : raw31523step2 = (fun i j => raw31523step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31523step2 raw31523step1; decide +kernel
      have hl : raw31523step2Labels = raw31523step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31523step1 raw31523step1Labels permutation8 permutation7
    mixedMoment B raw31523step2 raw31523step2Labels = mixedMoment B raw31523step3 raw31523step3Labels := by
      have ha : raw31523step3 = -raw31523step2 := by apply Matrix.ext; change ∀ i j, raw31523step3 i j = -(raw31523step2 i j); unfold raw31523step3 raw31523step2; decide +kernel
      have hl : raw31523step3Labels = raw31523step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31523step3 raw31523step3Labels = mixedMoment B raw31523step4 raw31523step4Labels := by
      have ha : raw31523step4 = raw31523step3 := by apply Matrix.ext; unfold raw31523step4 raw31523step3; decide +kernel
      have hl : raw31523step3Labels = labelEmbedding1 ∘ raw31523step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31523step3 raw31523step3Labels raw31523step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2288 node2288Labels := by rfl

def raw31524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31524Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31524step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31524step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31524step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31524step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31524step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31524step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31524 raw31524Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw31524 raw31524Labels = mixedMoment B raw31524step0 raw31524step0Labels := by
      have hz : ∀ j, raw31524 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw31524step0 = (fun i j => raw31524 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw31524step0 raw31524; decide +kernel
      have hl : raw31524step0Labels = raw31524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31524 raw31524Labels permutation265 hz
    mixedMoment B raw31524step0 raw31524step0Labels = mixedMoment B raw31524step1 raw31524step1Labels := by
      have ha : raw31524step1 = (fun i j => raw31524step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31524step1 raw31524step0; decide +kernel
      have hl : raw31524step1Labels = raw31524step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31524step0 raw31524step0Labels permutation38 permutation7
    mixedMoment B raw31524step1 raw31524step1Labels = mixedMoment B raw31524step2 raw31524step2Labels := by
      have ha : raw31524step2 = -raw31524step1 := by apply Matrix.ext; change ∀ i j, raw31524step2 i j = -(raw31524step1 i j); unfold raw31524step2 raw31524step1; decide +kernel
      have hl : raw31524step2Labels = raw31524step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31524step2 raw31524step2Labels = mixedMoment B raw31524step3 raw31524step3Labels := by
      have ha : raw31524step3 = raw31524step2 := by apply Matrix.ext; unfold raw31524step3 raw31524step2; decide +kernel
      have hl : raw31524step2Labels = labelEmbedding1 ∘ raw31524step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31524step2 raw31524step2Labels raw31524step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2225 node2225Labels := by rfl

def raw31525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31525Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31525step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31525step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw31525step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31525step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31525step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31525step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31525step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31525 raw31525Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw31525 raw31525Labels = mixedMoment B raw31525step0 raw31525step0Labels := by
      have hz : ∀ j, raw31525 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31525step0 = (fun i j => raw31525 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31525step0 raw31525; decide +kernel
      have hl : raw31525step0Labels = raw31525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31525 raw31525Labels permutation434 hz
    mixedMoment B raw31525step0 raw31525step0Labels = mixedMoment B raw31525step1 raw31525step1Labels := by
      have hz : ∀ j, raw31525step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31525step1 = (fun i j => raw31525step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31525step1 raw31525step0; decide +kernel
      have hl : raw31525step1Labels = raw31525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31525step0 raw31525step0Labels permutation56 hz
    mixedMoment B raw31525step1 raw31525step1Labels = mixedMoment B raw31525step2 raw31525step2Labels := by
      have ha : raw31525step2 = (fun i j => raw31525step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31525step2 raw31525step1; decide +kernel
      have hl : raw31525step2Labels = raw31525step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31525step1 raw31525step1Labels permutation8 permutation7
    mixedMoment B raw31525step2 raw31525step2Labels = mixedMoment B raw31525step3 raw31525step3Labels := by
      have ha : raw31525step3 = -raw31525step2 := by apply Matrix.ext; change ∀ i j, raw31525step3 i j = -(raw31525step2 i j); unfold raw31525step3 raw31525step2; decide +kernel
      have hl : raw31525step3Labels = raw31525step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31525step3 raw31525step3Labels = mixedMoment B raw31525step4 raw31525step4Labels := by
      have ha : raw31525step4 = raw31525step3 := by apply Matrix.ext; unfold raw31525step4 raw31525step3; decide +kernel
      have hl : raw31525step3Labels = labelEmbedding1 ∘ raw31525step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31525step3 raw31525step3Labels raw31525step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

def raw31526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31526Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31526step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31526step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31526step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw31526step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31526step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31526step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31526step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31526step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31526 raw31526Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw31526 raw31526Labels = mixedMoment B raw31526step0 raw31526step0Labels := by
      have hz : ∀ j, raw31526 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31526step0 = (fun i j => raw31526 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31526step0 raw31526; decide +kernel
      have hl : raw31526step0Labels = raw31526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31526 raw31526Labels permutation434 hz
    mixedMoment B raw31526step0 raw31526step0Labels = mixedMoment B raw31526step1 raw31526step1Labels := by
      have hz : ∀ j, raw31526step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31526step1 = (fun i j => raw31526step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31526step1 raw31526step0; decide +kernel
      have hl : raw31526step1Labels = raw31526step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31526step0 raw31526step0Labels permutation56 hz
    mixedMoment B raw31526step1 raw31526step1Labels = mixedMoment B raw31526step2 raw31526step2Labels := by
      have ha : raw31526step2 = (fun i j => raw31526step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31526step2 raw31526step1; decide +kernel
      have hl : raw31526step2Labels = raw31526step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31526step1 raw31526step1Labels permutation9 permutation7
    mixedMoment B raw31526step2 raw31526step2Labels = mixedMoment B raw31526step3 raw31526step3Labels := by
      have ha : raw31526step3 = -raw31526step2 := by apply Matrix.ext; change ∀ i j, raw31526step3 i j = -(raw31526step2 i j); unfold raw31526step3 raw31526step2; decide +kernel
      have hl : raw31526step3Labels = raw31526step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31526step3 raw31526step3Labels = mixedMoment B raw31526step4 raw31526step4Labels := by
      have ha : raw31526step4 = raw31526step3 := by apply Matrix.ext; unfold raw31526step4 raw31526step3; decide +kernel
      have hl : raw31526step3Labels = labelEmbedding1 ∘ raw31526step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31526step3 raw31526step3Labels raw31526step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

def raw31527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31527Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31527step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31527step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31527step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31527step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw31527step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31527step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw31527step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31527 raw31527Labels = mixedMoment B node1691 node1691Labels := by
  calc
    mixedMoment B raw31527 raw31527Labels = mixedMoment B raw31527step0 raw31527step0Labels := by
      have hz : ∀ j, raw31527 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31527step0 = (fun i j => raw31527 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31527step0 raw31527; decide +kernel
      have hl : raw31527step0Labels = raw31527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31527 raw31527Labels permutation434 hz
    mixedMoment B raw31527step0 raw31527step0Labels = mixedMoment B raw31527step1 raw31527step1Labels := by
      have ha : raw31527step1 = (fun i j => raw31527step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31527step1 raw31527step0; decide +kernel
      have hl : raw31527step1Labels = raw31527step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31527step0 raw31527step0Labels permutation32 permutation7
    mixedMoment B raw31527step1 raw31527step1Labels = mixedMoment B raw31527step2 raw31527step2Labels := by
      have ha : raw31527step2 = -raw31527step1 := by apply Matrix.ext; change ∀ i j, raw31527step2 i j = -(raw31527step1 i j); unfold raw31527step2 raw31527step1; decide +kernel
      have hl : raw31527step2Labels = raw31527step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31527step2 raw31527step2Labels = mixedMoment B raw31527step3 raw31527step3Labels := by
      have ha : raw31527step3 = raw31527step2 := by apply Matrix.ext; unfold raw31527step3 raw31527step2; decide +kernel
      have hl : raw31527step2Labels = labelEmbedding1 ∘ raw31527step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31527step2 raw31527step2Labels raw31527step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1691 node1691Labels := by rfl

def raw31528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31528Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31528step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31528step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31528step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw31528step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31528step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw31528step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31528 raw31528Labels = mixedMoment B node2166 node2166Labels := by
  calc
    mixedMoment B raw31528 raw31528Labels = mixedMoment B raw31528step0 raw31528step0Labels := by
      have hz : ∀ j, raw31528 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31528step0 = (fun i j => raw31528 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31528step0 raw31528; decide +kernel
      have hl : raw31528step0Labels = raw31528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31528 raw31528Labels permutation434 hz
    mixedMoment B raw31528step0 raw31528step0Labels = mixedMoment B raw31528step1 raw31528step1Labels := by
      have ha : raw31528step1 = (fun i j => raw31528step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31528step1 raw31528step0; decide +kernel
      have hl : raw31528step1Labels = raw31528step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31528step0 raw31528step0Labels permutation32 permutation7
    mixedMoment B raw31528step1 raw31528step1Labels = mixedMoment B raw31528step2 raw31528step2Labels := by
      have ha : raw31528step2 = -raw31528step1 := by apply Matrix.ext; change ∀ i j, raw31528step2 i j = -(raw31528step1 i j); unfold raw31528step2 raw31528step1; decide +kernel
      have hl : raw31528step2Labels = raw31528step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31528step2 raw31528step2Labels = mixedMoment B raw31528step3 raw31528step3Labels := by
      have ha : raw31528step3 = raw31528step2 := by apply Matrix.ext; unfold raw31528step3 raw31528step2; decide +kernel
      have hl : raw31528step2Labels = labelEmbedding1 ∘ raw31528step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31528step2 raw31528step2Labels raw31528step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2166 node2166Labels := by rfl

def raw31529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31529Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31529step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31529step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw31529step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31529step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw31529step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31529 raw31529Labels = mixedMoment B node2183 node2183Labels := by
  calc
    mixedMoment B raw31529 raw31529Labels = mixedMoment B raw31529step0 raw31529step0Labels := by
      have ha : raw31529step0 = (fun i j => raw31529 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31529step0 raw31529; decide +kernel
      have hl : raw31529step0Labels = raw31529Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31529 raw31529Labels permutation158 permutation7
    mixedMoment B raw31529step0 raw31529step0Labels = mixedMoment B raw31529step1 raw31529step1Labels := by
      have ha : raw31529step1 = -raw31529step0 := by apply Matrix.ext; change ∀ i j, raw31529step1 i j = -(raw31529step0 i j); unfold raw31529step1 raw31529step0; decide +kernel
      have hl : raw31529step1Labels = raw31529step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31529step1 raw31529step1Labels = mixedMoment B raw31529step2 raw31529step2Labels := by
      have ha : raw31529step2 = raw31529step1 := by apply Matrix.ext; unfold raw31529step2 raw31529step1; decide +kernel
      have hl : raw31529step1Labels = labelEmbedding1 ∘ raw31529step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31529step1 raw31529step1Labels raw31529step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2183 node2183Labels := by rfl

def raw31530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31530Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31530step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw31530step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31530step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw31530step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31530step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw31530step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31530 raw31530Labels = mixedMoment B node2227 node2227Labels := by
  calc
    mixedMoment B raw31530 raw31530Labels = mixedMoment B raw31530step0 raw31530step0Labels := by
      have hz : ∀ j, raw31530 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31530step0 = (fun i j => raw31530 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31530step0 raw31530; decide +kernel
      have hl : raw31530step0Labels = raw31530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31530 raw31530Labels permutation434 hz
    mixedMoment B raw31530step0 raw31530step0Labels = mixedMoment B raw31530step1 raw31530step1Labels := by
      have ha : raw31530step1 = (fun i j => raw31530step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31530step1 raw31530step0; decide +kernel
      have hl : raw31530step1Labels = raw31530step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31530step0 raw31530step0Labels permutation32 permutation7
    mixedMoment B raw31530step1 raw31530step1Labels = mixedMoment B raw31530step2 raw31530step2Labels := by
      have ha : raw31530step2 = -raw31530step1 := by apply Matrix.ext; change ∀ i j, raw31530step2 i j = -(raw31530step1 i j); unfold raw31530step2 raw31530step1; decide +kernel
      have hl : raw31530step2Labels = raw31530step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31530step2 raw31530step2Labels = mixedMoment B raw31530step3 raw31530step3Labels := by
      have ha : raw31530step3 = raw31530step2 := by apply Matrix.ext; unfold raw31530step3 raw31530step2; decide +kernel
      have hl : raw31530step2Labels = labelEmbedding1 ∘ raw31530step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31530step2 raw31530step2Labels raw31530step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2227 node2227Labels := by rfl

def raw31531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31531Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31531step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw31531step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31531step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw31531step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31531step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw31531step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31531 raw31531Labels = mixedMoment B node2227 node2227Labels := by
  calc
    mixedMoment B raw31531 raw31531Labels = mixedMoment B raw31531step0 raw31531step0Labels := by
      have hz : ∀ j, raw31531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31531step0 = (fun i j => raw31531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31531step0 raw31531; decide +kernel
      have hl : raw31531step0Labels = raw31531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31531 raw31531Labels permutation434 hz
    mixedMoment B raw31531step0 raw31531step0Labels = mixedMoment B raw31531step1 raw31531step1Labels := by
      have ha : raw31531step1 = (fun i j => raw31531step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31531step1 raw31531step0; decide +kernel
      have hl : raw31531step1Labels = raw31531step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31531step0 raw31531step0Labels permutation33 permutation7
    mixedMoment B raw31531step1 raw31531step1Labels = mixedMoment B raw31531step2 raw31531step2Labels := by
      have ha : raw31531step2 = -raw31531step1 := by apply Matrix.ext; change ∀ i j, raw31531step2 i j = -(raw31531step1 i j); unfold raw31531step2 raw31531step1; decide +kernel
      have hl : raw31531step2Labels = raw31531step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31531step2 raw31531step2Labels = mixedMoment B raw31531step3 raw31531step3Labels := by
      have ha : raw31531step3 = raw31531step2 := by apply Matrix.ext; unfold raw31531step3 raw31531step2; decide +kernel
      have hl : raw31531step2Labels = labelEmbedding1 ∘ raw31531step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31531step2 raw31531step2Labels raw31531step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2227 node2227Labels := by rfl

def raw31532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31532Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31532step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31532step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31532step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31532step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31532step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31532 raw31532Labels = mixedMoment B node1671 node1671Labels := by
  calc
    mixedMoment B raw31532 raw31532Labels = mixedMoment B raw31532step0 raw31532step0Labels := by
      have ha : raw31532step0 = (fun i j => raw31532 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31532step0 raw31532; decide +kernel
      have hl : raw31532step0Labels = raw31532Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31532 raw31532Labels permutation158 permutation7
    mixedMoment B raw31532step0 raw31532step0Labels = mixedMoment B raw31532step1 raw31532step1Labels := by
      have ha : raw31532step1 = -raw31532step0 := by apply Matrix.ext; change ∀ i j, raw31532step1 i j = -(raw31532step0 i j); unfold raw31532step1 raw31532step0; decide +kernel
      have hl : raw31532step1Labels = raw31532step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31532step1 raw31532step1Labels = mixedMoment B raw31532step2 raw31532step2Labels := by
      have ha : raw31532step2 = raw31532step1 := by apply Matrix.ext; unfold raw31532step2 raw31532step1; decide +kernel
      have hl : raw31532step1Labels = labelEmbedding1 ∘ raw31532step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31532step1 raw31532step1Labels raw31532step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1671 node1671Labels := by rfl

def raw31533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31533Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31533step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31533step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31533step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31533step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31533step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31533 raw31533Labels = mixedMoment B node2148 node2148Labels := by
  calc
    mixedMoment B raw31533 raw31533Labels = mixedMoment B raw31533step0 raw31533step0Labels := by
      have ha : raw31533step0 = (fun i j => raw31533 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31533step0 raw31533; decide +kernel
      have hl : raw31533step0Labels = raw31533Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31533 raw31533Labels permutation158 permutation7
    mixedMoment B raw31533step0 raw31533step0Labels = mixedMoment B raw31533step1 raw31533step1Labels := by
      have ha : raw31533step1 = -raw31533step0 := by apply Matrix.ext; change ∀ i j, raw31533step1 i j = -(raw31533step0 i j); unfold raw31533step1 raw31533step0; decide +kernel
      have hl : raw31533step1Labels = raw31533step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31533step1 raw31533step1Labels = mixedMoment B raw31533step2 raw31533step2Labels := by
      have ha : raw31533step2 = raw31533step1 := by apply Matrix.ext; unfold raw31533step2 raw31533step1; decide +kernel
      have hl : raw31533step1Labels = labelEmbedding1 ∘ raw31533step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31533step1 raw31533step1Labels raw31533step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2148 node2148Labels := by rfl

def raw31534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31534Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31534step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31534step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31534step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31534step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw31534step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31534 raw31534Labels = mixedMoment B node2199 node2199Labels := by
  calc
    mixedMoment B raw31534 raw31534Labels = mixedMoment B raw31534step0 raw31534step0Labels := by
      have ha : raw31534step0 = (fun i j => raw31534 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31534step0 raw31534; decide +kernel
      have hl : raw31534step0Labels = raw31534Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31534 raw31534Labels permutation158 permutation7
    mixedMoment B raw31534step0 raw31534step0Labels = mixedMoment B raw31534step1 raw31534step1Labels := by
      have ha : raw31534step1 = -raw31534step0 := by apply Matrix.ext; change ∀ i j, raw31534step1 i j = -(raw31534step0 i j); unfold raw31534step1 raw31534step0; decide +kernel
      have hl : raw31534step1Labels = raw31534step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31534step1 raw31534step1Labels = mixedMoment B raw31534step2 raw31534step2Labels := by
      have ha : raw31534step2 = raw31534step1 := by apply Matrix.ext; unfold raw31534step2 raw31534step1; decide +kernel
      have hl : raw31534step1Labels = labelEmbedding1 ∘ raw31534step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31534step1 raw31534step1Labels raw31534step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2199 node2199Labels := by rfl

def raw31535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31535Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw31535step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31535step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31535step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31535step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31535step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31535 raw31535Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw31535 raw31535Labels = mixedMoment B raw31535step0 raw31535step0Labels := by
      have ha : raw31535step0 = (fun i j => raw31535 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31535step0 raw31535; decide +kernel
      have hl : raw31535step0Labels = raw31535Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31535 raw31535Labels permutation158 permutation7
    mixedMoment B raw31535step0 raw31535step0Labels = mixedMoment B raw31535step1 raw31535step1Labels := by
      have ha : raw31535step1 = -raw31535step0 := by apply Matrix.ext; change ∀ i j, raw31535step1 i j = -(raw31535step0 i j); unfold raw31535step1 raw31535step0; decide +kernel
      have hl : raw31535step1Labels = raw31535step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31535step1 raw31535step1Labels = mixedMoment B raw31535step2 raw31535step2Labels := by
      have ha : raw31535step2 = raw31535step1 := by apply Matrix.ext; unfold raw31535step2 raw31535step1; decide +kernel
      have hl : raw31535step1Labels = labelEmbedding1 ∘ raw31535step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31535step1 raw31535step1Labels raw31535step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

def raw31536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31536Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw31536step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31536step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31536step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31536step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw31536step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31536 raw31536Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw31536 raw31536Labels = mixedMoment B raw31536step0 raw31536step0Labels := by
      have ha : raw31536step0 = (fun i j => raw31536 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31536step0 raw31536; decide +kernel
      have hl : raw31536step0Labels = raw31536Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31536 raw31536Labels permutation159 permutation7
    mixedMoment B raw31536step0 raw31536step0Labels = mixedMoment B raw31536step1 raw31536step1Labels := by
      have ha : raw31536step1 = -raw31536step0 := by apply Matrix.ext; change ∀ i j, raw31536step1 i j = -(raw31536step0 i j); unfold raw31536step1 raw31536step0; decide +kernel
      have hl : raw31536step1Labels = raw31536step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31536step1 raw31536step1Labels = mixedMoment B raw31536step2 raw31536step2Labels := by
      have ha : raw31536step2 = raw31536step1 := by apply Matrix.ext; unfold raw31536step2 raw31536step1; decide +kernel
      have hl : raw31536step1Labels = labelEmbedding1 ∘ raw31536step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31536step1 raw31536step1Labels raw31536step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

def raw31537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31537Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31537step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31537step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw31537step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31537step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw31537step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31537step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw31537step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31537 raw31537Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw31537 raw31537Labels = mixedMoment B raw31537step0 raw31537step0Labels := by
      have hz : ∀ j, raw31537 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31537step0 = (fun i j => raw31537 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31537step0 raw31537; decide +kernel
      have hl : raw31537step0Labels = raw31537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31537 raw31537Labels permutation434 hz
    mixedMoment B raw31537step0 raw31537step0Labels = mixedMoment B raw31537step1 raw31537step1Labels := by
      have ha : raw31537step1 = (fun i j => raw31537step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31537step1 raw31537step0; decide +kernel
      have hl : raw31537step1Labels = raw31537step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31537step0 raw31537step0Labels permutation33 permutation7
    mixedMoment B raw31537step1 raw31537step1Labels = mixedMoment B raw31537step2 raw31537step2Labels := by
      have ha : raw31537step2 = -raw31537step1 := by apply Matrix.ext; change ∀ i j, raw31537step2 i j = -(raw31537step1 i j); unfold raw31537step2 raw31537step1; decide +kernel
      have hl : raw31537step2Labels = raw31537step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31537step2 raw31537step2Labels = mixedMoment B raw31537step3 raw31537step3Labels := by
      have ha : raw31537step3 = raw31537step2 := by apply Matrix.ext; unfold raw31537step3 raw31537step2; decide +kernel
      have hl : raw31537step2Labels = labelEmbedding1 ∘ raw31537step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31537step2 raw31537step2Labels raw31537step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1689 node1689Labels := by rfl

def raw31538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31538Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31538step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw31538step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31538step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw31538step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31538step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw31538step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31538 raw31538Labels = mixedMoment B node2164 node2164Labels := by
  calc
    mixedMoment B raw31538 raw31538Labels = mixedMoment B raw31538step0 raw31538step0Labels := by
      have hz : ∀ j, raw31538 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31538step0 = (fun i j => raw31538 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31538step0 raw31538; decide +kernel
      have hl : raw31538step0Labels = raw31538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31538 raw31538Labels permutation434 hz
    mixedMoment B raw31538step0 raw31538step0Labels = mixedMoment B raw31538step1 raw31538step1Labels := by
      have ha : raw31538step1 = (fun i j => raw31538step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31538step1 raw31538step0; decide +kernel
      have hl : raw31538step1Labels = raw31538step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31538step0 raw31538step0Labels permutation33 permutation7
    mixedMoment B raw31538step1 raw31538step1Labels = mixedMoment B raw31538step2 raw31538step2Labels := by
      have ha : raw31538step2 = -raw31538step1 := by apply Matrix.ext; change ∀ i j, raw31538step2 i j = -(raw31538step1 i j); unfold raw31538step2 raw31538step1; decide +kernel
      have hl : raw31538step2Labels = raw31538step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31538step2 raw31538step2Labels = mixedMoment B raw31538step3 raw31538step3Labels := by
      have ha : raw31538step3 = raw31538step2 := by apply Matrix.ext; unfold raw31538step3 raw31538step2; decide +kernel
      have hl : raw31538step2Labels = labelEmbedding1 ∘ raw31538step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31538step2 raw31538step2Labels raw31538step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2164 node2164Labels := by rfl

def raw31539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31539Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31539step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw31539step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31539step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw31539step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31539step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw31539step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31539 raw31539Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw31539 raw31539Labels = mixedMoment B raw31539step0 raw31539step0Labels := by
      have hz : ∀ j, raw31539 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31539step0 = (fun i j => raw31539 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31539step0 raw31539; decide +kernel
      have hl : raw31539step0Labels = raw31539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31539 raw31539Labels permutation434 hz
    mixedMoment B raw31539step0 raw31539step0Labels = mixedMoment B raw31539step1 raw31539step1Labels := by
      have ha : raw31539step1 = (fun i j => raw31539step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31539step1 raw31539step0; decide +kernel
      have hl : raw31539step1Labels = raw31539step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31539step0 raw31539step0Labels permutation33 permutation7
    mixedMoment B raw31539step1 raw31539step1Labels = mixedMoment B raw31539step2 raw31539step2Labels := by
      have ha : raw31539step2 = -raw31539step1 := by apply Matrix.ext; change ∀ i j, raw31539step2 i j = -(raw31539step1 i j); unfold raw31539step2 raw31539step1; decide +kernel
      have hl : raw31539step2Labels = raw31539step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31539step2 raw31539step2Labels = mixedMoment B raw31539step3 raw31539step3Labels := by
      have ha : raw31539step3 = raw31539step2 := by apply Matrix.ext; unfold raw31539step3 raw31539step2; decide +kernel
      have hl : raw31539step2Labels = labelEmbedding1 ∘ raw31539step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31539step2 raw31539step2Labels raw31539step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2223 node2223Labels := by rfl

def raw31540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31540Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw31540step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31540step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw31540step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31540step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw31540step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31540 raw31540Labels = mixedMoment B node2181 node2181Labels := by
  calc
    mixedMoment B raw31540 raw31540Labels = mixedMoment B raw31540step0 raw31540step0Labels := by
      have ha : raw31540step0 = (fun i j => raw31540 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31540step0 raw31540; decide +kernel
      have hl : raw31540step0Labels = raw31540Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31540 raw31540Labels permutation159 permutation7
    mixedMoment B raw31540step0 raw31540step0Labels = mixedMoment B raw31540step1 raw31540step1Labels := by
      have ha : raw31540step1 = -raw31540step0 := by apply Matrix.ext; change ∀ i j, raw31540step1 i j = -(raw31540step0 i j); unfold raw31540step1 raw31540step0; decide +kernel
      have hl : raw31540step1Labels = raw31540step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31540step1 raw31540step1Labels = mixedMoment B raw31540step2 raw31540step2Labels := by
      have ha : raw31540step2 = raw31540step1 := by apply Matrix.ext; unfold raw31540step2 raw31540step1; decide +kernel
      have hl : raw31540step1Labels = labelEmbedding1 ∘ raw31540step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31540step1 raw31540step1Labels raw31540step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2181 node2181Labels := by rfl

def raw31541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31541Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1], ![1, 0, -1]]
def raw31541step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw31541step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31541step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw31541step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31541step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw31541step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31541 raw31541Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw31541 raw31541Labels = mixedMoment B raw31541step0 raw31541step0Labels := by
      have hz : ∀ j, raw31541 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31541step0 = (fun i j => raw31541 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31541step0 raw31541; decide +kernel
      have hl : raw31541step0Labels = raw31541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31541 raw31541Labels permutation434 hz
    mixedMoment B raw31541step0 raw31541step0Labels = mixedMoment B raw31541step1 raw31541step1Labels := by
      have ha : raw31541step1 = (fun i j => raw31541step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31541step1 raw31541step0; decide +kernel
      have hl : raw31541step1Labels = raw31541step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31541step0 raw31541step0Labels permutation33 permutation7
    mixedMoment B raw31541step1 raw31541step1Labels = mixedMoment B raw31541step2 raw31541step2Labels := by
      have ha : raw31541step2 = -raw31541step1 := by apply Matrix.ext; change ∀ i j, raw31541step2 i j = -(raw31541step1 i j); unfold raw31541step2 raw31541step1; decide +kernel
      have hl : raw31541step2Labels = raw31541step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31541step2 raw31541step2Labels = mixedMoment B raw31541step3 raw31541step3Labels := by
      have ha : raw31541step3 = raw31541step2 := by apply Matrix.ext; unfold raw31541step3 raw31541step2; decide +kernel
      have hl : raw31541step2Labels = labelEmbedding1 ∘ raw31541step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31541step2 raw31541step2Labels raw31541step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw31542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31542Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31542step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw31542step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31542step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw31542step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31542step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw31542step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31542 raw31542Labels = mixedMoment B node1689 node1689Labels := by
  calc
    mixedMoment B raw31542 raw31542Labels = mixedMoment B raw31542step0 raw31542step0Labels := by
      have hz : ∀ j, raw31542 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31542step0 = (fun i j => raw31542 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31542step0 raw31542; decide +kernel
      have hl : raw31542step0Labels = raw31542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31542 raw31542Labels permutation434 hz
    mixedMoment B raw31542step0 raw31542step0Labels = mixedMoment B raw31542step1 raw31542step1Labels := by
      have ha : raw31542step1 = (fun i j => raw31542step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31542step1 raw31542step0; decide +kernel
      have hl : raw31542step1Labels = raw31542step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31542step0 raw31542step0Labels permutation32 permutation7
    mixedMoment B raw31542step1 raw31542step1Labels = mixedMoment B raw31542step2 raw31542step2Labels := by
      have ha : raw31542step2 = -raw31542step1 := by apply Matrix.ext; change ∀ i j, raw31542step2 i j = -(raw31542step1 i j); unfold raw31542step2 raw31542step1; decide +kernel
      have hl : raw31542step2Labels = raw31542step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31542step2 raw31542step2Labels = mixedMoment B raw31542step3 raw31542step3Labels := by
      have ha : raw31542step3 = raw31542step2 := by apply Matrix.ext; unfold raw31542step3 raw31542step2; decide +kernel
      have hl : raw31542step2Labels = labelEmbedding1 ∘ raw31542step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31542step2 raw31542step2Labels raw31542step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1689 node1689Labels := by rfl

def raw31543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31543Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31543step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw31543step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw31543step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31543step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw31543step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31543 raw31543Labels = mixedMoment B node2164 node2164Labels := by
  calc
    mixedMoment B raw31543 raw31543Labels = mixedMoment B raw31543step0 raw31543step0Labels := by
      have hz : ∀ j, raw31543 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31543step0 = (fun i j => raw31543 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31543step0 raw31543; decide +kernel
      have hl : raw31543step0Labels = raw31543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31543 raw31543Labels permutation434 hz
    mixedMoment B raw31543step0 raw31543step0Labels = mixedMoment B raw31543step1 raw31543step1Labels := by
      have ha : raw31543step1 = (fun i j => raw31543step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31543step1 raw31543step0; decide +kernel
      have hl : raw31543step1Labels = raw31543step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31543step0 raw31543step0Labels permutation32 permutation7
    mixedMoment B raw31543step1 raw31543step1Labels = mixedMoment B raw31543step2 raw31543step2Labels := by
      have ha : raw31543step2 = -raw31543step1 := by apply Matrix.ext; change ∀ i j, raw31543step2 i j = -(raw31543step1 i j); unfold raw31543step2 raw31543step1; decide +kernel
      have hl : raw31543step2Labels = raw31543step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31543step2 raw31543step2Labels = mixedMoment B raw31543step3 raw31543step3Labels := by
      have ha : raw31543step3 = raw31543step2 := by apply Matrix.ext; unfold raw31543step3 raw31543step2; decide +kernel
      have hl : raw31543step2Labels = labelEmbedding1 ∘ raw31543step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31543step2 raw31543step2Labels raw31543step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2164 node2164Labels := by rfl

def raw31544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31544Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31544step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -2, 3]]
def raw31544step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31544step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw31544step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31544step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 2, -3]]
def raw31544step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31544 raw31544Labels = mixedMoment B node2223 node2223Labels := by
  calc
    mixedMoment B raw31544 raw31544Labels = mixedMoment B raw31544step0 raw31544step0Labels := by
      have hz : ∀ j, raw31544 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31544step0 = (fun i j => raw31544 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31544step0 raw31544; decide +kernel
      have hl : raw31544step0Labels = raw31544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31544 raw31544Labels permutation434 hz
    mixedMoment B raw31544step0 raw31544step0Labels = mixedMoment B raw31544step1 raw31544step1Labels := by
      have ha : raw31544step1 = (fun i j => raw31544step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31544step1 raw31544step0; decide +kernel
      have hl : raw31544step1Labels = raw31544step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31544step0 raw31544step0Labels permutation32 permutation7
    mixedMoment B raw31544step1 raw31544step1Labels = mixedMoment B raw31544step2 raw31544step2Labels := by
      have ha : raw31544step2 = -raw31544step1 := by apply Matrix.ext; change ∀ i j, raw31544step2 i j = -(raw31544step1 i j); unfold raw31544step2 raw31544step1; decide +kernel
      have hl : raw31544step2Labels = raw31544step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31544step2 raw31544step2Labels = mixedMoment B raw31544step3 raw31544step3Labels := by
      have ha : raw31544step3 = raw31544step2 := by apply Matrix.ext; unfold raw31544step3 raw31544step2; decide +kernel
      have hl : raw31544step2Labels = labelEmbedding1 ∘ raw31544step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31544step2 raw31544step2Labels raw31544step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2223 node2223Labels := by rfl

def raw31545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31545Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw31545step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw31545step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31545step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw31545step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31545 raw31545Labels = mixedMoment B node2181 node2181Labels := by
  calc
    mixedMoment B raw31545 raw31545Labels = mixedMoment B raw31545step0 raw31545step0Labels := by
      have ha : raw31545step0 = (fun i j => raw31545 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31545step0 raw31545; decide +kernel
      have hl : raw31545step0Labels = raw31545Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31545 raw31545Labels permutation158 permutation7
    mixedMoment B raw31545step0 raw31545step0Labels = mixedMoment B raw31545step1 raw31545step1Labels := by
      have ha : raw31545step1 = -raw31545step0 := by apply Matrix.ext; change ∀ i j, raw31545step1 i j = -(raw31545step0 i j); unfold raw31545step1 raw31545step0; decide +kernel
      have hl : raw31545step1Labels = raw31545step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31545step1 raw31545step1Labels = mixedMoment B raw31545step2 raw31545step2Labels := by
      have ha : raw31545step2 = raw31545step1 := by apply Matrix.ext; unfold raw31545step2 raw31545step1; decide +kernel
      have hl : raw31545step1Labels = labelEmbedding1 ∘ raw31545step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31545step1 raw31545step1Labels raw31545step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2181 node2181Labels := by rfl

def raw31546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw31546Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw31546step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31546step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw31546step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31546step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw31546step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31546step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw31546step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31546 raw31546Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw31546 raw31546Labels = mixedMoment B raw31546step0 raw31546step0Labels := by
      have hz : ∀ j, raw31546 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31546step0 = (fun i j => raw31546 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31546step0 raw31546; decide +kernel
      have hl : raw31546step0Labels = raw31546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31546 raw31546Labels permutation434 hz
    mixedMoment B raw31546step0 raw31546step0Labels = mixedMoment B raw31546step1 raw31546step1Labels := by
      have ha : raw31546step1 = (fun i j => raw31546step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31546step1 raw31546step0; decide +kernel
      have hl : raw31546step1Labels = raw31546step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31546step0 raw31546step0Labels permutation32 permutation7
    mixedMoment B raw31546step1 raw31546step1Labels = mixedMoment B raw31546step2 raw31546step2Labels := by
      have ha : raw31546step2 = -raw31546step1 := by apply Matrix.ext; change ∀ i j, raw31546step2 i j = -(raw31546step1 i j); unfold raw31546step2 raw31546step1; decide +kernel
      have hl : raw31546step2Labels = raw31546step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31546step2 raw31546step2Labels = mixedMoment B raw31546step3 raw31546step3Labels := by
      have ha : raw31546step3 = raw31546step2 := by apply Matrix.ext; unfold raw31546step3 raw31546step2; decide +kernel
      have hl : raw31546step2Labels = labelEmbedding1 ∘ raw31546step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31546step2 raw31546step2Labels raw31546step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw31547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31547Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31547step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31547 raw31547Labels = mixedMoment B node3380 node3380Labels := by
  calc
    mixedMoment B raw31547 raw31547Labels = mixedMoment B raw31547step0 raw31547step0Labels := by
      have hz : ∀ j, raw31547 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31547step0 = (fun i j => raw31547 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31547step0 raw31547; decide +kernel
      have hl : raw31547step0Labels = raw31547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31547 raw31547Labels permutation434 hz
    _ = mixedMoment B node3380 node3380Labels := by rfl

def raw31548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31548step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31548 raw31548Labels = mixedMoment B node2029 node2029Labels := by
  calc
    mixedMoment B raw31548 raw31548Labels = mixedMoment B raw31548step0 raw31548step0Labels := by
      have hz : ∀ j, raw31548 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31548step0 = (fun i j => raw31548 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31548step0 raw31548; decide +kernel
      have hl : raw31548step0Labels = raw31548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31548 raw31548Labels permutation434 hz
    _ = mixedMoment B node2029 node2029Labels := by rfl

def raw31549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31549Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31549step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31549 raw31549Labels = mixedMoment B node1815 node1815Labels := by
  calc
    mixedMoment B raw31549 raw31549Labels = mixedMoment B raw31549step0 raw31549step0Labels := by
      have hz : ∀ j, raw31549 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31549step0 = (fun i j => raw31549 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31549step0 raw31549; decide +kernel
      have hl : raw31549step0Labels = raw31549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31549 raw31549Labels permutation434 hz
    _ = mixedMoment B node1815 node1815Labels := by rfl

def raw31550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31550Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31550 raw31550Labels = mixedMoment B node1792 node1792Labels := by
  calc
    _ = mixedMoment B node1792 node1792Labels := by rfl

def raw31551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw31551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31551step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31551step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31551 raw31551Labels = mixedMoment B node1796 node1796Labels := by
  calc
    mixedMoment B raw31551 raw31551Labels = mixedMoment B raw31551step0 raw31551step0Labels := by
      have hz : ∀ j, raw31551 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31551step0 = (fun i j => raw31551 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31551step0 raw31551; decide +kernel
      have hl : raw31551step0Labels = raw31551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31551 raw31551Labels permutation434 hz
    mixedMoment B raw31551step0 raw31551step0Labels = mixedMoment B raw31551step1 raw31551step1Labels := by
      have ha : raw31551step1 = (fun i j => raw31551step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31551step1 raw31551step0; decide +kernel
      have hl : raw31551step1Labels = raw31551step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31551step0 raw31551step0Labels permutation33 permutation2
    _ = mixedMoment B node1796 node1796Labels := by rfl

def raw31552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw31552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31552 raw31552Labels = mixedMoment B node1796 node1796Labels := by
  calc
    mixedMoment B raw31552 raw31552Labels = mixedMoment B raw31552step0 raw31552step0Labels := by
      have hz : ∀ j, raw31552 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31552step0 = (fun i j => raw31552 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31552step0 raw31552; decide +kernel
      have hl : raw31552step0Labels = raw31552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31552 raw31552Labels permutation434 hz
    _ = mixedMoment B node1796 node1796Labels := by rfl

def raw31553 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]
def raw31553Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31553step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]
def raw31553step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw31553step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw31553step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical31553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31553 raw31553Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw31553 raw31553Labels = mixedMoment B raw31553step0 raw31553step0Labels := by
      have hz : ∀ j, raw31553 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31553step0 = (fun i j => raw31553 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31553step0 raw31553; decide +kernel
      have hl : raw31553step0Labels = raw31553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31553 raw31553Labels permutation434 hz
    mixedMoment B raw31553step0 raw31553step0Labels = mixedMoment B raw31553step1 raw31553step1Labels := by
      have hz : ∀ j, raw31553step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31553step1 = (fun i j => raw31553step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31553step1 raw31553step0; decide +kernel
      have hl : raw31553step1Labels = raw31553step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31553step0 raw31553step0Labels permutation56 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw31554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31554 raw31554Labels = mixedMoment B node933 node933Labels := by
  calc
    mixedMoment B raw31554 raw31554Labels = mixedMoment B raw31554step0 raw31554step0Labels := by
      have hz : ∀ j, raw31554 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31554step0 = (fun i j => raw31554 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31554step0 raw31554; decide +kernel
      have hl : raw31554step0Labels = raw31554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31554 raw31554Labels permutation434 hz
    _ = mixedMoment B node933 node933Labels := by rfl

def raw31555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31555 raw31555Labels = mixedMoment B node1967 node1967Labels := by
  calc
    mixedMoment B raw31555 raw31555Labels = mixedMoment B raw31555step0 raw31555step0Labels := by
      have ha : raw31555step0 = (fun i j => raw31555 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31555step0 raw31555; decide +kernel
      have hl : raw31555step0Labels = raw31555Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31555 raw31555Labels permutation158 permutation2
    _ = mixedMoment B node1967 node1967Labels := by rfl

def raw31556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31556step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31556 raw31556Labels = mixedMoment B node2057 node2057Labels := by
  calc
    mixedMoment B raw31556 raw31556Labels = mixedMoment B raw31556step0 raw31556step0Labels := by
      have hz : ∀ j, raw31556 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31556step0 = (fun i j => raw31556 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31556step0 raw31556; decide +kernel
      have hl : raw31556step0Labels = raw31556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31556 raw31556Labels permutation434 hz
    _ = mixedMoment B node2057 node2057Labels := by rfl

def raw31557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw31557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31557step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31557step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31557 raw31557Labels = mixedMoment B node2057 node2057Labels := by
  calc
    mixedMoment B raw31557 raw31557Labels = mixedMoment B raw31557step0 raw31557step0Labels := by
      have hz : ∀ j, raw31557 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31557step0 = (fun i j => raw31557 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31557step0 raw31557; decide +kernel
      have hl : raw31557step0Labels = raw31557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31557 raw31557Labels permutation434 hz
    mixedMoment B raw31557step0 raw31557step0Labels = mixedMoment B raw31557step1 raw31557step1Labels := by
      have ha : raw31557step1 = (fun i j => raw31557step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31557step1 raw31557step0; decide +kernel
      have hl : raw31557step1Labels = raw31557step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31557step0 raw31557step0Labels permutation33 permutation2
    _ = mixedMoment B node2057 node2057Labels := by rfl

def raw31558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31558 raw31558Labels = mixedMoment B node907 node907Labels := by
  calc
    _ = mixedMoment B node907 node907Labels := by rfl

def raw31559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31559Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31559 raw31559Labels = mixedMoment B node1975 node1975Labels := by
  calc
    _ = mixedMoment B node1975 node1975Labels := by rfl

def raw31560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31560 raw31560Labels = mixedMoment B node2020 node2020Labels := by
  calc
    _ = mixedMoment B node2020 node2020Labels := by rfl

def raw31561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31561Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31561 raw31561Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw31561 raw31561Labels = mixedMoment B raw31561step0 raw31561step0Labels := by
      have ha : raw31561step0 = (fun i j => raw31561 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31561step0 raw31561; decide +kernel
      have hl : raw31561step0Labels = raw31561Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31561 raw31561Labels permutation153 permutation2
    _ = mixedMoment B node2020 node2020Labels := by rfl

def raw31562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31562step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31562step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31562step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31562 raw31562Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw31562 raw31562Labels = mixedMoment B raw31562step0 raw31562step0Labels := by
      have hz : ∀ j, raw31562 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31562step0 = (fun i j => raw31562 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31562step0 raw31562; decide +kernel
      have hl : raw31562step0Labels = raw31562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31562 raw31562Labels permutation434 hz
    mixedMoment B raw31562step0 raw31562step0Labels = mixedMoment B raw31562step1 raw31562step1Labels := by
      have ha : raw31562step1 = (fun i j => raw31562step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31562step1 raw31562step0; decide +kernel
      have hl : raw31562step1Labels = raw31562step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31562step0 raw31562step0Labels permutation32 permutation3
    mixedMoment B raw31562step1 raw31562step1Labels = mixedMoment B raw31562step2 raw31562step2Labels := by
      have ha : raw31562step2 = raw31562step1 := by apply Matrix.ext; unfold raw31562step2 raw31562step1; decide +kernel
      have hl : raw31562step1Labels = labelEmbedding6 ∘ raw31562step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31562step1 raw31562step1Labels raw31562step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw31563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31563step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31563step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31563step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31563step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31563 raw31563Labels = mixedMoment B node5418 node5418Labels := by
  calc
    mixedMoment B raw31563 raw31563Labels = mixedMoment B raw31563step0 raw31563step0Labels := by
      have hz : ∀ j, raw31563 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31563step0 = (fun i j => raw31563 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31563step0 raw31563; decide +kernel
      have hl : raw31563step0Labels = raw31563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31563 raw31563Labels permutation434 hz
    mixedMoment B raw31563step0 raw31563step0Labels = mixedMoment B raw31563step1 raw31563step1Labels := by
      have ha : raw31563step1 = (fun i j => raw31563step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31563step1 raw31563step0; decide +kernel
      have hl : raw31563step1Labels = raw31563step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31563step0 raw31563step0Labels permutation32 permutation3
    mixedMoment B raw31563step1 raw31563step1Labels = mixedMoment B raw31563step2 raw31563step2Labels := by
      have ha : raw31563step2 = raw31563step1 := by apply Matrix.ext; unfold raw31563step2 raw31563step1; decide +kernel
      have hl : raw31563step1Labels = labelEmbedding6 ∘ raw31563step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31563step1 raw31563step1Labels raw31563step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5418 node5418Labels := by rfl

def raw31564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31564step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31564step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31564step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31564step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31564 raw31564Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw31564 raw31564Labels = mixedMoment B raw31564step0 raw31564step0Labels := by
      have ha : raw31564step0 = (fun i j => raw31564 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31564step0 raw31564; decide +kernel
      have hl : raw31564step0Labels = raw31564Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31564 raw31564Labels permutation200 permutation3
    mixedMoment B raw31564step0 raw31564step0Labels = mixedMoment B raw31564step1 raw31564step1Labels := by
      have ha : raw31564step1 = raw31564step0 := by apply Matrix.ext; unfold raw31564step1 raw31564step0; decide +kernel
      have hl : raw31564step0Labels = labelEmbedding6 ∘ raw31564step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31564step0 raw31564step0Labels raw31564step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw31565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw31565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw31565step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31565step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw31565step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31565 raw31565Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw31565 raw31565Labels = mixedMoment B raw31565step0 raw31565step0Labels := by
      have hz : ∀ j, raw31565 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31565step0 = (fun i j => raw31565 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31565step0 raw31565; decide +kernel
      have hl : raw31565step0Labels = raw31565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31565 raw31565Labels permutation434 hz
    mixedMoment B raw31565step0 raw31565step0Labels = mixedMoment B raw31565step1 raw31565step1Labels := by
      have ha : raw31565step1 = (fun i j => raw31565step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31565step1 raw31565step0; decide +kernel
      have hl : raw31565step1Labels = raw31565step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31565step0 raw31565step0Labels permutation33 permutation3
    mixedMoment B raw31565step1 raw31565step1Labels = mixedMoment B raw31565step2 raw31565step2Labels := by
      have ha : raw31565step2 = raw31565step1 := by apply Matrix.ext; unfold raw31565step2 raw31565step1; decide +kernel
      have hl : raw31565step1Labels = labelEmbedding6 ∘ raw31565step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31565step1 raw31565step1Labels raw31565step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw31566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw31566step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31566step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw31566step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31566 raw31566Labels = mixedMoment B node4224 node4224Labels := by
  calc
    mixedMoment B raw31566 raw31566Labels = mixedMoment B raw31566step0 raw31566step0Labels := by
      have hz : ∀ j, raw31566 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31566step0 = (fun i j => raw31566 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31566step0 raw31566; decide +kernel
      have hl : raw31566step0Labels = raw31566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31566 raw31566Labels permutation434 hz
    mixedMoment B raw31566step0 raw31566step0Labels = mixedMoment B raw31566step1 raw31566step1Labels := by
      have ha : raw31566step1 = (fun i j => raw31566step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31566step1 raw31566step0; decide +kernel
      have hl : raw31566step1Labels = raw31566step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31566step0 raw31566step0Labels permutation32 permutation3
    mixedMoment B raw31566step1 raw31566step1Labels = mixedMoment B raw31566step2 raw31566step2Labels := by
      have ha : raw31566step2 = raw31566step1 := by apply Matrix.ext; unfold raw31566step2 raw31566step1; decide +kernel
      have hl : raw31566step1Labels = labelEmbedding6 ∘ raw31566step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31566step1 raw31566step1Labels raw31566step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4224 node4224Labels := by rfl

def raw31567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw31567step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31567step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw31567step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31567 raw31567Labels = mixedMoment B node4654 node4654Labels := by
  calc
    mixedMoment B raw31567 raw31567Labels = mixedMoment B raw31567step0 raw31567step0Labels := by
      have hz : ∀ j, raw31567 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31567step0 = (fun i j => raw31567 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31567step0 raw31567; decide +kernel
      have hl : raw31567step0Labels = raw31567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31567 raw31567Labels permutation434 hz
    mixedMoment B raw31567step0 raw31567step0Labels = mixedMoment B raw31567step1 raw31567step1Labels := by
      have ha : raw31567step1 = (fun i j => raw31567step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31567step1 raw31567step0; decide +kernel
      have hl : raw31567step1Labels = raw31567step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31567step0 raw31567step0Labels permutation32 permutation3
    mixedMoment B raw31567step1 raw31567step1Labels = mixedMoment B raw31567step2 raw31567step2Labels := by
      have ha : raw31567step2 = raw31567step1 := by apply Matrix.ext; unfold raw31567step2 raw31567step1; decide +kernel
      have hl : raw31567step1Labels = labelEmbedding6 ∘ raw31567step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31567step1 raw31567step1Labels raw31567step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4654 node4654Labels := by rfl

def raw31568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31568step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw31568step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31568step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw31568step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31568 raw31568Labels = mixedMoment B node4717 node4717Labels := by
  calc
    mixedMoment B raw31568 raw31568Labels = mixedMoment B raw31568step0 raw31568step0Labels := by
      have ha : raw31568step0 = (fun i j => raw31568 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31568step0 raw31568; decide +kernel
      have hl : raw31568step0Labels = raw31568Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31568 raw31568Labels permutation200 permutation3
    mixedMoment B raw31568step0 raw31568step0Labels = mixedMoment B raw31568step1 raw31568step1Labels := by
      have ha : raw31568step1 = raw31568step0 := by apply Matrix.ext; unfold raw31568step1 raw31568step0; decide +kernel
      have hl : raw31568step0Labels = labelEmbedding6 ∘ raw31568step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31568step0 raw31568step0Labels raw31568step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4717 node4717Labels := by rfl

def raw31569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw31569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31569step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31569step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31569step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31569 raw31569Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw31569 raw31569Labels = mixedMoment B raw31569step0 raw31569step0Labels := by
      have hz : ∀ j, raw31569 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31569step0 = (fun i j => raw31569 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31569step0 raw31569; decide +kernel
      have hl : raw31569step0Labels = raw31569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31569 raw31569Labels permutation434 hz
    mixedMoment B raw31569step0 raw31569step0Labels = mixedMoment B raw31569step1 raw31569step1Labels := by
      have ha : raw31569step1 = (fun i j => raw31569step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31569step1 raw31569step0; decide +kernel
      have hl : raw31569step1Labels = raw31569step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31569step0 raw31569step0Labels permutation36 permutation3
    mixedMoment B raw31569step1 raw31569step1Labels = mixedMoment B raw31569step2 raw31569step2Labels := by
      have ha : raw31569step2 = raw31569step1 := by apply Matrix.ext; unfold raw31569step2 raw31569step1; decide +kernel
      have hl : raw31569step1Labels = labelEmbedding6 ∘ raw31569step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31569step1 raw31569step1Labels raw31569step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw31570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31570step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31570step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31570step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31570 raw31570Labels = mixedMoment B node4201 node4201Labels := by
  calc
    mixedMoment B raw31570 raw31570Labels = mixedMoment B raw31570step0 raw31570step0Labels := by
      have ha : raw31570step0 = (fun i j => raw31570 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31570step0 raw31570; decide +kernel
      have hl : raw31570step0Labels = raw31570Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31570 raw31570Labels permutation152 permutation3
    mixedMoment B raw31570step0 raw31570step0Labels = mixedMoment B raw31570step1 raw31570step1Labels := by
      have ha : raw31570step1 = raw31570step0 := by apply Matrix.ext; unfold raw31570step1 raw31570step0; decide +kernel
      have hl : raw31570step0Labels = labelEmbedding6 ∘ raw31570step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31570step0 raw31570step0Labels raw31570step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4201 node4201Labels := by rfl

def raw31571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31571step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31571step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31571step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31571 raw31571Labels = mixedMoment B node4635 node4635Labels := by
  calc
    mixedMoment B raw31571 raw31571Labels = mixedMoment B raw31571step0 raw31571step0Labels := by
      have ha : raw31571step0 = (fun i j => raw31571 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31571step0 raw31571; decide +kernel
      have hl : raw31571step0Labels = raw31571Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31571 raw31571Labels permutation152 permutation3
    mixedMoment B raw31571step0 raw31571step0Labels = mixedMoment B raw31571step1 raw31571step1Labels := by
      have ha : raw31571step1 = raw31571step0 := by apply Matrix.ext; unfold raw31571step1 raw31571step0; decide +kernel
      have hl : raw31571step0Labels = labelEmbedding6 ∘ raw31571step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31571step0 raw31571step0Labels raw31571step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4635 node4635Labels := by rfl

def raw31572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31572step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31572step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31572step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31572 raw31572Labels = mixedMoment B node4767 node4767Labels := by
  calc
    mixedMoment B raw31572 raw31572Labels = mixedMoment B raw31572step0 raw31572step0Labels := by
      have ha : raw31572step0 = (fun i j => raw31572 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31572step0 raw31572; decide +kernel
      have hl : raw31572step0Labels = raw31572Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31572 raw31572Labels permutation152 permutation3
    mixedMoment B raw31572step0 raw31572step0Labels = mixedMoment B raw31572step1 raw31572step1Labels := by
      have ha : raw31572step1 = raw31572step0 := by apply Matrix.ext; unfold raw31572step1 raw31572step0; decide +kernel
      have hl : raw31572step0Labels = labelEmbedding6 ∘ raw31572step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31572step0 raw31572step0Labels raw31572step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4767 node4767Labels := by rfl

def raw31573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -2, -1], ![2, -1, -1]]
def raw31573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31573step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31573step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31573step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31573step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31573 raw31573Labels = mixedMoment B node4204 node4204Labels := by
  calc
    mixedMoment B raw31573 raw31573Labels = mixedMoment B raw31573step0 raw31573step0Labels := by
      have hz : ∀ j, raw31573 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31573step0 = (fun i j => raw31573 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31573step0 raw31573; decide +kernel
      have hl : raw31573step0Labels = raw31573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31573 raw31573Labels permutation434 hz
    mixedMoment B raw31573step0 raw31573step0Labels = mixedMoment B raw31573step1 raw31573step1Labels := by
      have ha : raw31573step1 = (fun i j => raw31573step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31573step1 raw31573step0; decide +kernel
      have hl : raw31573step1Labels = raw31573step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31573step0 raw31573step0Labels permutation33 permutation3
    mixedMoment B raw31573step1 raw31573step1Labels = mixedMoment B raw31573step2 raw31573step2Labels := by
      have ha : raw31573step2 = raw31573step1 := by apply Matrix.ext; unfold raw31573step2 raw31573step1; decide +kernel
      have hl : raw31573step1Labels = labelEmbedding6 ∘ raw31573step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31573step1 raw31573step1Labels raw31573step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4204 node4204Labels := by rfl

def raw31574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![3, -2, -1], ![2, -1, -1]]
def raw31574step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31574step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31574step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31574 raw31574Labels = mixedMoment B node4637 node4637Labels := by
  calc
    mixedMoment B raw31574 raw31574Labels = mixedMoment B raw31574step0 raw31574step0Labels := by
      have hz : ∀ j, raw31574 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31574step0 = (fun i j => raw31574 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31574step0 raw31574; decide +kernel
      have hl : raw31574step0Labels = raw31574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31574 raw31574Labels permutation434 hz
    mixedMoment B raw31574step0 raw31574step0Labels = mixedMoment B raw31574step1 raw31574step1Labels := by
      have ha : raw31574step1 = (fun i j => raw31574step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31574step1 raw31574step0; decide +kernel
      have hl : raw31574step1Labels = raw31574step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31574step0 raw31574step0Labels permutation33 permutation3
    mixedMoment B raw31574step1 raw31574step1Labels = mixedMoment B raw31574step2 raw31574step2Labels := by
      have ha : raw31574step2 = raw31574step1 := by apply Matrix.ext; unfold raw31574step2 raw31574step1; decide +kernel
      have hl : raw31574step1Labels = labelEmbedding6 ∘ raw31574step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31574step1 raw31574step1Labels raw31574step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4637 node4637Labels := by rfl

def raw31575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![3, -2, -1], ![2, -1, -1]]
def raw31575step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31575step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31575step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31575step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31575 raw31575Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw31575 raw31575Labels = mixedMoment B raw31575step0 raw31575step0Labels := by
      have hz : ∀ j, raw31575 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31575step0 = (fun i j => raw31575 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31575step0 raw31575; decide +kernel
      have hl : raw31575step0Labels = raw31575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31575 raw31575Labels permutation434 hz
    mixedMoment B raw31575step0 raw31575step0Labels = mixedMoment B raw31575step1 raw31575step1Labels := by
      have ha : raw31575step1 = (fun i j => raw31575step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31575step1 raw31575step0; decide +kernel
      have hl : raw31575step1Labels = raw31575step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31575step0 raw31575step0Labels permutation33 permutation3
    mixedMoment B raw31575step1 raw31575step1Labels = mixedMoment B raw31575step2 raw31575step2Labels := by
      have ha : raw31575step2 = raw31575step1 := by apply Matrix.ext; unfold raw31575step2 raw31575step1; decide +kernel
      have hl : raw31575step1Labels = labelEmbedding6 ∘ raw31575step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31575step1 raw31575step1Labels raw31575step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4769 node4769Labels := by rfl

def raw31576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31576step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31576step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31576step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31576 raw31576Labels = mixedMoment B node4706 node4706Labels := by
  calc
    mixedMoment B raw31576 raw31576Labels = mixedMoment B raw31576step0 raw31576step0Labels := by
      have ha : raw31576step0 = (fun i j => raw31576 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31576step0 raw31576; decide +kernel
      have hl : raw31576step0Labels = raw31576Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31576 raw31576Labels permutation201 permutation3
    mixedMoment B raw31576step0 raw31576step0Labels = mixedMoment B raw31576step1 raw31576step1Labels := by
      have ha : raw31576step1 = raw31576step0 := by apply Matrix.ext; unfold raw31576step1 raw31576step0; decide +kernel
      have hl : raw31576step0Labels = labelEmbedding6 ∘ raw31576step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31576step0 raw31576step0Labels raw31576step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4706 node4706Labels := by rfl

def raw31577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -2, -1], ![1, 0, -1]]
def raw31577step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw31577step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31577step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw31577step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31577 raw31577Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw31577 raw31577Labels = mixedMoment B raw31577step0 raw31577step0Labels := by
      have hz : ∀ j, raw31577 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31577step0 = (fun i j => raw31577 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31577step0 raw31577; decide +kernel
      have hl : raw31577step0Labels = raw31577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31577 raw31577Labels permutation434 hz
    mixedMoment B raw31577step0 raw31577step0Labels = mixedMoment B raw31577step1 raw31577step1Labels := by
      have ha : raw31577step1 = (fun i j => raw31577step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31577step1 raw31577step0; decide +kernel
      have hl : raw31577step1Labels = raw31577step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31577step0 raw31577step0Labels permutation33 permutation3
    mixedMoment B raw31577step1 raw31577step1Labels = mixedMoment B raw31577step2 raw31577step2Labels := by
      have ha : raw31577step2 = raw31577step1 := by apply Matrix.ext; unfold raw31577step2 raw31577step1; decide +kernel
      have hl : raw31577step1Labels = labelEmbedding6 ∘ raw31577step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31577step1 raw31577step1Labels raw31577step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw31578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -2, -1]]
def raw31578step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31578step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31578step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31578step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31578 raw31578Labels = mixedMoment B node4204 node4204Labels := by
  calc
    mixedMoment B raw31578 raw31578Labels = mixedMoment B raw31578step0 raw31578step0Labels := by
      have hz : ∀ j, raw31578 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31578step0 = (fun i j => raw31578 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31578step0 raw31578; decide +kernel
      have hl : raw31578step0Labels = raw31578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31578 raw31578Labels permutation434 hz
    mixedMoment B raw31578step0 raw31578step0Labels = mixedMoment B raw31578step1 raw31578step1Labels := by
      have ha : raw31578step1 = (fun i j => raw31578step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31578step1 raw31578step0; decide +kernel
      have hl : raw31578step1Labels = raw31578step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31578step0 raw31578step0Labels permutation32 permutation3
    mixedMoment B raw31578step1 raw31578step1Labels = mixedMoment B raw31578step2 raw31578step2Labels := by
      have ha : raw31578step2 = raw31578step1 := by apply Matrix.ext; unfold raw31578step2 raw31578step1; decide +kernel
      have hl : raw31578step1Labels = labelEmbedding6 ∘ raw31578step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31578step1 raw31578step1Labels raw31578step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4204 node4204Labels := by rfl

def raw31579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![3, -2, -1]]
def raw31579step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31579step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31579step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31579step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31579step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31579 raw31579Labels = mixedMoment B node4637 node4637Labels := by
  calc
    mixedMoment B raw31579 raw31579Labels = mixedMoment B raw31579step0 raw31579step0Labels := by
      have hz : ∀ j, raw31579 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31579step0 = (fun i j => raw31579 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31579step0 raw31579; decide +kernel
      have hl : raw31579step0Labels = raw31579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31579 raw31579Labels permutation434 hz
    mixedMoment B raw31579step0 raw31579step0Labels = mixedMoment B raw31579step1 raw31579step1Labels := by
      have ha : raw31579step1 = (fun i j => raw31579step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31579step1 raw31579step0; decide +kernel
      have hl : raw31579step1Labels = raw31579step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31579step0 raw31579step0Labels permutation32 permutation3
    mixedMoment B raw31579step1 raw31579step1Labels = mixedMoment B raw31579step2 raw31579step2Labels := by
      have ha : raw31579step2 = raw31579step1 := by apply Matrix.ext; unfold raw31579step2 raw31579step1; decide +kernel
      have hl : raw31579step1Labels = labelEmbedding6 ∘ raw31579step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31579step1 raw31579step1Labels raw31579step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4637 node4637Labels := by rfl

def raw31580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![3, -2, -1]]
def raw31580step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31580step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31580step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31580step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31580 raw31580Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw31580 raw31580Labels = mixedMoment B raw31580step0 raw31580step0Labels := by
      have hz : ∀ j, raw31580 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31580step0 = (fun i j => raw31580 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31580step0 raw31580; decide +kernel
      have hl : raw31580step0Labels = raw31580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31580 raw31580Labels permutation434 hz
    mixedMoment B raw31580step0 raw31580step0Labels = mixedMoment B raw31580step1 raw31580step1Labels := by
      have ha : raw31580step1 = (fun i j => raw31580step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31580step1 raw31580step0; decide +kernel
      have hl : raw31580step1Labels = raw31580step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31580step0 raw31580step0Labels permutation32 permutation3
    mixedMoment B raw31580step1 raw31580step1Labels = mixedMoment B raw31580step2 raw31580step2Labels := by
      have ha : raw31580step2 = raw31580step1 := by apply Matrix.ext; unfold raw31580step2 raw31580step1; decide +kernel
      have hl : raw31580step1Labels = labelEmbedding6 ∘ raw31580step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31580step1 raw31580step1Labels raw31580step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4769 node4769Labels := by rfl

def raw31581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31581step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31581step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31581 raw31581Labels = mixedMoment B node4706 node4706Labels := by
  calc
    mixedMoment B raw31581 raw31581Labels = mixedMoment B raw31581step0 raw31581step0Labels := by
      have ha : raw31581step0 = (fun i j => raw31581 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31581step0 raw31581; decide +kernel
      have hl : raw31581step0Labels = raw31581Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31581 raw31581Labels permutation200 permutation3
    mixedMoment B raw31581step0 raw31581step0Labels = mixedMoment B raw31581step1 raw31581step1Labels := by
      have ha : raw31581step1 = raw31581step0 := by apply Matrix.ext; unfold raw31581step1 raw31581step0; decide +kernel
      have hl : raw31581step0Labels = labelEmbedding6 ∘ raw31581step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31581step0 raw31581step0Labels raw31581step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4706 node4706Labels := by rfl

def raw31582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31582step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31582step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31582 raw31582Labels = mixedMoment B node3694 node3694Labels := by
  calc
    mixedMoment B raw31582 raw31582Labels = mixedMoment B raw31582step0 raw31582step0Labels := by
      have hz : ∀ j, raw31582 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31582step0 = (fun i j => raw31582 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31582step0 raw31582; decide +kernel
      have hl : raw31582step0Labels = raw31582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31582 raw31582Labels permutation434 hz
    mixedMoment B raw31582step0 raw31582step0Labels = mixedMoment B raw31582step1 raw31582step1Labels := by
      have ha : raw31582step1 = (fun i j => raw31582step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31582step1 raw31582step0; decide +kernel
      have hl : raw31582step1Labels = raw31582step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31582step0 raw31582step0Labels permutation32 permutation3
    _ = mixedMoment B node3694 node3694Labels := by rfl

def raw31583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31583Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31583step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31583step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31583step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31583 raw31583Labels = mixedMoment B node3824 node3824Labels := by
  calc
    mixedMoment B raw31583 raw31583Labels = mixedMoment B raw31583step0 raw31583step0Labels := by
      have hz : ∀ j, raw31583 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31583step0 = (fun i j => raw31583 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31583step0 raw31583; decide +kernel
      have hl : raw31583step0Labels = raw31583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31583 raw31583Labels permutation434 hz
    mixedMoment B raw31583step0 raw31583step0Labels = mixedMoment B raw31583step1 raw31583step1Labels := by
      have ha : raw31583step1 = (fun i j => raw31583step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31583step1 raw31583step0; decide +kernel
      have hl : raw31583step1Labels = raw31583step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31583step0 raw31583step0Labels permutation32 permutation3
    _ = mixedMoment B node3824 node3824Labels := by rfl

def raw31584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31584Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31584step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31584 raw31584Labels = mixedMoment B node3779 node3779Labels := by
  calc
    mixedMoment B raw31584 raw31584Labels = mixedMoment B raw31584step0 raw31584step0Labels := by
      have ha : raw31584step0 = (fun i j => raw31584 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31584step0 raw31584; decide +kernel
      have hl : raw31584step0Labels = raw31584Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31584 raw31584Labels permutation200 permutation3
    _ = mixedMoment B node3779 node3779Labels := by rfl

def raw31585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw31585step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31585step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw31585step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31585 raw31585Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw31585 raw31585Labels = mixedMoment B raw31585step0 raw31585step0Labels := by
      have hz : ∀ j, raw31585 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31585step0 = (fun i j => raw31585 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31585step0 raw31585; decide +kernel
      have hl : raw31585step0Labels = raw31585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31585 raw31585Labels permutation434 hz
    mixedMoment B raw31585step0 raw31585step0Labels = mixedMoment B raw31585step1 raw31585step1Labels := by
      have ha : raw31585step1 = (fun i j => raw31585step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31585step1 raw31585step0; decide +kernel
      have hl : raw31585step1Labels = raw31585step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31585step0 raw31585step0Labels permutation33 permutation3
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw31586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw31586step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw31586step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31586 raw31586Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw31586 raw31586Labels = mixedMoment B raw31586step0 raw31586step0Labels := by
      have hz : ∀ j, raw31586 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31586step0 = (fun i j => raw31586 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31586step0 raw31586; decide +kernel
      have hl : raw31586step0Labels = raw31586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31586 raw31586Labels permutation434 hz
    mixedMoment B raw31586step0 raw31586step0Labels = mixedMoment B raw31586step1 raw31586step1Labels := by
      have ha : raw31586step1 = (fun i j => raw31586step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31586step1 raw31586step0; decide +kernel
      have hl : raw31586step1Labels = raw31586step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31586step0 raw31586step0Labels permutation32 permutation3
    _ = mixedMoment B node2244 node2244Labels := by rfl

def raw31587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31587Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31587step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw31587step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31587 raw31587Labels = mixedMoment B node725 node725Labels := by
  calc
    mixedMoment B raw31587 raw31587Labels = mixedMoment B raw31587step0 raw31587step0Labels := by
      have hz : ∀ j, raw31587 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31587step0 = (fun i j => raw31587 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31587step0 raw31587; decide +kernel
      have hl : raw31587step0Labels = raw31587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31587 raw31587Labels permutation434 hz
    mixedMoment B raw31587step0 raw31587step0Labels = mixedMoment B raw31587step1 raw31587step1Labels := by
      have ha : raw31587step1 = (fun i j => raw31587step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31587step1 raw31587step0; decide +kernel
      have hl : raw31587step1Labels = raw31587step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31587step0 raw31587step0Labels permutation32 permutation3
    _ = mixedMoment B node725 node725Labels := by rfl

def raw31588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31588Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31588step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw31588step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31588 raw31588Labels = mixedMoment B node1782 node1782Labels := by
  calc
    mixedMoment B raw31588 raw31588Labels = mixedMoment B raw31588step0 raw31588step0Labels := by
      have hz : ∀ j, raw31588 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31588step0 = (fun i j => raw31588 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31588step0 raw31588; decide +kernel
      have hl : raw31588step0Labels = raw31588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31588 raw31588Labels permutation434 hz
    mixedMoment B raw31588step0 raw31588step0Labels = mixedMoment B raw31588step1 raw31588step1Labels := by
      have ha : raw31588step1 = (fun i j => raw31588step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31588step1 raw31588step0; decide +kernel
      have hl : raw31588step1Labels = raw31588step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31588step0 raw31588step0Labels permutation32 permutation3
    _ = mixedMoment B node1782 node1782Labels := by rfl

def raw31589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31589Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw31589step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31589 raw31589Labels = mixedMoment B node1871 node1871Labels := by
  calc
    mixedMoment B raw31589 raw31589Labels = mixedMoment B raw31589step0 raw31589step0Labels := by
      have ha : raw31589step0 = (fun i j => raw31589 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31589step0 raw31589; decide +kernel
      have hl : raw31589step0Labels = raw31589Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31589 raw31589Labels permutation200 permutation3
    _ = mixedMoment B node1871 node1871Labels := by rfl

def raw31590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw31590step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw31590step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31590 raw31590Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw31590 raw31590Labels = mixedMoment B raw31590step0 raw31590step0Labels := by
      have hz : ∀ j, raw31590 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31590step0 = (fun i j => raw31590 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31590step0 raw31590; decide +kernel
      have hl : raw31590step0Labels = raw31590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31590 raw31590Labels permutation434 hz
    mixedMoment B raw31590step0 raw31590step0Labels = mixedMoment B raw31590step1 raw31590step1Labels := by
      have ha : raw31590step1 = (fun i j => raw31590step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31590step1 raw31590step0; decide +kernel
      have hl : raw31590step1Labels = raw31590step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31590step0 raw31590step0Labels permutation36 permutation3
    _ = mixedMoment B node2054 node2054Labels := by rfl

def raw31591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31591Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31591step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31591 raw31591Labels = mixedMoment B node704 node704Labels := by
  calc
    mixedMoment B raw31591 raw31591Labels = mixedMoment B raw31591step0 raw31591step0Labels := by
      have ha : raw31591step0 = (fun i j => raw31591 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31591step0 raw31591; decide +kernel
      have hl : raw31591step0Labels = raw31591Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31591 raw31591Labels permutation152 permutation3
    _ = mixedMoment B node704 node704Labels := by rfl

def raw31592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31592Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31592step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31592step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31592 raw31592Labels = mixedMoment B node1764 node1764Labels := by
  calc
    mixedMoment B raw31592 raw31592Labels = mixedMoment B raw31592step0 raw31592step0Labels := by
      have ha : raw31592step0 = (fun i j => raw31592 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31592step0 raw31592; decide +kernel
      have hl : raw31592step0Labels = raw31592Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31592 raw31592Labels permutation152 permutation3
    _ = mixedMoment B node1764 node1764Labels := by rfl

def raw31593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw31593Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31593step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31593 raw31593Labels = mixedMoment B node1967 node1967Labels := by
  calc
    mixedMoment B raw31593 raw31593Labels = mixedMoment B raw31593step0 raw31593step0Labels := by
      have ha : raw31593step0 = (fun i j => raw31593 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31593step0 raw31593; decide +kernel
      have hl : raw31593step0Labels = raw31593Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31593 raw31593Labels permutation152 permutation3
    _ = mixedMoment B node1967 node1967Labels := by rfl

def raw31594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw31594Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw31594step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31594 raw31594Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw31594 raw31594Labels = mixedMoment B raw31594step0 raw31594step0Labels := by
      have ha : raw31594step0 = (fun i j => raw31594 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31594step0 raw31594; decide +kernel
      have hl : raw31594step0Labels = raw31594Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31594 raw31594Labels permutation156 permutation3
    _ = mixedMoment B node2020 node2020Labels := by rfl

def raw31595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31595Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -2, -1], ![2, -1, -1]]
def raw31595step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31595step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31595 raw31595Labels = mixedMoment B node707 node707Labels := by
  calc
    mixedMoment B raw31595 raw31595Labels = mixedMoment B raw31595step0 raw31595step0Labels := by
      have hz : ∀ j, raw31595 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31595step0 = (fun i j => raw31595 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31595step0 raw31595; decide +kernel
      have hl : raw31595step0Labels = raw31595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31595 raw31595Labels permutation434 hz
    mixedMoment B raw31595step0 raw31595step0Labels = mixedMoment B raw31595step1 raw31595step1Labels := by
      have ha : raw31595step1 = (fun i j => raw31595step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31595step1 raw31595step0; decide +kernel
      have hl : raw31595step1Labels = raw31595step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31595step0 raw31595step0Labels permutation33 permutation3
    _ = mixedMoment B node707 node707Labels := by rfl

def raw31596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31596Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![3, -2, -1], ![2, -1, -1]]
def raw31596step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31596step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31596 raw31596Labels = mixedMoment B node1766 node1766Labels := by
  calc
    mixedMoment B raw31596 raw31596Labels = mixedMoment B raw31596step0 raw31596step0Labels := by
      have hz : ∀ j, raw31596 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31596step0 = (fun i j => raw31596 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31596step0 raw31596; decide +kernel
      have hl : raw31596step0Labels = raw31596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31596 raw31596Labels permutation434 hz
    mixedMoment B raw31596step0 raw31596step0Labels = mixedMoment B raw31596step1 raw31596step1Labels := by
      have ha : raw31596step1 = (fun i j => raw31596step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31596step1 raw31596step0; decide +kernel
      have hl : raw31596step1Labels = raw31596step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31596step0 raw31596step0Labels permutation33 permutation3
    _ = mixedMoment B node1766 node1766Labels := by rfl

def raw31597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31597Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![3, -2, -1], ![2, -1, -1]]
def raw31597step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31597step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31597 raw31597Labels = mixedMoment B node1969 node1969Labels := by
  calc
    mixedMoment B raw31597 raw31597Labels = mixedMoment B raw31597step0 raw31597step0Labels := by
      have hz : ∀ j, raw31597 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31597step0 = (fun i j => raw31597 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31597step0 raw31597; decide +kernel
      have hl : raw31597step0Labels = raw31597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31597 raw31597Labels permutation434 hz
    mixedMoment B raw31597step0 raw31597step0Labels = mixedMoment B raw31597step1 raw31597step1Labels := by
      have ha : raw31597step1 = (fun i j => raw31597step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31597step1 raw31597step0; decide +kernel
      have hl : raw31597step1Labels = raw31597step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31597step0 raw31597step0Labels permutation33 permutation3
    _ = mixedMoment B node1969 node1969Labels := by rfl

def raw31598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw31598Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31598step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31598 raw31598Labels = mixedMoment B node1860 node1860Labels := by
  calc
    mixedMoment B raw31598 raw31598Labels = mixedMoment B raw31598step0 raw31598step0Labels := by
      have ha : raw31598step0 = (fun i j => raw31598 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31598step0 raw31598; decide +kernel
      have hl : raw31598step0Labels = raw31598Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31598 raw31598Labels permutation201 permutation3
    _ = mixedMoment B node1860 node1860Labels := by rfl

def raw31599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw31599Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -2, -1], ![1, 0, -1]]
def raw31599step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw31599step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31599 raw31599Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw31599 raw31599Labels = mixedMoment B raw31599step0 raw31599step0Labels := by
      have hz : ∀ j, raw31599 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31599step0 = (fun i j => raw31599 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31599step0 raw31599; decide +kernel
      have hl : raw31599step0Labels = raw31599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31599 raw31599Labels permutation434 hz
    mixedMoment B raw31599step0 raw31599step0Labels = mixedMoment B raw31599step1 raw31599step1Labels := by
      have ha : raw31599step1 = (fun i j => raw31599step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31599step1 raw31599step0; decide +kernel
      have hl : raw31599step1Labels = raw31599step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31599step0 raw31599step0Labels permutation33 permutation3
    _ = mixedMoment B node2022 node2022Labels := by rfl

def raw31600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31600Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -2, -1]]
def raw31600step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31600step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31600 raw31600Labels = mixedMoment B node707 node707Labels := by
  calc
    mixedMoment B raw31600 raw31600Labels = mixedMoment B raw31600step0 raw31600step0Labels := by
      have hz : ∀ j, raw31600 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31600step0 = (fun i j => raw31600 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31600step0 raw31600; decide +kernel
      have hl : raw31600step0Labels = raw31600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31600 raw31600Labels permutation434 hz
    mixedMoment B raw31600step0 raw31600step0Labels = mixedMoment B raw31600step1 raw31600step1Labels := by
      have ha : raw31600step1 = (fun i j => raw31600step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31600step1 raw31600step0; decide +kernel
      have hl : raw31600step1Labels = raw31600step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31600step0 raw31600step0Labels permutation32 permutation3
    _ = mixedMoment B node707 node707Labels := by rfl

def raw31601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31601Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![3, -2, -1]]
def raw31601step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31601step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31601 raw31601Labels = mixedMoment B node1766 node1766Labels := by
  calc
    mixedMoment B raw31601 raw31601Labels = mixedMoment B raw31601step0 raw31601step0Labels := by
      have hz : ∀ j, raw31601 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31601step0 = (fun i j => raw31601 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31601step0 raw31601; decide +kernel
      have hl : raw31601step0Labels = raw31601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31601 raw31601Labels permutation434 hz
    mixedMoment B raw31601step0 raw31601step0Labels = mixedMoment B raw31601step1 raw31601step1Labels := by
      have ha : raw31601step1 = (fun i j => raw31601step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31601step1 raw31601step0; decide +kernel
      have hl : raw31601step1Labels = raw31601step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31601step0 raw31601step0Labels permutation32 permutation3
    _ = mixedMoment B node1766 node1766Labels := by rfl

def raw31602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31602Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![3, -2, -1]]
def raw31602step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw31602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31602 raw31602Labels = mixedMoment B node1969 node1969Labels := by
  calc
    mixedMoment B raw31602 raw31602Labels = mixedMoment B raw31602step0 raw31602step0Labels := by
      have hz : ∀ j, raw31602 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31602step0 = (fun i j => raw31602 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31602step0 raw31602; decide +kernel
      have hl : raw31602step0Labels = raw31602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31602 raw31602Labels permutation434 hz
    mixedMoment B raw31602step0 raw31602step0Labels = mixedMoment B raw31602step1 raw31602step1Labels := by
      have ha : raw31602step1 = (fun i j => raw31602step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31602step1 raw31602step0; decide +kernel
      have hl : raw31602step1Labels = raw31602step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31602step0 raw31602step0Labels permutation32 permutation3
    _ = mixedMoment B node1969 node1969Labels := by rfl

def raw31603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31603Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31603step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31603 raw31603Labels = mixedMoment B node1860 node1860Labels := by
  calc
    mixedMoment B raw31603 raw31603Labels = mixedMoment B raw31603step0 raw31603step0Labels := by
      have ha : raw31603step0 = (fun i j => raw31603 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31603step0 raw31603; decide +kernel
      have hl : raw31603step0Labels = raw31603Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31603 raw31603Labels permutation200 permutation3
    _ = mixedMoment B node1860 node1860Labels := by rfl

def raw31604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw31604step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31604step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw31604step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31604step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw31604step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31604 raw31604Labels = mixedMoment B node4427 node4427Labels := by
  calc
    mixedMoment B raw31604 raw31604Labels = mixedMoment B raw31604step0 raw31604step0Labels := by
      have hz : ∀ j, raw31604 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31604step0 = (fun i j => raw31604 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31604step0 raw31604; decide +kernel
      have hl : raw31604step0Labels = raw31604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31604 raw31604Labels permutation434 hz
    mixedMoment B raw31604step0 raw31604step0Labels = mixedMoment B raw31604step1 raw31604step1Labels := by
      have ha : raw31604step1 = (fun i j => raw31604step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31604step1 raw31604step0; decide +kernel
      have hl : raw31604step1Labels = raw31604step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31604step0 raw31604step0Labels permutation35 permutation4
    mixedMoment B raw31604step1 raw31604step1Labels = mixedMoment B raw31604step2 raw31604step2Labels := by
      have ha : raw31604step2 = -raw31604step1 := by apply Matrix.ext; change ∀ i j, raw31604step2 i j = -(raw31604step1 i j); unfold raw31604step2 raw31604step1; decide +kernel
      have hl : raw31604step2Labels = raw31604step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31604step2 raw31604step2Labels = mixedMoment B raw31604step3 raw31604step3Labels := by
      have ha : raw31604step3 = raw31604step2 := by apply Matrix.ext; unfold raw31604step3 raw31604step2; decide +kernel
      have hl : raw31604step2Labels = labelEmbedding7 ∘ raw31604step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31604step2 raw31604step2Labels raw31604step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4427 node4427Labels := by rfl

def raw31605 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw31605step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31605step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw31605step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31605 raw31605Labels = mixedMoment B node4785 node4785Labels := by
  calc
    mixedMoment B raw31605 raw31605Labels = mixedMoment B raw31605step0 raw31605step0Labels := by
      have ha : raw31605step0 = (fun i j => raw31605 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31605step0 raw31605; decide +kernel
      have hl : raw31605step0Labels = raw31605Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31605 raw31605Labels permutation158 permutation6
    mixedMoment B raw31605step0 raw31605step0Labels = mixedMoment B raw31605step1 raw31605step1Labels := by
      have ha : raw31605step1 = raw31605step0 := by apply Matrix.ext; unfold raw31605step1 raw31605step0; decide +kernel
      have hl : raw31605step0Labels = labelEmbedding9 ∘ raw31605step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31605step0 raw31605step0Labels raw31605step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4785 node4785Labels := by rfl

def raw31606 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw31606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw31606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw31606step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw31606step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31606 raw31606Labels = mixedMoment B node4821 node4821Labels := by
  calc
    mixedMoment B raw31606 raw31606Labels = mixedMoment B raw31606step0 raw31606step0Labels := by
      have hz : ∀ j, raw31606 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31606step0 = (fun i j => raw31606 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31606step0 raw31606; decide +kernel
      have hl : raw31606step0Labels = raw31606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31606 raw31606Labels permutation434 hz
    mixedMoment B raw31606step0 raw31606step0Labels = mixedMoment B raw31606step1 raw31606step1Labels := by
      have ha : raw31606step1 = (fun i j => raw31606step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31606step1 raw31606step0; decide +kernel
      have hl : raw31606step1Labels = raw31606step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31606step0 raw31606step0Labels permutation32 permutation6
    mixedMoment B raw31606step1 raw31606step1Labels = mixedMoment B raw31606step2 raw31606step2Labels := by
      have ha : raw31606step2 = raw31606step1 := by apply Matrix.ext; unfold raw31606step2 raw31606step1; decide +kernel
      have hl : raw31606step1Labels = labelEmbedding9 ∘ raw31606step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31606step1 raw31606step1Labels raw31606step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4821 node4821Labels := by rfl

def raw31607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31607step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31607step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31607step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31607step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31607step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31607 raw31607Labels = mixedMoment B node4415 node4415Labels := by
  calc
    mixedMoment B raw31607 raw31607Labels = mixedMoment B raw31607step0 raw31607step0Labels := by
      have ha : raw31607step0 = (fun i j => raw31607 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31607step0 raw31607; decide +kernel
      have hl : raw31607step0Labels = raw31607Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31607 raw31607Labels permutation152 permutation4
    mixedMoment B raw31607step0 raw31607step0Labels = mixedMoment B raw31607step1 raw31607step1Labels := by
      have ha : raw31607step1 = -raw31607step0 := by apply Matrix.ext; change ∀ i j, raw31607step1 i j = -(raw31607step0 i j); unfold raw31607step1 raw31607step0; decide +kernel
      have hl : raw31607step1Labels = raw31607step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31607step1 raw31607step1Labels = mixedMoment B raw31607step2 raw31607step2Labels := by
      have ha : raw31607step2 = raw31607step1 := by apply Matrix.ext; unfold raw31607step2 raw31607step1; decide +kernel
      have hl : raw31607step1Labels = labelEmbedding7 ∘ raw31607step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31607step1 raw31607step1Labels raw31607step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4415 node4415Labels := by rfl

def raw31608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31608step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31608step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31608step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw31608step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31608 raw31608Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw31608 raw31608Labels = mixedMoment B raw31608step0 raw31608step0Labels := by
      have hz : ∀ j, raw31608 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31608step0 = (fun i j => raw31608 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31608step0 raw31608; decide +kernel
      have hl : raw31608step0Labels = raw31608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31608 raw31608Labels permutation434 hz
    mixedMoment B raw31608step0 raw31608step0Labels = mixedMoment B raw31608step1 raw31608step1Labels := by
      have ha : raw31608step1 = (fun i j => raw31608step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31608step1 raw31608step0; decide +kernel
      have hl : raw31608step1Labels = raw31608step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31608step0 raw31608step0Labels permutation32 permutation4
    mixedMoment B raw31608step1 raw31608step1Labels = mixedMoment B raw31608step2 raw31608step2Labels := by
      have ha : raw31608step2 = -raw31608step1 := by apply Matrix.ext; change ∀ i j, raw31608step2 i j = -(raw31608step1 i j); unfold raw31608step2 raw31608step1; decide +kernel
      have hl : raw31608step2Labels = raw31608step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31608step2 raw31608step2Labels = mixedMoment B raw31608step3 raw31608step3Labels := by
      have ha : raw31608step3 = raw31608step2 := by apply Matrix.ext; unfold raw31608step3 raw31608step2; decide +kernel
      have hl : raw31608step2Labels = labelEmbedding7 ∘ raw31608step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31608step2 raw31608step2Labels raw31608step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4419 node4419Labels := by rfl

def raw31609 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31609step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31609step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31609 raw31609Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw31609 raw31609Labels = mixedMoment B raw31609step0 raw31609step0Labels := by
      have ha : raw31609step0 = (fun i j => raw31609 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31609step0 raw31609; decide +kernel
      have hl : raw31609step0Labels = raw31609Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31609 raw31609Labels permutation158 permutation6
    mixedMoment B raw31609step0 raw31609step0Labels = mixedMoment B raw31609step1 raw31609step1Labels := by
      have ha : raw31609step1 = raw31609step0 := by apply Matrix.ext; unfold raw31609step1 raw31609step0; decide +kernel
      have hl : raw31609step0Labels = labelEmbedding9 ∘ raw31609step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31609step0 raw31609step0Labels raw31609step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4782 node4782Labels := by rfl

def raw31610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw31610Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31610step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31610 raw31610Labels = mixedMoment B node1990 node1990Labels := by
  calc
    mixedMoment B raw31610 raw31610Labels = mixedMoment B raw31610step0 raw31610step0Labels := by
      have ha : raw31610step0 = (fun i j => raw31610 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31610step0 raw31610; decide +kernel
      have hl : raw31610step0Labels = raw31610Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31610 raw31610Labels permutation159 permutation2
    _ = mixedMoment B node1990 node1990Labels := by rfl

def raw31611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw31611Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31611step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31611step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31611 raw31611Labels = mixedMoment B node3367 node3367Labels := by
  calc
    mixedMoment B raw31611 raw31611Labels = mixedMoment B raw31611step0 raw31611step0Labels := by
      have ha : raw31611step0 = (fun i j => raw31611 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31611step0 raw31611; decide +kernel
      have hl : raw31611step0Labels = raw31611Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31611 raw31611Labels permutation159 permutation2
    _ = mixedMoment B node3367 node3367Labels := by rfl

def raw31612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw31612Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31612step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31612 raw31612Labels = mixedMoment B node3499 node3499Labels := by
  calc
    mixedMoment B raw31612 raw31612Labels = mixedMoment B raw31612step0 raw31612step0Labels := by
      have ha : raw31612step0 = (fun i j => raw31612 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31612step0 raw31612; decide +kernel
      have hl : raw31612step0Labels = raw31612Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31612 raw31612Labels permutation153 permutation2
    _ = mixedMoment B node3499 node3499Labels := by rfl

def raw31613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw31613Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31613step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31613step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31613 raw31613Labels = mixedMoment B node3429 node3429Labels := by
  calc
    mixedMoment B raw31613 raw31613Labels = mixedMoment B raw31613step0 raw31613step0Labels := by
      have ha : raw31613step0 = (fun i j => raw31613 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31613step0 raw31613; decide +kernel
      have hl : raw31613step0Labels = raw31613Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31613 raw31613Labels permutation201 permutation2
    _ = mixedMoment B node3429 node3429Labels := by rfl

def raw31614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw31614Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw31614step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31614 raw31614Labels = mixedMoment B node3515 node3515Labels := by
  calc
    mixedMoment B raw31614 raw31614Labels = mixedMoment B raw31614step0 raw31614step0Labels := by
      have ha : raw31614step0 = (fun i j => raw31614 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31614step0 raw31614; decide +kernel
      have hl : raw31614step0Labels = raw31614Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31614 raw31614Labels permutation158 permutation2
    _ = mixedMoment B node3515 node3515Labels := by rfl

def raw31615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw31615Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw31615step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31615 raw31615Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw31615 raw31615Labels = mixedMoment B raw31615step0 raw31615step0Labels := by
      have ha : raw31615step0 = (fun i j => raw31615 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31615step0 raw31615; decide +kernel
      have hl : raw31615step0Labels = raw31615Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31615 raw31615Labels permutation159 permutation2
    _ = mixedMoment B node3514 node3514Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
