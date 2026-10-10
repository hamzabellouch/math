import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw20736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20736Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20736step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20736 raw20736Labels = mixedMoment B node635 node635Labels := by
  calc
    mixedMoment B raw20736 raw20736Labels = mixedMoment B raw20736step0 raw20736step0Labels := by
      have hz : ∀ j, raw20736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20736step0 = (fun i j => raw20736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20736step0 raw20736; decide +kernel
      have hl : raw20736step0Labels = raw20736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20736 raw20736Labels permutation346 hz
    mixedMoment B raw20736step0 raw20736step0Labels = mixedMoment B raw20736step1 raw20736step1Labels := by
      have hz : ∀ j, raw20736step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20736step1 = (fun i j => raw20736step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20736step1 raw20736step0; decide +kernel
      have hl : raw20736step1Labels = raw20736step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20736step0 raw20736step0Labels permutation56 hz
    _ = mixedMoment B node635 node635Labels := by rfl

def raw20737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20737Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20737step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20737step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20737step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20737 raw20737Labels = mixedMoment B node633 node633Labels := by
  calc
    mixedMoment B raw20737 raw20737Labels = mixedMoment B raw20737step0 raw20737step0Labels := by
      have hz : ∀ j, raw20737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20737step0 = (fun i j => raw20737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20737step0 raw20737; decide +kernel
      have hl : raw20737step0Labels = raw20737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20737 raw20737Labels permutation346 hz
    mixedMoment B raw20737step0 raw20737step0Labels = mixedMoment B raw20737step1 raw20737step1Labels := by
      have hz : ∀ j, raw20737step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20737step1 = (fun i j => raw20737step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20737step1 raw20737step0; decide +kernel
      have hl : raw20737step1Labels = raw20737step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20737step0 raw20737step0Labels permutation56 hz
    _ = mixedMoment B node633 node633Labels := by rfl

def raw20738 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-1, 1], ![1, -1], ![2, -2]]
def raw20738Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20738step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![2, -2]]
def raw20738step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20738step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw20738step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20738 raw20738Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw20738 raw20738Labels = mixedMoment B raw20738step0 raw20738step0Labels := by
      have hz : ∀ j, raw20738 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20738step0 = (fun i j => raw20738 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20738step0 raw20738; decide +kernel
      have hl : raw20738step0Labels = raw20738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20738 raw20738Labels permutation346 hz
    mixedMoment B raw20738step0 raw20738step0Labels = mixedMoment B raw20738step1 raw20738step1Labels := by
      have hz : ∀ j, raw20738step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20738step1 = (fun i j => raw20738step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20738step1 raw20738step0; decide +kernel
      have hl : raw20738step1Labels = raw20738step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20738step0 raw20738step0Labels permutation56 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw20739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20739Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20739step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw20739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20739step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20739 raw20739Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw20739 raw20739Labels = mixedMoment B raw20739step0 raw20739step0Labels := by
      have hz : ∀ j, raw20739 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20739step0 = (fun i j => raw20739 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20739step0 raw20739; decide +kernel
      have hl : raw20739step0Labels = raw20739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20739 raw20739Labels permutation346 hz
    mixedMoment B raw20739step0 raw20739step0Labels = mixedMoment B raw20739step1 raw20739step1Labels := by
      have ha : raw20739step1 = (fun i j => raw20739step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20739step1 raw20739step0; decide +kernel
      have hl : raw20739step1Labels = raw20739step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20739step0 raw20739step0Labels permutation151 permutation2
    mixedMoment B raw20739step1 raw20739step1Labels = mixedMoment B raw20739step2 raw20739step2Labels := by
      have ha : raw20739step2 = -raw20739step1 := by apply Matrix.ext; change ∀ i j, raw20739step2 i j = -(raw20739step1 i j); unfold raw20739step2 raw20739step1; decide +kernel
      have hl : raw20739step2Labels = raw20739step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2482 node2482Labels := by rfl

def raw20740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20740Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20740 raw20740Labels = mixedMoment B node1148 node1148Labels := by
  calc
    mixedMoment B raw20740 raw20740Labels = mixedMoment B raw20740step0 raw20740step0Labels := by
      have ha : raw20740step0 = (fun i j => raw20740 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20740step0 raw20740; decide +kernel
      have hl : raw20740step0Labels = raw20740Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20740 raw20740Labels permutation158 permutation2
    _ = mixedMoment B node1148 node1148Labels := by rfl

def raw20741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20741step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20741 raw20741Labels = mixedMoment B node1159 node1159Labels := by
  calc
    mixedMoment B raw20741 raw20741Labels = mixedMoment B raw20741step0 raw20741step0Labels := by
      have hz : ∀ j, raw20741 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20741step0 = (fun i j => raw20741 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20741step0 raw20741; decide +kernel
      have hl : raw20741step0Labels = raw20741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20741 raw20741Labels permutation346 hz
    _ = mixedMoment B node1159 node1159Labels := by rfl

def raw20742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20742 raw20742Labels = mixedMoment B node1154 node1154Labels := by
  calc
    mixedMoment B raw20742 raw20742Labels = mixedMoment B raw20742step0 raw20742step0Labels := by
      have hz : ∀ j, raw20742 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20742step0 = (fun i j => raw20742 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20742step0 raw20742; decide +kernel
      have hl : raw20742step0Labels = raw20742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20742 raw20742Labels permutation346 hz
    _ = mixedMoment B node1154 node1154Labels := by rfl

def raw20743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20743Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20743step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw20743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20743 raw20743Labels = mixedMoment B node1115 node1115Labels := by
  calc
    mixedMoment B raw20743 raw20743Labels = mixedMoment B raw20743step0 raw20743step0Labels := by
      have hz : ∀ j, raw20743 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20743step0 = (fun i j => raw20743 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20743step0 raw20743; decide +kernel
      have hl : raw20743step0Labels = raw20743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20743 raw20743Labels permutation346 hz
    mixedMoment B raw20743step0 raw20743step0Labels = mixedMoment B raw20743step1 raw20743step1Labels := by
      have ha : raw20743step1 = (fun i j => raw20743step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20743step1 raw20743step0; decide +kernel
      have hl : raw20743step1Labels = raw20743step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20743step0 raw20743step0Labels permutation151 permutation2
    mixedMoment B raw20743step1 raw20743step1Labels = mixedMoment B raw20743step2 raw20743step2Labels := by
      have ha : raw20743step2 = -raw20743step1 := by apply Matrix.ext; change ∀ i j, raw20743step2 i j = -(raw20743step1 i j); unfold raw20743step2 raw20743step1; decide +kernel
      have hl : raw20743step2Labels = raw20743step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1115 node1115Labels := by rfl

def raw20744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20744Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20744step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20744step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20744step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20744 raw20744Labels = mixedMoment B node2517 node2517Labels := by
  calc
    mixedMoment B raw20744 raw20744Labels = mixedMoment B raw20744step0 raw20744step0Labels := by
      have hz : ∀ j, raw20744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20744step0 = (fun i j => raw20744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20744step0 raw20744; decide +kernel
      have hl : raw20744step0Labels = raw20744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20744 raw20744Labels permutation346 hz
    mixedMoment B raw20744step0 raw20744step0Labels = mixedMoment B raw20744step1 raw20744step1Labels := by
      have hz : ∀ j, raw20744step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20744step1 = (fun i j => raw20744step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20744step1 raw20744step0; decide +kernel
      have hl : raw20744step1Labels = raw20744step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20744step0 raw20744step0Labels permutation56 hz
    _ = mixedMoment B node2517 node2517Labels := by rfl

def raw20745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20745Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20745step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20745 raw20745Labels = mixedMoment B node1131 node1131Labels := by
  calc
    mixedMoment B raw20745 raw20745Labels = mixedMoment B raw20745step0 raw20745step0Labels := by
      have hz : ∀ j, raw20745 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20745step0 = (fun i j => raw20745 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20745step0 raw20745; decide +kernel
      have hl : raw20745step0Labels = raw20745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20745 raw20745Labels permutation346 hz
    mixedMoment B raw20745step0 raw20745step0Labels = mixedMoment B raw20745step1 raw20745step1Labels := by
      have ha : raw20745step1 = (fun i j => raw20745step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20745step1 raw20745step0; decide +kernel
      have hl : raw20745step1Labels = raw20745step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20745step0 raw20745step0Labels permutation38 permutation2
    _ = mixedMoment B node1131 node1131Labels := by rfl

def raw20746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20746Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20746step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20746step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20746 raw20746Labels = mixedMoment B node1131 node1131Labels := by
  calc
    mixedMoment B raw20746 raw20746Labels = mixedMoment B raw20746step0 raw20746step0Labels := by
      have hz : ∀ j, raw20746 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20746step0 = (fun i j => raw20746 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20746step0 raw20746; decide +kernel
      have hl : raw20746step0Labels = raw20746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20746 raw20746Labels permutation265 hz
    mixedMoment B raw20746step0 raw20746step0Labels = mixedMoment B raw20746step1 raw20746step1Labels := by
      have ha : raw20746step1 = (fun i j => raw20746step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20746step1 raw20746step0; decide +kernel
      have hl : raw20746step1Labels = raw20746step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20746step0 raw20746step0Labels permutation38 permutation2
    _ = mixedMoment B node1131 node1131Labels := by rfl

def raw20747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20747Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20747step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20747step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20747step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20747 raw20747Labels = mixedMoment B node1144 node1144Labels := by
  calc
    mixedMoment B raw20747 raw20747Labels = mixedMoment B raw20747step0 raw20747step0Labels := by
      have hz : ∀ j, raw20747 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20747step0 = (fun i j => raw20747 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20747step0 raw20747; decide +kernel
      have hl : raw20747step0Labels = raw20747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20747 raw20747Labels permutation346 hz
    mixedMoment B raw20747step0 raw20747step0Labels = mixedMoment B raw20747step1 raw20747step1Labels := by
      have hz : ∀ j, raw20747step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20747step1 = (fun i j => raw20747step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20747step1 raw20747step0; decide +kernel
      have hl : raw20747step1Labels = raw20747step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20747step0 raw20747step0Labels permutation56 hz
    _ = mixedMoment B node1144 node1144Labels := by rfl

def raw20748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20748step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw20748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20748 raw20748Labels = mixedMoment B node1140 node1140Labels := by
  calc
    mixedMoment B raw20748 raw20748Labels = mixedMoment B raw20748step0 raw20748step0Labels := by
      have hz : ∀ j, raw20748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20748step0 = (fun i j => raw20748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20748step0 raw20748; decide +kernel
      have hl : raw20748step0Labels = raw20748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20748 raw20748Labels permutation346 hz
    mixedMoment B raw20748step0 raw20748step0Labels = mixedMoment B raw20748step1 raw20748step1Labels := by
      have hz : ∀ j, raw20748step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20748step1 = (fun i j => raw20748step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20748step1 raw20748step0; decide +kernel
      have hl : raw20748step1Labels = raw20748step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20748step0 raw20748step0Labels permutation56 hz
    _ = mixedMoment B node1140 node1140Labels := by rfl

def raw20749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20749step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20749step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20749step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20749step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20749 raw20749Labels = mixedMoment B node4144 node4144Labels := by
  calc
    mixedMoment B raw20749 raw20749Labels = mixedMoment B raw20749step0 raw20749step0Labels := by
      have hz : ∀ j, raw20749 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20749step0 = (fun i j => raw20749 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20749step0 raw20749; decide +kernel
      have hl : raw20749step0Labels = raw20749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20749 raw20749Labels permutation346 hz
    mixedMoment B raw20749step0 raw20749step0Labels = mixedMoment B raw20749step1 raw20749step1Labels := by
      have ha : raw20749step1 = (fun i j => raw20749step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20749step1 raw20749step0; decide +kernel
      have hl : raw20749step1Labels = raw20749step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20749step0 raw20749step0Labels permutation38 permutation3
    mixedMoment B raw20749step1 raw20749step1Labels = mixedMoment B raw20749step2 raw20749step2Labels := by
      have ha : raw20749step2 = raw20749step1 := by apply Matrix.ext; unfold raw20749step2 raw20749step1; decide +kernel
      have hl : raw20749step1Labels = labelEmbedding6 ∘ raw20749step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20749step1 raw20749step1Labels raw20749step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4144 node4144Labels := by rfl

def raw20750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20750step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20750step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20750 raw20750Labels = mixedMoment B node4523 node4523Labels := by
  calc
    mixedMoment B raw20750 raw20750Labels = mixedMoment B raw20750step0 raw20750step0Labels := by
      have ha : raw20750step0 = (fun i j => raw20750 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20750step0 raw20750; decide +kernel
      have hl : raw20750step0Labels = raw20750Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20750 raw20750Labels permutation182 permutation3
    mixedMoment B raw20750step0 raw20750step0Labels = mixedMoment B raw20750step1 raw20750step1Labels := by
      have ha : raw20750step1 = raw20750step0 := by apply Matrix.ext; unfold raw20750step1 raw20750step0; decide +kernel
      have hl : raw20750step0Labels = labelEmbedding6 ∘ raw20750step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20750step0 raw20750step0Labels raw20750step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4523 node4523Labels := by rfl

def raw20751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20751step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20751step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20751step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20751 raw20751Labels = mixedMoment B node4517 node4517Labels := by
  calc
    mixedMoment B raw20751 raw20751Labels = mixedMoment B raw20751step0 raw20751step0Labels := by
      have hz : ∀ j, raw20751 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20751step0 = (fun i j => raw20751 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20751step0 raw20751; decide +kernel
      have hl : raw20751step0Labels = raw20751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20751 raw20751Labels permutation346 hz
    mixedMoment B raw20751step0 raw20751step0Labels = mixedMoment B raw20751step1 raw20751step1Labels := by
      have ha : raw20751step1 = (fun i j => raw20751step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20751step1 raw20751step0; decide +kernel
      have hl : raw20751step1Labels = raw20751step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20751step0 raw20751step0Labels permutation38 permutation3
    mixedMoment B raw20751step1 raw20751step1Labels = mixedMoment B raw20751step2 raw20751step2Labels := by
      have ha : raw20751step2 = raw20751step1 := by apply Matrix.ext; unfold raw20751step2 raw20751step1; decide +kernel
      have hl : raw20751step1Labels = labelEmbedding6 ∘ raw20751step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20751step1 raw20751step1Labels raw20751step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4517 node4517Labels := by rfl

def raw20752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw20752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw20752step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20752step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw20752step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20752step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20752step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20752step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20752step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20752 raw20752Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw20752 raw20752Labels = mixedMoment B raw20752step0 raw20752step0Labels := by
      have hz : ∀ j, raw20752 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20752step0 = (fun i j => raw20752 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20752step0 raw20752; decide +kernel
      have hl : raw20752step0Labels = raw20752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20752 raw20752Labels permutation520 hz
    mixedMoment B raw20752step0 raw20752step0Labels = mixedMoment B raw20752step1 raw20752step1Labels := by
      have hz : ∀ j, raw20752step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20752step1 = (fun i j => raw20752step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20752step1 raw20752step0; decide +kernel
      have hl : raw20752step1Labels = raw20752step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20752step0 raw20752step0Labels permutation80 hz
    mixedMoment B raw20752step1 raw20752step1Labels = mixedMoment B raw20752step2 raw20752step2Labels := by
      have ha : raw20752step2 = (fun i j => raw20752step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20752step2 raw20752step1; decide +kernel
      have hl : raw20752step2Labels = raw20752step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20752step1 raw20752step1Labels permutation10 permutation3
    mixedMoment B raw20752step2 raw20752step2Labels = mixedMoment B raw20752step3 raw20752step3Labels := by
      have ha : raw20752step3 = raw20752step2 := by apply Matrix.ext; unfold raw20752step3 raw20752step2; decide +kernel
      have hl : raw20752step2Labels = labelEmbedding6 ∘ raw20752step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20752step2 raw20752step2Labels raw20752step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

def raw20753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20753step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20753step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20753step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20753 raw20753Labels = mixedMoment B node4144 node4144Labels := by
  calc
    mixedMoment B raw20753 raw20753Labels = mixedMoment B raw20753step0 raw20753step0Labels := by
      have hz : ∀ j, raw20753 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20753step0 = (fun i j => raw20753 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20753step0 raw20753; decide +kernel
      have hl : raw20753step0Labels = raw20753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20753 raw20753Labels permutation265 hz
    mixedMoment B raw20753step0 raw20753step0Labels = mixedMoment B raw20753step1 raw20753step1Labels := by
      have ha : raw20753step1 = (fun i j => raw20753step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20753step1 raw20753step0; decide +kernel
      have hl : raw20753step1Labels = raw20753step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20753step0 raw20753step0Labels permutation38 permutation3
    mixedMoment B raw20753step1 raw20753step1Labels = mixedMoment B raw20753step2 raw20753step2Labels := by
      have ha : raw20753step2 = raw20753step1 := by apply Matrix.ext; unfold raw20753step2 raw20753step1; decide +kernel
      have hl : raw20753step1Labels = labelEmbedding6 ∘ raw20753step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20753step1 raw20753step1Labels raw20753step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4144 node4144Labels := by rfl

def raw20754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20754step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20754step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20754step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20754 raw20754Labels = mixedMoment B node4523 node4523Labels := by
  calc
    mixedMoment B raw20754 raw20754Labels = mixedMoment B raw20754step0 raw20754step0Labels := by
      have ha : raw20754step0 = (fun i j => raw20754 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20754step0 raw20754; decide +kernel
      have hl : raw20754step0Labels = raw20754Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20754 raw20754Labels permutation158 permutation3
    mixedMoment B raw20754step0 raw20754step0Labels = mixedMoment B raw20754step1 raw20754step1Labels := by
      have ha : raw20754step1 = raw20754step0 := by apply Matrix.ext; unfold raw20754step1 raw20754step0; decide +kernel
      have hl : raw20754step0Labels = labelEmbedding6 ∘ raw20754step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20754step0 raw20754step0Labels raw20754step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4523 node4523Labels := by rfl

def raw20755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20755step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20755step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20755step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20755step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20755 raw20755Labels = mixedMoment B node4517 node4517Labels := by
  calc
    mixedMoment B raw20755 raw20755Labels = mixedMoment B raw20755step0 raw20755step0Labels := by
      have hz : ∀ j, raw20755 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20755step0 = (fun i j => raw20755 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20755step0 raw20755; decide +kernel
      have hl : raw20755step0Labels = raw20755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20755 raw20755Labels permutation265 hz
    mixedMoment B raw20755step0 raw20755step0Labels = mixedMoment B raw20755step1 raw20755step1Labels := by
      have ha : raw20755step1 = (fun i j => raw20755step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20755step1 raw20755step0; decide +kernel
      have hl : raw20755step1Labels = raw20755step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20755step0 raw20755step0Labels permutation38 permutation3
    mixedMoment B raw20755step1 raw20755step1Labels = mixedMoment B raw20755step2 raw20755step2Labels := by
      have ha : raw20755step2 = raw20755step1 := by apply Matrix.ext; unfold raw20755step2 raw20755step1; decide +kernel
      have hl : raw20755step1Labels = labelEmbedding6 ∘ raw20755step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20755step1 raw20755step1Labels raw20755step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4517 node4517Labels := by rfl

def raw20756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw20756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw20756step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20756step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw20756step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20756step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20756step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20756step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20756step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20756 raw20756Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw20756 raw20756Labels = mixedMoment B raw20756step0 raw20756step0Labels := by
      have hz : ∀ j, raw20756 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20756step0 = (fun i j => raw20756 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20756step0 raw20756; decide +kernel
      have hl : raw20756step0Labels = raw20756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20756 raw20756Labels permutation520 hz
    mixedMoment B raw20756step0 raw20756step0Labels = mixedMoment B raw20756step1 raw20756step1Labels := by
      have hz : ∀ j, raw20756step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20756step1 = (fun i j => raw20756step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20756step1 raw20756step0; decide +kernel
      have hl : raw20756step1Labels = raw20756step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20756step0 raw20756step0Labels permutation56 hz
    mixedMoment B raw20756step1 raw20756step1Labels = mixedMoment B raw20756step2 raw20756step2Labels := by
      have ha : raw20756step2 = (fun i j => raw20756step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20756step2 raw20756step1; decide +kernel
      have hl : raw20756step2Labels = raw20756step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20756step1 raw20756step1Labels permutation10 permutation3
    mixedMoment B raw20756step2 raw20756step2Labels = mixedMoment B raw20756step3 raw20756step3Labels := by
      have ha : raw20756step3 = raw20756step2 := by apply Matrix.ext; unfold raw20756step3 raw20756step2; decide +kernel
      have hl : raw20756step2Labels = labelEmbedding6 ∘ raw20756step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20756step2 raw20756step2Labels raw20756step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

def raw20757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20757step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20757step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20757step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20757step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20757step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20757step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20757step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20757 raw20757Labels = mixedMoment B node4177 node4177Labels := by
  calc
    mixedMoment B raw20757 raw20757Labels = mixedMoment B raw20757step0 raw20757step0Labels := by
      have hz : ∀ j, raw20757 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20757step0 = (fun i j => raw20757 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20757step0 raw20757; decide +kernel
      have hl : raw20757step0Labels = raw20757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20757 raw20757Labels permutation346 hz
    mixedMoment B raw20757step0 raw20757step0Labels = mixedMoment B raw20757step1 raw20757step1Labels := by
      have hz : ∀ j, raw20757step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20757step1 = (fun i j => raw20757step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20757step1 raw20757step0; decide +kernel
      have hl : raw20757step1Labels = raw20757step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20757step0 raw20757step0Labels permutation56 hz
    mixedMoment B raw20757step1 raw20757step1Labels = mixedMoment B raw20757step2 raw20757step2Labels := by
      have ha : raw20757step2 = (fun i j => raw20757step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20757step2 raw20757step1; decide +kernel
      have hl : raw20757step2Labels = raw20757step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20757step1 raw20757step1Labels permutation8 permutation3
    mixedMoment B raw20757step2 raw20757step2Labels = mixedMoment B raw20757step3 raw20757step3Labels := by
      have ha : raw20757step3 = raw20757step2 := by apply Matrix.ext; unfold raw20757step3 raw20757step2; decide +kernel
      have hl : raw20757step2Labels = labelEmbedding6 ∘ raw20757step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20757step2 raw20757step2Labels raw20757step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4177 node4177Labels := by rfl

def raw20758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20758step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20758step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20758step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20758step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20758 raw20758Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw20758 raw20758Labels = mixedMoment B raw20758step0 raw20758step0Labels := by
      have hz : ∀ j, raw20758 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20758step0 = (fun i j => raw20758 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20758step0 raw20758; decide +kernel
      have hl : raw20758step0Labels = raw20758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20758 raw20758Labels permutation346 hz
    mixedMoment B raw20758step0 raw20758step0Labels = mixedMoment B raw20758step1 raw20758step1Labels := by
      have ha : raw20758step1 = (fun i j => raw20758step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20758step1 raw20758step0; decide +kernel
      have hl : raw20758step1Labels = raw20758step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20758step0 raw20758step0Labels permutation32 permutation3
    mixedMoment B raw20758step1 raw20758step1Labels = mixedMoment B raw20758step2 raw20758step2Labels := by
      have ha : raw20758step2 = raw20758step1 := by apply Matrix.ext; unfold raw20758step2 raw20758step1; decide +kernel
      have hl : raw20758step1Labels = labelEmbedding6 ∘ raw20758step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20758step1 raw20758step1Labels raw20758step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4546 node4546Labels := by rfl

def raw20759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20759step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20759step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20759step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20759step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20759 raw20759Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw20759 raw20759Labels = mixedMoment B raw20759step0 raw20759step0Labels := by
      have hz : ∀ j, raw20759 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20759step0 = (fun i j => raw20759 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20759step0 raw20759; decide +kernel
      have hl : raw20759step0Labels = raw20759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20759 raw20759Labels permutation265 hz
    mixedMoment B raw20759step0 raw20759step0Labels = mixedMoment B raw20759step1 raw20759step1Labels := by
      have ha : raw20759step1 = (fun i j => raw20759step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20759step1 raw20759step0; decide +kernel
      have hl : raw20759step1Labels = raw20759step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20759step0 raw20759step0Labels permutation32 permutation3
    mixedMoment B raw20759step1 raw20759step1Labels = mixedMoment B raw20759step2 raw20759step2Labels := by
      have ha : raw20759step2 = raw20759step1 := by apply Matrix.ext; unfold raw20759step2 raw20759step1; decide +kernel
      have hl : raw20759step1Labels = labelEmbedding6 ∘ raw20759step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20759step1 raw20759step1Labels raw20759step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4546 node4546Labels := by rfl

def raw20760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw20760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20760step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20760step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20760step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20760step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw20760step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20760step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw20760step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20760step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw20760step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20760 raw20760Labels = mixedMoment B node4625 node4625Labels := by
  calc
    mixedMoment B raw20760 raw20760Labels = mixedMoment B raw20760step0 raw20760step0Labels := by
      have hz : ∀ j, raw20760 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20760step0 = (fun i j => raw20760 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20760step0 raw20760; decide +kernel
      have hl : raw20760step0Labels = raw20760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20760 raw20760Labels permutation520 hz
    mixedMoment B raw20760step0 raw20760step0Labels = mixedMoment B raw20760step1 raw20760step1Labels := by
      have hz : ∀ j, raw20760step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20760step1 = (fun i j => raw20760step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20760step1 raw20760step0; decide +kernel
      have hl : raw20760step1Labels = raw20760step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20760step0 raw20760step0Labels permutation80 hz
    mixedMoment B raw20760step1 raw20760step1Labels = mixedMoment B raw20760step2 raw20760step2Labels := by
      have hz : ∀ j, raw20760step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20760step2 = (fun i j => raw20760step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20760step2 raw20760step1; decide +kernel
      have hl : raw20760step2Labels = raw20760step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20760step1 raw20760step1Labels permutation14 hz
    mixedMoment B raw20760step2 raw20760step2Labels = mixedMoment B raw20760step3 raw20760step3Labels := by
      have ha : raw20760step3 = (fun i j => raw20760step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20760step3 raw20760step2; decide +kernel
      have hl : raw20760step3Labels = raw20760step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20760step2 raw20760step2Labels permutation2 permutation3
    mixedMoment B raw20760step3 raw20760step3Labels = mixedMoment B raw20760step4 raw20760step4Labels := by
      have ha : raw20760step4 = raw20760step3 := by apply Matrix.ext; unfold raw20760step4 raw20760step3; decide +kernel
      have hl : raw20760step3Labels = labelEmbedding6 ∘ raw20760step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20760step3 raw20760step3Labels raw20760step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4625 node4625Labels := by rfl

def raw20761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20761step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20761step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20761step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20761step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20761step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20761step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20761step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20761 raw20761Labels = mixedMoment B node4148 node4148Labels := by
  calc
    mixedMoment B raw20761 raw20761Labels = mixedMoment B raw20761step0 raw20761step0Labels := by
      have hz : ∀ j, raw20761 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20761step0 = (fun i j => raw20761 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20761step0 raw20761; decide +kernel
      have hl : raw20761step0Labels = raw20761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20761 raw20761Labels permutation346 hz
    mixedMoment B raw20761step0 raw20761step0Labels = mixedMoment B raw20761step1 raw20761step1Labels := by
      have hz : ∀ j, raw20761step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20761step1 = (fun i j => raw20761step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20761step1 raw20761step0; decide +kernel
      have hl : raw20761step1Labels = raw20761step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20761step0 raw20761step0Labels permutation56 hz
    mixedMoment B raw20761step1 raw20761step1Labels = mixedMoment B raw20761step2 raw20761step2Labels := by
      have ha : raw20761step2 = (fun i j => raw20761step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20761step2 raw20761step1; decide +kernel
      have hl : raw20761step2Labels = raw20761step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20761step1 raw20761step1Labels permutation8 permutation3
    mixedMoment B raw20761step2 raw20761step2Labels = mixedMoment B raw20761step3 raw20761step3Labels := by
      have ha : raw20761step3 = raw20761step2 := by apply Matrix.ext; unfold raw20761step3 raw20761step2; decide +kernel
      have hl : raw20761step2Labels = labelEmbedding6 ∘ raw20761step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20761step2 raw20761step2Labels raw20761step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4148 node4148Labels := by rfl

def raw20762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20762step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20762step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20762step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20762step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20762 raw20762Labels = mixedMoment B node4526 node4526Labels := by
  calc
    mixedMoment B raw20762 raw20762Labels = mixedMoment B raw20762step0 raw20762step0Labels := by
      have hz : ∀ j, raw20762 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20762step0 = (fun i j => raw20762 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20762step0 raw20762; decide +kernel
      have hl : raw20762step0Labels = raw20762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20762 raw20762Labels permutation346 hz
    mixedMoment B raw20762step0 raw20762step0Labels = mixedMoment B raw20762step1 raw20762step1Labels := by
      have ha : raw20762step1 = (fun i j => raw20762step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20762step1 raw20762step0; decide +kernel
      have hl : raw20762step1Labels = raw20762step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20762step0 raw20762step0Labels permutation32 permutation3
    mixedMoment B raw20762step1 raw20762step1Labels = mixedMoment B raw20762step2 raw20762step2Labels := by
      have ha : raw20762step2 = raw20762step1 := by apply Matrix.ext; unfold raw20762step2 raw20762step1; decide +kernel
      have hl : raw20762step1Labels = labelEmbedding6 ∘ raw20762step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20762step1 raw20762step1Labels raw20762step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4526 node4526Labels := by rfl

def raw20763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20763step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20763step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20763step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20763step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20763step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20763 raw20763Labels = mixedMoment B node4526 node4526Labels := by
  calc
    mixedMoment B raw20763 raw20763Labels = mixedMoment B raw20763step0 raw20763step0Labels := by
      have hz : ∀ j, raw20763 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20763step0 = (fun i j => raw20763 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20763step0 raw20763; decide +kernel
      have hl : raw20763step0Labels = raw20763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20763 raw20763Labels permutation265 hz
    mixedMoment B raw20763step0 raw20763step0Labels = mixedMoment B raw20763step1 raw20763step1Labels := by
      have ha : raw20763step1 = (fun i j => raw20763step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20763step1 raw20763step0; decide +kernel
      have hl : raw20763step1Labels = raw20763step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20763step0 raw20763step0Labels permutation32 permutation3
    mixedMoment B raw20763step1 raw20763step1Labels = mixedMoment B raw20763step2 raw20763step2Labels := by
      have ha : raw20763step2 = raw20763step1 := by apply Matrix.ext; unfold raw20763step2 raw20763step1; decide +kernel
      have hl : raw20763step1Labels = labelEmbedding6 ∘ raw20763step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20763step1 raw20763step1Labels raw20763step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4526 node4526Labels := by rfl

def raw20764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20764step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20764step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20764step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20764step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw20764step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20764step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw20764step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20764 raw20764Labels = mixedMoment B node4520 node4520Labels := by
  calc
    mixedMoment B raw20764 raw20764Labels = mixedMoment B raw20764step0 raw20764step0Labels := by
      have hz : ∀ j, raw20764 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20764step0 = (fun i j => raw20764 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20764step0 raw20764; decide +kernel
      have hl : raw20764step0Labels = raw20764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20764 raw20764Labels permutation346 hz
    mixedMoment B raw20764step0 raw20764step0Labels = mixedMoment B raw20764step1 raw20764step1Labels := by
      have hz : ∀ j, raw20764step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20764step1 = (fun i j => raw20764step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20764step1 raw20764step0; decide +kernel
      have hl : raw20764step1Labels = raw20764step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20764step0 raw20764step0Labels permutation56 hz
    mixedMoment B raw20764step1 raw20764step1Labels = mixedMoment B raw20764step2 raw20764step2Labels := by
      have ha : raw20764step2 = (fun i j => raw20764step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20764step2 raw20764step1; decide +kernel
      have hl : raw20764step2Labels = raw20764step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20764step1 raw20764step1Labels permutation8 permutation3
    mixedMoment B raw20764step2 raw20764step2Labels = mixedMoment B raw20764step3 raw20764step3Labels := by
      have ha : raw20764step3 = raw20764step2 := by apply Matrix.ext; unfold raw20764step3 raw20764step2; decide +kernel
      have hl : raw20764step2Labels = labelEmbedding6 ∘ raw20764step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20764step2 raw20764step2Labels raw20764step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4520 node4520Labels := by rfl

def raw20765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20765step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20765step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw20765step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20765step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw20765step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20765 raw20765Labels = mixedMoment B node4146 node4146Labels := by
  calc
    mixedMoment B raw20765 raw20765Labels = mixedMoment B raw20765step0 raw20765step0Labels := by
      have hz : ∀ j, raw20765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20765step0 = (fun i j => raw20765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20765step0 raw20765; decide +kernel
      have hl : raw20765step0Labels = raw20765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20765 raw20765Labels permutation346 hz
    mixedMoment B raw20765step0 raw20765step0Labels = mixedMoment B raw20765step1 raw20765step1Labels := by
      have hz : ∀ j, raw20765step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20765step1 = (fun i j => raw20765step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20765step1 raw20765step0; decide +kernel
      have hl : raw20765step1Labels = raw20765step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20765step0 raw20765step0Labels permutation56 hz
    mixedMoment B raw20765step1 raw20765step1Labels = mixedMoment B raw20765step2 raw20765step2Labels := by
      have ha : raw20765step2 = (fun i j => raw20765step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20765step2 raw20765step1; decide +kernel
      have hl : raw20765step2Labels = raw20765step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20765step1 raw20765step1Labels permutation8 permutation3
    mixedMoment B raw20765step2 raw20765step2Labels = mixedMoment B raw20765step3 raw20765step3Labels := by
      have ha : raw20765step3 = raw20765step2 := by apply Matrix.ext; unfold raw20765step3 raw20765step2; decide +kernel
      have hl : raw20765step2Labels = labelEmbedding6 ∘ raw20765step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20765step2 raw20765step2Labels raw20765step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4146 node4146Labels := by rfl

def raw20766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20766step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20766step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20766step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20766step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20766 raw20766Labels = mixedMoment B node4293 node4293Labels := by
  calc
    mixedMoment B raw20766 raw20766Labels = mixedMoment B raw20766step0 raw20766step0Labels := by
      have hz : ∀ j, raw20766 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20766step0 = (fun i j => raw20766 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20766step0 raw20766; decide +kernel
      have hl : raw20766step0Labels = raw20766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20766 raw20766Labels permutation346 hz
    mixedMoment B raw20766step0 raw20766step0Labels = mixedMoment B raw20766step1 raw20766step1Labels := by
      have ha : raw20766step1 = (fun i j => raw20766step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20766step1 raw20766step0; decide +kernel
      have hl : raw20766step1Labels = raw20766step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20766step0 raw20766step0Labels permutation151 permutation3
    mixedMoment B raw20766step1 raw20766step1Labels = mixedMoment B raw20766step2 raw20766step2Labels := by
      have ha : raw20766step2 = -raw20766step1 := by apply Matrix.ext; change ∀ i j, raw20766step2 i j = -(raw20766step1 i j); unfold raw20766step2 raw20766step1; decide +kernel
      have hl : raw20766step2Labels = raw20766step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20766step2 raw20766step2Labels = mixedMoment B raw20766step3 raw20766step3Labels := by
      have ha : raw20766step3 = raw20766step2 := by apply Matrix.ext; unfold raw20766step3 raw20766step2; decide +kernel
      have hl : raw20766step2Labels = labelEmbedding6 ∘ raw20766step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20766step2 raw20766step2Labels raw20766step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4293 node4293Labels := by rfl

def raw20767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20767step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20767step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20767step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20767step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20767 raw20767Labels = mixedMoment B node4293 node4293Labels := by
  calc
    mixedMoment B raw20767 raw20767Labels = mixedMoment B raw20767step0 raw20767step0Labels := by
      have hz : ∀ j, raw20767 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20767step0 = (fun i j => raw20767 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20767step0 raw20767; decide +kernel
      have hl : raw20767step0Labels = raw20767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20767 raw20767Labels permutation265 hz
    mixedMoment B raw20767step0 raw20767step0Labels = mixedMoment B raw20767step1 raw20767step1Labels := by
      have ha : raw20767step1 = (fun i j => raw20767step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20767step1 raw20767step0; decide +kernel
      have hl : raw20767step1Labels = raw20767step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20767step0 raw20767step0Labels permutation151 permutation3
    mixedMoment B raw20767step1 raw20767step1Labels = mixedMoment B raw20767step2 raw20767step2Labels := by
      have ha : raw20767step2 = -raw20767step1 := by apply Matrix.ext; change ∀ i j, raw20767step2 i j = -(raw20767step1 i j); unfold raw20767step2 raw20767step1; decide +kernel
      have hl : raw20767step2Labels = raw20767step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20767step2 raw20767step2Labels = mixedMoment B raw20767step3 raw20767step3Labels := by
      have ha : raw20767step3 = raw20767step2 := by apply Matrix.ext; unfold raw20767step3 raw20767step2; decide +kernel
      have hl : raw20767step2Labels = labelEmbedding6 ∘ raw20767step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20767step2 raw20767step2Labels raw20767step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4293 node4293Labels := by rfl

def raw20768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20768step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20768step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20768step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, -1, 2], ![-4, 2, 2]]
def raw20768step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20768step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw20768step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20768step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw20768step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20768 raw20768Labels = mixedMoment B node4315 node4315Labels := by
  calc
    mixedMoment B raw20768 raw20768Labels = mixedMoment B raw20768step0 raw20768step0Labels := by
      have hz : ∀ j, raw20768 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20768step0 = (fun i j => raw20768 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20768step0 raw20768; decide +kernel
      have hl : raw20768step0Labels = raw20768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20768 raw20768Labels permutation346 hz
    mixedMoment B raw20768step0 raw20768step0Labels = mixedMoment B raw20768step1 raw20768step1Labels := by
      have hz : ∀ j, raw20768step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20768step1 = (fun i j => raw20768step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20768step1 raw20768step0; decide +kernel
      have hl : raw20768step1Labels = raw20768step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20768step0 raw20768step0Labels permutation56 hz
    mixedMoment B raw20768step1 raw20768step1Labels = mixedMoment B raw20768step2 raw20768step2Labels := by
      have ha : raw20768step2 = (fun i j => raw20768step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20768step2 raw20768step1; decide +kernel
      have hl : raw20768step2Labels = raw20768step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20768step1 raw20768step1Labels permutation31 permutation3
    mixedMoment B raw20768step2 raw20768step2Labels = mixedMoment B raw20768step3 raw20768step3Labels := by
      have ha : raw20768step3 = -raw20768step2 := by apply Matrix.ext; change ∀ i j, raw20768step3 i j = -(raw20768step2 i j); unfold raw20768step3 raw20768step2; decide +kernel
      have hl : raw20768step3Labels = raw20768step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20768step3 raw20768step3Labels = mixedMoment B raw20768step4 raw20768step4Labels := by
      have ha : raw20768step4 = raw20768step3 := by apply Matrix.ext; unfold raw20768step4 raw20768step3; decide +kernel
      have hl : raw20768step3Labels = labelEmbedding6 ∘ raw20768step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20768step3 raw20768step3Labels raw20768step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4315 node4315Labels := by rfl

def raw20769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![4, -3, -1]]
def raw20769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw20769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20769step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw20769step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20769step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw20769step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20769step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw20769step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20769step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw20769step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20769step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw20769step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20769 raw20769Labels = mixedMoment B node4468 node4468Labels := by
  calc
    mixedMoment B raw20769 raw20769Labels = mixedMoment B raw20769step0 raw20769step0Labels := by
      have hz : ∀ j, raw20769 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20769step0 = (fun i j => raw20769 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20769step0 raw20769; decide +kernel
      have hl : raw20769step0Labels = raw20769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20769 raw20769Labels permutation520 hz
    mixedMoment B raw20769step0 raw20769step0Labels = mixedMoment B raw20769step1 raw20769step1Labels := by
      have hz : ∀ j, raw20769step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20769step1 = (fun i j => raw20769step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20769step1 raw20769step0; decide +kernel
      have hl : raw20769step1Labels = raw20769step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20769step0 raw20769step0Labels permutation80 hz
    mixedMoment B raw20769step1 raw20769step1Labels = mixedMoment B raw20769step2 raw20769step2Labels := by
      have hz : ∀ j, raw20769step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20769step2 = (fun i j => raw20769step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20769step2 raw20769step1; decide +kernel
      have hl : raw20769step2Labels = raw20769step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20769step1 raw20769step1Labels permutation14 hz
    mixedMoment B raw20769step2 raw20769step2Labels = mixedMoment B raw20769step3 raw20769step3Labels := by
      have ha : raw20769step3 = (fun i j => raw20769step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20769step3 raw20769step2; decide +kernel
      have hl : raw20769step3Labels = raw20769step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20769step2 raw20769step2Labels permutation7 permutation3
    mixedMoment B raw20769step3 raw20769step3Labels = mixedMoment B raw20769step4 raw20769step4Labels := by
      have ha : raw20769step4 = -raw20769step3 := by apply Matrix.ext; change ∀ i j, raw20769step4 i j = -(raw20769step3 i j); unfold raw20769step4 raw20769step3; decide +kernel
      have hl : raw20769step4Labels = raw20769step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw20769step4 raw20769step4Labels = mixedMoment B raw20769step5 raw20769step5Labels := by
      have ha : raw20769step5 = raw20769step4 := by apply Matrix.ext; unfold raw20769step5 raw20769step4; decide +kernel
      have hl : raw20769step4Labels = labelEmbedding6 ∘ raw20769step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20769step4 raw20769step4Labels raw20769step5Labels labelEmbedding6 hl
    _ = mixedMoment B node4468 node4468Labels := by rfl

def raw20770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20770Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20770step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20770step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20770 raw20770Labels = mixedMoment B node572 node572Labels := by
  calc
    mixedMoment B raw20770 raw20770Labels = mixedMoment B raw20770step0 raw20770step0Labels := by
      have hz : ∀ j, raw20770 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20770step0 = (fun i j => raw20770 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20770step0 raw20770; decide +kernel
      have hl : raw20770step0Labels = raw20770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20770 raw20770Labels permutation346 hz
    mixedMoment B raw20770step0 raw20770step0Labels = mixedMoment B raw20770step1 raw20770step1Labels := by
      have ha : raw20770step1 = (fun i j => raw20770step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20770step1 raw20770step0; decide +kernel
      have hl : raw20770step1Labels = raw20770step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20770step0 raw20770step0Labels permutation38 permutation3
    _ = mixedMoment B node572 node572Labels := by rfl

def raw20771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20771Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20771step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20771 raw20771Labels = mixedMoment B node1107 node1107Labels := by
  calc
    mixedMoment B raw20771 raw20771Labels = mixedMoment B raw20771step0 raw20771step0Labels := by
      have ha : raw20771step0 = (fun i j => raw20771 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20771step0 raw20771; decide +kernel
      have hl : raw20771step0Labels = raw20771Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20771 raw20771Labels permutation182 permutation3
    _ = mixedMoment B node1107 node1107Labels := by rfl

def raw20772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20772Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20772step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20772step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20772 raw20772Labels = mixedMoment B node1101 node1101Labels := by
  calc
    mixedMoment B raw20772 raw20772Labels = mixedMoment B raw20772step0 raw20772step0Labels := by
      have hz : ∀ j, raw20772 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20772step0 = (fun i j => raw20772 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20772step0 raw20772; decide +kernel
      have hl : raw20772step0Labels = raw20772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20772 raw20772Labels permutation346 hz
    mixedMoment B raw20772step0 raw20772step0Labels = mixedMoment B raw20772step1 raw20772step1Labels := by
      have ha : raw20772step1 = (fun i j => raw20772step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20772step1 raw20772step0; decide +kernel
      have hl : raw20772step1Labels = raw20772step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20772step0 raw20772step0Labels permutation38 permutation3
    _ = mixedMoment B node1101 node1101Labels := by rfl

def raw20773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw20773Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw20773step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20773step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw20773step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20773step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20773step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20773 raw20773Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw20773 raw20773Labels = mixedMoment B raw20773step0 raw20773step0Labels := by
      have hz : ∀ j, raw20773 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20773step0 = (fun i j => raw20773 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20773step0 raw20773; decide +kernel
      have hl : raw20773step0Labels = raw20773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20773 raw20773Labels permutation520 hz
    mixedMoment B raw20773step0 raw20773step0Labels = mixedMoment B raw20773step1 raw20773step1Labels := by
      have hz : ∀ j, raw20773step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20773step1 = (fun i j => raw20773step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20773step1 raw20773step0; decide +kernel
      have hl : raw20773step1Labels = raw20773step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20773step0 raw20773step0Labels permutation80 hz
    mixedMoment B raw20773step1 raw20773step1Labels = mixedMoment B raw20773step2 raw20773step2Labels := by
      have ha : raw20773step2 = (fun i j => raw20773step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20773step2 raw20773step1; decide +kernel
      have hl : raw20773step2Labels = raw20773step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20773step1 raw20773step1Labels permutation10 permutation3
    _ = mixedMoment B node1242 node1242Labels := by rfl

def raw20774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20774Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20774step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20774step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20774 raw20774Labels = mixedMoment B node572 node572Labels := by
  calc
    mixedMoment B raw20774 raw20774Labels = mixedMoment B raw20774step0 raw20774step0Labels := by
      have hz : ∀ j, raw20774 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20774step0 = (fun i j => raw20774 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20774step0 raw20774; decide +kernel
      have hl : raw20774step0Labels = raw20774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20774 raw20774Labels permutation265 hz
    mixedMoment B raw20774step0 raw20774step0Labels = mixedMoment B raw20774step1 raw20774step1Labels := by
      have ha : raw20774step1 = (fun i j => raw20774step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20774step1 raw20774step0; decide +kernel
      have hl : raw20774step1Labels = raw20774step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20774step0 raw20774step0Labels permutation38 permutation3
    _ = mixedMoment B node572 node572Labels := by rfl

def raw20775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20775Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20775step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20775 raw20775Labels = mixedMoment B node1107 node1107Labels := by
  calc
    mixedMoment B raw20775 raw20775Labels = mixedMoment B raw20775step0 raw20775step0Labels := by
      have ha : raw20775step0 = (fun i j => raw20775 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20775step0 raw20775; decide +kernel
      have hl : raw20775step0Labels = raw20775Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20775 raw20775Labels permutation158 permutation3
    _ = mixedMoment B node1107 node1107Labels := by rfl

def raw20776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20776Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20776step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20776step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20776 raw20776Labels = mixedMoment B node1101 node1101Labels := by
  calc
    mixedMoment B raw20776 raw20776Labels = mixedMoment B raw20776step0 raw20776step0Labels := by
      have hz : ∀ j, raw20776 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20776step0 = (fun i j => raw20776 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20776step0 raw20776; decide +kernel
      have hl : raw20776step0Labels = raw20776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20776 raw20776Labels permutation265 hz
    mixedMoment B raw20776step0 raw20776step0Labels = mixedMoment B raw20776step1 raw20776step1Labels := by
      have ha : raw20776step1 = (fun i j => raw20776step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20776step1 raw20776step0; decide +kernel
      have hl : raw20776step1Labels = raw20776step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20776step0 raw20776step0Labels permutation38 permutation3
    _ = mixedMoment B node1101 node1101Labels := by rfl

def raw20777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw20777Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw20777step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20777step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw20777step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20777step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20777step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20777 raw20777Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw20777 raw20777Labels = mixedMoment B raw20777step0 raw20777step0Labels := by
      have hz : ∀ j, raw20777 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20777step0 = (fun i j => raw20777 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20777step0 raw20777; decide +kernel
      have hl : raw20777step0Labels = raw20777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20777 raw20777Labels permutation520 hz
    mixedMoment B raw20777step0 raw20777step0Labels = mixedMoment B raw20777step1 raw20777step1Labels := by
      have hz : ∀ j, raw20777step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20777step1 = (fun i j => raw20777step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20777step1 raw20777step0; decide +kernel
      have hl : raw20777step1Labels = raw20777step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20777step0 raw20777step0Labels permutation56 hz
    mixedMoment B raw20777step1 raw20777step1Labels = mixedMoment B raw20777step2 raw20777step2Labels := by
      have ha : raw20777step2 = (fun i j => raw20777step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20777step2 raw20777step1; decide +kernel
      have hl : raw20777step2Labels = raw20777step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20777step1 raw20777step1Labels permutation10 permutation3
    _ = mixedMoment B node1242 node1242Labels := by rfl

def raw20778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20778Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20778step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20778step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20778step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20778step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20778step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20778 raw20778Labels = mixedMoment B node605 node605Labels := by
  calc
    mixedMoment B raw20778 raw20778Labels = mixedMoment B raw20778step0 raw20778step0Labels := by
      have hz : ∀ j, raw20778 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20778step0 = (fun i j => raw20778 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20778step0 raw20778; decide +kernel
      have hl : raw20778step0Labels = raw20778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20778 raw20778Labels permutation346 hz
    mixedMoment B raw20778step0 raw20778step0Labels = mixedMoment B raw20778step1 raw20778step1Labels := by
      have hz : ∀ j, raw20778step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20778step1 = (fun i j => raw20778step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20778step1 raw20778step0; decide +kernel
      have hl : raw20778step1Labels = raw20778step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20778step0 raw20778step0Labels permutation56 hz
    mixedMoment B raw20778step1 raw20778step1Labels = mixedMoment B raw20778step2 raw20778step2Labels := by
      have ha : raw20778step2 = (fun i j => raw20778step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20778step2 raw20778step1; decide +kernel
      have hl : raw20778step2Labels = raw20778step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20778step1 raw20778step1Labels permutation8 permutation3
    _ = mixedMoment B node605 node605Labels := by rfl

def raw20779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20779Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20779step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20779step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20779 raw20779Labels = mixedMoment B node1131 node1131Labels := by
  calc
    mixedMoment B raw20779 raw20779Labels = mixedMoment B raw20779step0 raw20779step0Labels := by
      have hz : ∀ j, raw20779 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20779step0 = (fun i j => raw20779 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20779step0 raw20779; decide +kernel
      have hl : raw20779step0Labels = raw20779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20779 raw20779Labels permutation346 hz
    mixedMoment B raw20779step0 raw20779step0Labels = mixedMoment B raw20779step1 raw20779step1Labels := by
      have ha : raw20779step1 = (fun i j => raw20779step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20779step1 raw20779step0; decide +kernel
      have hl : raw20779step1Labels = raw20779step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20779step0 raw20779step0Labels permutation32 permutation3
    _ = mixedMoment B node1131 node1131Labels := by rfl

def raw20780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20780Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20780step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20780step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20780 raw20780Labels = mixedMoment B node1131 node1131Labels := by
  calc
    mixedMoment B raw20780 raw20780Labels = mixedMoment B raw20780step0 raw20780step0Labels := by
      have hz : ∀ j, raw20780 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20780step0 = (fun i j => raw20780 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20780step0 raw20780; decide +kernel
      have hl : raw20780step0Labels = raw20780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20780 raw20780Labels permutation265 hz
    mixedMoment B raw20780step0 raw20780step0Labels = mixedMoment B raw20780step1 raw20780step1Labels := by
      have ha : raw20780step1 = (fun i j => raw20780step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20780step1 raw20780step0; decide +kernel
      have hl : raw20780step1Labels = raw20780step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20780step0 raw20780step0Labels permutation32 permutation3
    _ = mixedMoment B node1131 node1131Labels := by rfl

def raw20781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw20781Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20781step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20781step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20781step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20781step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw20781step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20781step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw20781step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20781 raw20781Labels = mixedMoment B node1304 node1304Labels := by
  calc
    mixedMoment B raw20781 raw20781Labels = mixedMoment B raw20781step0 raw20781step0Labels := by
      have hz : ∀ j, raw20781 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20781step0 = (fun i j => raw20781 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20781step0 raw20781; decide +kernel
      have hl : raw20781step0Labels = raw20781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20781 raw20781Labels permutation520 hz
    mixedMoment B raw20781step0 raw20781step0Labels = mixedMoment B raw20781step1 raw20781step1Labels := by
      have hz : ∀ j, raw20781step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20781step1 = (fun i j => raw20781step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20781step1 raw20781step0; decide +kernel
      have hl : raw20781step1Labels = raw20781step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20781step0 raw20781step0Labels permutation80 hz
    mixedMoment B raw20781step1 raw20781step1Labels = mixedMoment B raw20781step2 raw20781step2Labels := by
      have hz : ∀ j, raw20781step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20781step2 = (fun i j => raw20781step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20781step2 raw20781step1; decide +kernel
      have hl : raw20781step2Labels = raw20781step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20781step1 raw20781step1Labels permutation14 hz
    mixedMoment B raw20781step2 raw20781step2Labels = mixedMoment B raw20781step3 raw20781step3Labels := by
      have ha : raw20781step3 = (fun i j => raw20781step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20781step3 raw20781step2; decide +kernel
      have hl : raw20781step3Labels = raw20781step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20781step2 raw20781step2Labels permutation2 permutation3
    _ = mixedMoment B node1304 node1304Labels := by rfl

def raw20782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20782step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20782step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20782step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20782step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20782step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20782 raw20782Labels = mixedMoment B node576 node576Labels := by
  calc
    mixedMoment B raw20782 raw20782Labels = mixedMoment B raw20782step0 raw20782step0Labels := by
      have hz : ∀ j, raw20782 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20782step0 = (fun i j => raw20782 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20782step0 raw20782; decide +kernel
      have hl : raw20782step0Labels = raw20782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20782 raw20782Labels permutation346 hz
    mixedMoment B raw20782step0 raw20782step0Labels = mixedMoment B raw20782step1 raw20782step1Labels := by
      have hz : ∀ j, raw20782step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20782step1 = (fun i j => raw20782step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20782step1 raw20782step0; decide +kernel
      have hl : raw20782step1Labels = raw20782step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20782step0 raw20782step0Labels permutation56 hz
    mixedMoment B raw20782step1 raw20782step1Labels = mixedMoment B raw20782step2 raw20782step2Labels := by
      have ha : raw20782step2 = (fun i j => raw20782step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20782step2 raw20782step1; decide +kernel
      have hl : raw20782step2Labels = raw20782step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20782step1 raw20782step1Labels permutation8 permutation3
    _ = mixedMoment B node576 node576Labels := by rfl

def raw20783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20783step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20783step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20783 raw20783Labels = mixedMoment B node1110 node1110Labels := by
  calc
    mixedMoment B raw20783 raw20783Labels = mixedMoment B raw20783step0 raw20783step0Labels := by
      have hz : ∀ j, raw20783 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20783step0 = (fun i j => raw20783 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20783step0 raw20783; decide +kernel
      have hl : raw20783step0Labels = raw20783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20783 raw20783Labels permutation346 hz
    mixedMoment B raw20783step0 raw20783step0Labels = mixedMoment B raw20783step1 raw20783step1Labels := by
      have ha : raw20783step1 = (fun i j => raw20783step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20783step1 raw20783step0; decide +kernel
      have hl : raw20783step1Labels = raw20783step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20783step0 raw20783step0Labels permutation32 permutation3
    _ = mixedMoment B node1110 node1110Labels := by rfl

def raw20784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20784Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20784step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw20784step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20784 raw20784Labels = mixedMoment B node1110 node1110Labels := by
  calc
    mixedMoment B raw20784 raw20784Labels = mixedMoment B raw20784step0 raw20784step0Labels := by
      have hz : ∀ j, raw20784 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20784step0 = (fun i j => raw20784 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20784step0 raw20784; decide +kernel
      have hl : raw20784step0Labels = raw20784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20784 raw20784Labels permutation265 hz
    mixedMoment B raw20784step0 raw20784step0Labels = mixedMoment B raw20784step1 raw20784step1Labels := by
      have ha : raw20784step1 = (fun i j => raw20784step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20784step1 raw20784step0; decide +kernel
      have hl : raw20784step1Labels = raw20784step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20784step0 raw20784step0Labels permutation32 permutation3
    _ = mixedMoment B node1110 node1110Labels := by rfl

def raw20785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw20785step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20785step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw20785step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20785 raw20785Labels = mixedMoment B node1104 node1104Labels := by
  calc
    mixedMoment B raw20785 raw20785Labels = mixedMoment B raw20785step0 raw20785step0Labels := by
      have hz : ∀ j, raw20785 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20785step0 = (fun i j => raw20785 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20785step0 raw20785; decide +kernel
      have hl : raw20785step0Labels = raw20785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20785 raw20785Labels permutation346 hz
    mixedMoment B raw20785step0 raw20785step0Labels = mixedMoment B raw20785step1 raw20785step1Labels := by
      have hz : ∀ j, raw20785step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20785step1 = (fun i j => raw20785step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20785step1 raw20785step0; decide +kernel
      have hl : raw20785step1Labels = raw20785step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20785step0 raw20785step0Labels permutation56 hz
    mixedMoment B raw20785step1 raw20785step1Labels = mixedMoment B raw20785step2 raw20785step2Labels := by
      have ha : raw20785step2 = (fun i j => raw20785step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20785step2 raw20785step1; decide +kernel
      have hl : raw20785step2Labels = raw20785step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20785step1 raw20785step1Labels permutation8 permutation3
    _ = mixedMoment B node1104 node1104Labels := by rfl

def raw20786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20786step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20786step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20786step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw20786step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20786 raw20786Labels = mixedMoment B node574 node574Labels := by
  calc
    mixedMoment B raw20786 raw20786Labels = mixedMoment B raw20786step0 raw20786step0Labels := by
      have hz : ∀ j, raw20786 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20786step0 = (fun i j => raw20786 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20786step0 raw20786; decide +kernel
      have hl : raw20786step0Labels = raw20786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20786 raw20786Labels permutation346 hz
    mixedMoment B raw20786step0 raw20786step0Labels = mixedMoment B raw20786step1 raw20786step1Labels := by
      have hz : ∀ j, raw20786step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20786step1 = (fun i j => raw20786step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20786step1 raw20786step0; decide +kernel
      have hl : raw20786step1Labels = raw20786step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20786step0 raw20786step0Labels permutation56 hz
    mixedMoment B raw20786step1 raw20786step1Labels = mixedMoment B raw20786step2 raw20786step2Labels := by
      have ha : raw20786step2 = (fun i j => raw20786step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20786step2 raw20786step1; decide +kernel
      have hl : raw20786step2Labels = raw20786step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20786step1 raw20786step1Labels permutation8 permutation3
    _ = mixedMoment B node574 node574Labels := by rfl

def raw20787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20787step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20787step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20787step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20787 raw20787Labels = mixedMoment B node871 node871Labels := by
  calc
    mixedMoment B raw20787 raw20787Labels = mixedMoment B raw20787step0 raw20787step0Labels := by
      have hz : ∀ j, raw20787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20787step0 = (fun i j => raw20787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20787step0 raw20787; decide +kernel
      have hl : raw20787step0Labels = raw20787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20787 raw20787Labels permutation346 hz
    mixedMoment B raw20787step0 raw20787step0Labels = mixedMoment B raw20787step1 raw20787step1Labels := by
      have ha : raw20787step1 = (fun i j => raw20787step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20787step1 raw20787step0; decide +kernel
      have hl : raw20787step1Labels = raw20787step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20787step0 raw20787step0Labels permutation151 permutation3
    mixedMoment B raw20787step1 raw20787step1Labels = mixedMoment B raw20787step2 raw20787step2Labels := by
      have ha : raw20787step2 = -raw20787step1 := by apply Matrix.ext; change ∀ i j, raw20787step2 i j = -(raw20787step1 i j); unfold raw20787step2 raw20787step1; decide +kernel
      have hl : raw20787step2Labels = raw20787step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node871 node871Labels := by rfl

def raw20788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20788step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw20788step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw20788step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20788 raw20788Labels = mixedMoment B node871 node871Labels := by
  calc
    mixedMoment B raw20788 raw20788Labels = mixedMoment B raw20788step0 raw20788step0Labels := by
      have hz : ∀ j, raw20788 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20788step0 = (fun i j => raw20788 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20788step0 raw20788; decide +kernel
      have hl : raw20788step0Labels = raw20788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20788 raw20788Labels permutation265 hz
    mixedMoment B raw20788step0 raw20788step0Labels = mixedMoment B raw20788step1 raw20788step1Labels := by
      have ha : raw20788step1 = (fun i j => raw20788step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20788step1 raw20788step0; decide +kernel
      have hl : raw20788step1Labels = raw20788step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20788step0 raw20788step0Labels permutation151 permutation3
    mixedMoment B raw20788step1 raw20788step1Labels = mixedMoment B raw20788step2 raw20788step2Labels := by
      have ha : raw20788step2 = -raw20788step1 := by apply Matrix.ext; change ∀ i j, raw20788step2 i j = -(raw20788step1 i j); unfold raw20788step2 raw20788step1; decide +kernel
      have hl : raw20788step2Labels = raw20788step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node871 node871Labels := by rfl

def raw20789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20789step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20789step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![4, -3, -1]]
def raw20789step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20789step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, -1, 2], ![-4, 2, 2]]
def raw20789step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20789step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw20789step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20789 raw20789Labels = mixedMoment B node893 node893Labels := by
  calc
    mixedMoment B raw20789 raw20789Labels = mixedMoment B raw20789step0 raw20789step0Labels := by
      have hz : ∀ j, raw20789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20789step0 = (fun i j => raw20789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20789step0 raw20789; decide +kernel
      have hl : raw20789step0Labels = raw20789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20789 raw20789Labels permutation346 hz
    mixedMoment B raw20789step0 raw20789step0Labels = mixedMoment B raw20789step1 raw20789step1Labels := by
      have hz : ∀ j, raw20789step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20789step1 = (fun i j => raw20789step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20789step1 raw20789step0; decide +kernel
      have hl : raw20789step1Labels = raw20789step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20789step0 raw20789step0Labels permutation56 hz
    mixedMoment B raw20789step1 raw20789step1Labels = mixedMoment B raw20789step2 raw20789step2Labels := by
      have ha : raw20789step2 = (fun i j => raw20789step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20789step2 raw20789step1; decide +kernel
      have hl : raw20789step2Labels = raw20789step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20789step1 raw20789step1Labels permutation31 permutation3
    mixedMoment B raw20789step2 raw20789step2Labels = mixedMoment B raw20789step3 raw20789step3Labels := by
      have ha : raw20789step3 = -raw20789step2 := by apply Matrix.ext; change ∀ i j, raw20789step3 i j = -(raw20789step2 i j); unfold raw20789step3 raw20789step2; decide +kernel
      have hl : raw20789step3Labels = raw20789step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node893 node893Labels := by rfl

def raw20790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![4, -3, -1]]
def raw20790Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw20790step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![4, -3, -1]]
def raw20790step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20790step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![4, -3, -1]]
def raw20790step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20790step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-4, 2, 2]]
def raw20790step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20790step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![4, -2, -2]]
def raw20790step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20790 raw20790Labels = mixedMoment B node1051 node1051Labels := by
  calc
    mixedMoment B raw20790 raw20790Labels = mixedMoment B raw20790step0 raw20790step0Labels := by
      have hz : ∀ j, raw20790 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20790step0 = (fun i j => raw20790 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20790step0 raw20790; decide +kernel
      have hl : raw20790step0Labels = raw20790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20790 raw20790Labels permutation520 hz
    mixedMoment B raw20790step0 raw20790step0Labels = mixedMoment B raw20790step1 raw20790step1Labels := by
      have hz : ∀ j, raw20790step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20790step1 = (fun i j => raw20790step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20790step1 raw20790step0; decide +kernel
      have hl : raw20790step1Labels = raw20790step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20790step0 raw20790step0Labels permutation80 hz
    mixedMoment B raw20790step1 raw20790step1Labels = mixedMoment B raw20790step2 raw20790step2Labels := by
      have hz : ∀ j, raw20790step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20790step2 = (fun i j => raw20790step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20790step2 raw20790step1; decide +kernel
      have hl : raw20790step2Labels = raw20790step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20790step1 raw20790step1Labels permutation14 hz
    mixedMoment B raw20790step2 raw20790step2Labels = mixedMoment B raw20790step3 raw20790step3Labels := by
      have ha : raw20790step3 = (fun i j => raw20790step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20790step3 raw20790step2; decide +kernel
      have hl : raw20790step3Labels = raw20790step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20790step2 raw20790step2Labels permutation7 permutation3
    mixedMoment B raw20790step3 raw20790step3Labels = mixedMoment B raw20790step4 raw20790step4Labels := by
      have ha : raw20790step4 = -raw20790step3 := by apply Matrix.ext; change ∀ i j, raw20790step4 i j = -(raw20790step3 i j); unfold raw20790step4 raw20790step3; decide +kernel
      have hl : raw20790step4Labels = raw20790step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1051 node1051Labels := by rfl

def raw20791 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20791step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20791step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20791step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20791step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20791 raw20791Labels = mixedMoment B node4440 node4440Labels := by
  calc
    mixedMoment B raw20791 raw20791Labels = mixedMoment B raw20791step0 raw20791step0Labels := by
      have hz : ∀ j, raw20791 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20791step0 = (fun i j => raw20791 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20791step0 raw20791; decide +kernel
      have hl : raw20791step0Labels = raw20791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20791 raw20791Labels permutation346 hz
    mixedMoment B raw20791step0 raw20791step0Labels = mixedMoment B raw20791step1 raw20791step1Labels := by
      have ha : raw20791step1 = (fun i j => raw20791step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20791step1 raw20791step0; decide +kernel
      have hl : raw20791step1Labels = raw20791step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20791step0 raw20791step0Labels permutation32 permutation7
    mixedMoment B raw20791step1 raw20791step1Labels = mixedMoment B raw20791step2 raw20791step2Labels := by
      have ha : raw20791step2 = raw20791step1 := by apply Matrix.ext; unfold raw20791step2 raw20791step1; decide +kernel
      have hl : raw20791step1Labels = labelEmbedding10 ∘ raw20791step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20791step1 raw20791step1Labels raw20791step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4440 node4440Labels := by rfl

def raw20792 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20792step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20792step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20792step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20792 raw20792Labels = mixedMoment B node4440 node4440Labels := by
  calc
    mixedMoment B raw20792 raw20792Labels = mixedMoment B raw20792step0 raw20792step0Labels := by
      have hz : ∀ j, raw20792 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20792step0 = (fun i j => raw20792 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20792step0 raw20792; decide +kernel
      have hl : raw20792step0Labels = raw20792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20792 raw20792Labels permutation265 hz
    mixedMoment B raw20792step0 raw20792step0Labels = mixedMoment B raw20792step1 raw20792step1Labels := by
      have ha : raw20792step1 = (fun i j => raw20792step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20792step1 raw20792step0; decide +kernel
      have hl : raw20792step1Labels = raw20792step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20792step0 raw20792step0Labels permutation32 permutation7
    mixedMoment B raw20792step1 raw20792step1Labels = mixedMoment B raw20792step2 raw20792step2Labels := by
      have ha : raw20792step2 = raw20792step1 := by apply Matrix.ext; unfold raw20792step2 raw20792step1; decide +kernel
      have hl : raw20792step1Labels = labelEmbedding10 ∘ raw20792step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20792step1 raw20792step1Labels raw20792step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4440 node4440Labels := by rfl

def raw20793 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20793step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20793step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20793step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw20793step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20793step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw20793step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20793 raw20793Labels = mixedMoment B node4476 node4476Labels := by
  calc
    mixedMoment B raw20793 raw20793Labels = mixedMoment B raw20793step0 raw20793step0Labels := by
      have hz : ∀ j, raw20793 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20793step0 = (fun i j => raw20793 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20793step0 raw20793; decide +kernel
      have hl : raw20793step0Labels = raw20793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20793 raw20793Labels permutation346 hz
    mixedMoment B raw20793step0 raw20793step0Labels = mixedMoment B raw20793step1 raw20793step1Labels := by
      have hz : ∀ j, raw20793step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20793step1 = (fun i j => raw20793step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20793step1 raw20793step0; decide +kernel
      have hl : raw20793step1Labels = raw20793step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20793step0 raw20793step0Labels permutation56 hz
    mixedMoment B raw20793step1 raw20793step1Labels = mixedMoment B raw20793step2 raw20793step2Labels := by
      have ha : raw20793step2 = (fun i j => raw20793step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20793step2 raw20793step1; decide +kernel
      have hl : raw20793step2Labels = raw20793step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20793step1 raw20793step1Labels permutation8 permutation7
    mixedMoment B raw20793step2 raw20793step2Labels = mixedMoment B raw20793step3 raw20793step3Labels := by
      have ha : raw20793step3 = raw20793step2 := by apply Matrix.ext; unfold raw20793step3 raw20793step2; decide +kernel
      have hl : raw20793step2Labels = labelEmbedding10 ∘ raw20793step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20793step2 raw20793step2Labels raw20793step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4476 node4476Labels := by rfl

def raw20794 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20794step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20794step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20794step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20794step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20794step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20794step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20794 raw20794Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw20794 raw20794Labels = mixedMoment B raw20794step0 raw20794step0Labels := by
      have hz : ∀ j, raw20794 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20794step0 = (fun i j => raw20794 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20794step0 raw20794; decide +kernel
      have hl : raw20794step0Labels = raw20794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20794 raw20794Labels permutation346 hz
    mixedMoment B raw20794step0 raw20794step0Labels = mixedMoment B raw20794step1 raw20794step1Labels := by
      have hz : ∀ j, raw20794step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20794step1 = (fun i j => raw20794step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20794step1 raw20794step0; decide +kernel
      have hl : raw20794step1Labels = raw20794step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20794step0 raw20794step0Labels permutation56 hz
    mixedMoment B raw20794step1 raw20794step1Labels = mixedMoment B raw20794step2 raw20794step2Labels := by
      have ha : raw20794step2 = (fun i j => raw20794step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20794step2 raw20794step1; decide +kernel
      have hl : raw20794step2Labels = raw20794step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20794step1 raw20794step1Labels permutation8 permutation7
    mixedMoment B raw20794step2 raw20794step2Labels = mixedMoment B raw20794step3 raw20794step3Labels := by
      have ha : raw20794step3 = raw20794step2 := by apply Matrix.ext; unfold raw20794step3 raw20794step2; decide +kernel
      have hl : raw20794step2Labels = labelEmbedding10 ∘ raw20794step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20794step2 raw20794step2Labels raw20794step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4460 node4460Labels := by rfl

def raw20795 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20795step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20795step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20795step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20795step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20795 raw20795Labels = mixedMoment B node4401 node4401Labels := by
  calc
    mixedMoment B raw20795 raw20795Labels = mixedMoment B raw20795step0 raw20795step0Labels := by
      have hz : ∀ j, raw20795 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20795step0 = (fun i j => raw20795 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20795step0 raw20795; decide +kernel
      have hl : raw20795step0Labels = raw20795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20795 raw20795Labels permutation346 hz
    mixedMoment B raw20795step0 raw20795step0Labels = mixedMoment B raw20795step1 raw20795step1Labels := by
      have ha : raw20795step1 = (fun i j => raw20795step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20795step1 raw20795step0; decide +kernel
      have hl : raw20795step1Labels = raw20795step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20795step0 raw20795step0Labels permutation38 permutation6
    mixedMoment B raw20795step1 raw20795step1Labels = mixedMoment B raw20795step2 raw20795step2Labels := by
      have ha : raw20795step2 = raw20795step1 := by apply Matrix.ext; unfold raw20795step2 raw20795step1; decide +kernel
      have hl : raw20795step1Labels = labelEmbedding9 ∘ raw20795step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20795step1 raw20795step1Labels raw20795step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4401 node4401Labels := by rfl

def raw20796 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20796step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20796step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20796 raw20796Labels = mixedMoment B node4577 node4577Labels := by
  calc
    mixedMoment B raw20796 raw20796Labels = mixedMoment B raw20796step0 raw20796step0Labels := by
      have ha : raw20796step0 = (fun i j => raw20796 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20796step0 raw20796; decide +kernel
      have hl : raw20796step0Labels = raw20796Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20796 raw20796Labels permutation182 permutation6
    mixedMoment B raw20796step0 raw20796step0Labels = mixedMoment B raw20796step1 raw20796step1Labels := by
      have ha : raw20796step1 = raw20796step0 := by apply Matrix.ext; unfold raw20796step1 raw20796step0; decide +kernel
      have hl : raw20796step0Labels = labelEmbedding9 ∘ raw20796step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20796step0 raw20796step0Labels raw20796step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4577 node4577Labels := by rfl

def raw20797 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20797step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20797step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20797step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20797 raw20797Labels = mixedMoment B node4564 node4564Labels := by
  calc
    mixedMoment B raw20797 raw20797Labels = mixedMoment B raw20797step0 raw20797step0Labels := by
      have hz : ∀ j, raw20797 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20797step0 = (fun i j => raw20797 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20797step0 raw20797; decide +kernel
      have hl : raw20797step0Labels = raw20797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20797 raw20797Labels permutation346 hz
    mixedMoment B raw20797step0 raw20797step0Labels = mixedMoment B raw20797step1 raw20797step1Labels := by
      have ha : raw20797step1 = (fun i j => raw20797step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20797step1 raw20797step0; decide +kernel
      have hl : raw20797step1Labels = raw20797step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20797step0 raw20797step0Labels permutation38 permutation6
    mixedMoment B raw20797step1 raw20797step1Labels = mixedMoment B raw20797step2 raw20797step2Labels := by
      have ha : raw20797step2 = raw20797step1 := by apply Matrix.ext; unfold raw20797step2 raw20797step1; decide +kernel
      have hl : raw20797step1Labels = labelEmbedding9 ∘ raw20797step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20797step1 raw20797step1Labels raw20797step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4564 node4564Labels := by rfl

def raw20798 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20798step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20798step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20798step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20798step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20798 raw20798Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw20798 raw20798Labels = mixedMoment B raw20798step0 raw20798step0Labels := by
      have hz : ∀ j, raw20798 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20798step0 = (fun i j => raw20798 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20798step0 raw20798; decide +kernel
      have hl : raw20798step0Labels = raw20798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20798 raw20798Labels permutation346 hz
    mixedMoment B raw20798step0 raw20798step0Labels = mixedMoment B raw20798step1 raw20798step1Labels := by
      have ha : raw20798step1 = (fun i j => raw20798step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20798step1 raw20798step0; decide +kernel
      have hl : raw20798step1Labels = raw20798step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20798step0 raw20798step0Labels permutation32 permutation7
    mixedMoment B raw20798step1 raw20798step1Labels = mixedMoment B raw20798step2 raw20798step2Labels := by
      have ha : raw20798step2 = raw20798step1 := by apply Matrix.ext; unfold raw20798step2 raw20798step1; decide +kernel
      have hl : raw20798step1Labels = labelEmbedding10 ∘ raw20798step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20798step1 raw20798step1Labels raw20798step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw20799 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20799step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20799step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20799step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20799 raw20799Labels = mixedMoment B node4401 node4401Labels := by
  calc
    mixedMoment B raw20799 raw20799Labels = mixedMoment B raw20799step0 raw20799step0Labels := by
      have hz : ∀ j, raw20799 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20799step0 = (fun i j => raw20799 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20799step0 raw20799; decide +kernel
      have hl : raw20799step0Labels = raw20799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20799 raw20799Labels permutation265 hz
    mixedMoment B raw20799step0 raw20799step0Labels = mixedMoment B raw20799step1 raw20799step1Labels := by
      have ha : raw20799step1 = (fun i j => raw20799step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20799step1 raw20799step0; decide +kernel
      have hl : raw20799step1Labels = raw20799step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20799step0 raw20799step0Labels permutation38 permutation6
    mixedMoment B raw20799step1 raw20799step1Labels = mixedMoment B raw20799step2 raw20799step2Labels := by
      have ha : raw20799step2 = raw20799step1 := by apply Matrix.ext; unfold raw20799step2 raw20799step1; decide +kernel
      have hl : raw20799step1Labels = labelEmbedding9 ∘ raw20799step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20799step1 raw20799step1Labels raw20799step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4401 node4401Labels := by rfl

def raw20800 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20800step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20800step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20800step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20800 raw20800Labels = mixedMoment B node4577 node4577Labels := by
  calc
    mixedMoment B raw20800 raw20800Labels = mixedMoment B raw20800step0 raw20800step0Labels := by
      have ha : raw20800step0 = (fun i j => raw20800 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20800step0 raw20800; decide +kernel
      have hl : raw20800step0Labels = raw20800Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20800 raw20800Labels permutation158 permutation6
    mixedMoment B raw20800step0 raw20800step0Labels = mixedMoment B raw20800step1 raw20800step1Labels := by
      have ha : raw20800step1 = raw20800step0 := by apply Matrix.ext; unfold raw20800step1 raw20800step0; decide +kernel
      have hl : raw20800step0Labels = labelEmbedding9 ∘ raw20800step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20800step0 raw20800step0Labels raw20800step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4577 node4577Labels := by rfl

def raw20801 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20801step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20801step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20801step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20801step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20801 raw20801Labels = mixedMoment B node4564 node4564Labels := by
  calc
    mixedMoment B raw20801 raw20801Labels = mixedMoment B raw20801step0 raw20801step0Labels := by
      have hz : ∀ j, raw20801 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20801step0 = (fun i j => raw20801 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20801step0 raw20801; decide +kernel
      have hl : raw20801step0Labels = raw20801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20801 raw20801Labels permutation265 hz
    mixedMoment B raw20801step0 raw20801step0Labels = mixedMoment B raw20801step1 raw20801step1Labels := by
      have ha : raw20801step1 = (fun i j => raw20801step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20801step1 raw20801step0; decide +kernel
      have hl : raw20801step1Labels = raw20801step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20801step0 raw20801step0Labels permutation38 permutation6
    mixedMoment B raw20801step1 raw20801step1Labels = mixedMoment B raw20801step2 raw20801step2Labels := by
      have ha : raw20801step2 = raw20801step1 := by apply Matrix.ext; unfold raw20801step2 raw20801step1; decide +kernel
      have hl : raw20801step1Labels = labelEmbedding9 ∘ raw20801step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20801step1 raw20801step1Labels raw20801step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4564 node4564Labels := by rfl

def raw20802 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20802Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20802step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20802step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20802step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20802step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20802 raw20802Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw20802 raw20802Labels = mixedMoment B raw20802step0 raw20802step0Labels := by
      have hz : ∀ j, raw20802 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20802step0 = (fun i j => raw20802 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20802step0 raw20802; decide +kernel
      have hl : raw20802step0Labels = raw20802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20802 raw20802Labels permutation265 hz
    mixedMoment B raw20802step0 raw20802step0Labels = mixedMoment B raw20802step1 raw20802step1Labels := by
      have ha : raw20802step1 = (fun i j => raw20802step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20802step1 raw20802step0; decide +kernel
      have hl : raw20802step1Labels = raw20802step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20802step0 raw20802step0Labels permutation32 permutation7
    mixedMoment B raw20802step1 raw20802step1Labels = mixedMoment B raw20802step2 raw20802step2Labels := by
      have ha : raw20802step2 = raw20802step1 := by apply Matrix.ext; unfold raw20802step2 raw20802step1; decide +kernel
      have hl : raw20802step1Labels = labelEmbedding10 ∘ raw20802step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20802step1 raw20802step1Labels raw20802step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw20803 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20803step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20803step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20803step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20803step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw20803step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20803step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw20803step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20803 raw20803Labels = mixedMoment B node4428 node4428Labels := by
  calc
    mixedMoment B raw20803 raw20803Labels = mixedMoment B raw20803step0 raw20803step0Labels := by
      have hz : ∀ j, raw20803 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20803step0 = (fun i j => raw20803 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20803step0 raw20803; decide +kernel
      have hl : raw20803step0Labels = raw20803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20803 raw20803Labels permutation346 hz
    mixedMoment B raw20803step0 raw20803step0Labels = mixedMoment B raw20803step1 raw20803step1Labels := by
      have hz : ∀ j, raw20803step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20803step1 = (fun i j => raw20803step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20803step1 raw20803step0; decide +kernel
      have hl : raw20803step1Labels = raw20803step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20803step0 raw20803step0Labels permutation56 hz
    mixedMoment B raw20803step1 raw20803step1Labels = mixedMoment B raw20803step2 raw20803step2Labels := by
      have ha : raw20803step2 = (fun i j => raw20803step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20803step2 raw20803step1; decide +kernel
      have hl : raw20803step2Labels = raw20803step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20803step1 raw20803step1Labels permutation8 permutation6
    mixedMoment B raw20803step2 raw20803step2Labels = mixedMoment B raw20803step3 raw20803step3Labels := by
      have ha : raw20803step3 = raw20803step2 := by apply Matrix.ext; unfold raw20803step3 raw20803step2; decide +kernel
      have hl : raw20803step2Labels = labelEmbedding9 ∘ raw20803step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20803step2 raw20803step2Labels raw20803step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4428 node4428Labels := by rfl

def raw20804 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20804Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20804step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw20804step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20804step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw20804step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20804 raw20804Labels = mixedMoment B node4584 node4584Labels := by
  calc
    mixedMoment B raw20804 raw20804Labels = mixedMoment B raw20804step0 raw20804step0Labels := by
      have hz : ∀ j, raw20804 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20804step0 = (fun i j => raw20804 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20804step0 raw20804; decide +kernel
      have hl : raw20804step0Labels = raw20804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20804 raw20804Labels permutation346 hz
    mixedMoment B raw20804step0 raw20804step0Labels = mixedMoment B raw20804step1 raw20804step1Labels := by
      have ha : raw20804step1 = (fun i j => raw20804step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20804step1 raw20804step0; decide +kernel
      have hl : raw20804step1Labels = raw20804step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20804step0 raw20804step0Labels permutation32 permutation6
    mixedMoment B raw20804step1 raw20804step1Labels = mixedMoment B raw20804step2 raw20804step2Labels := by
      have ha : raw20804step2 = raw20804step1 := by apply Matrix.ext; unfold raw20804step2 raw20804step1; decide +kernel
      have hl : raw20804step1Labels = labelEmbedding9 ∘ raw20804step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20804step1 raw20804step1Labels raw20804step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4584 node4584Labels := by rfl

def raw20805 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20805Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20805step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw20805step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20805step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw20805step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20805 raw20805Labels = mixedMoment B node4584 node4584Labels := by
  calc
    mixedMoment B raw20805 raw20805Labels = mixedMoment B raw20805step0 raw20805step0Labels := by
      have hz : ∀ j, raw20805 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20805step0 = (fun i j => raw20805 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20805step0 raw20805; decide +kernel
      have hl : raw20805step0Labels = raw20805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20805 raw20805Labels permutation265 hz
    mixedMoment B raw20805step0 raw20805step0Labels = mixedMoment B raw20805step1 raw20805step1Labels := by
      have ha : raw20805step1 = (fun i j => raw20805step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20805step1 raw20805step0; decide +kernel
      have hl : raw20805step1Labels = raw20805step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20805step0 raw20805step0Labels permutation32 permutation6
    mixedMoment B raw20805step1 raw20805step1Labels = mixedMoment B raw20805step2 raw20805step2Labels := by
      have ha : raw20805step2 = raw20805step1 := by apply Matrix.ext; unfold raw20805step2 raw20805step1; decide +kernel
      have hl : raw20805step1Labels = labelEmbedding9 ∘ raw20805step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20805step1 raw20805step1Labels raw20805step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4584 node4584Labels := by rfl

def raw20806 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20806step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20806step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20806step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20806step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw20806step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20806step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw20806step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20806 raw20806Labels = mixedMoment B node4573 node4573Labels := by
  calc
    mixedMoment B raw20806 raw20806Labels = mixedMoment B raw20806step0 raw20806step0Labels := by
      have hz : ∀ j, raw20806 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20806step0 = (fun i j => raw20806 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20806step0 raw20806; decide +kernel
      have hl : raw20806step0Labels = raw20806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20806 raw20806Labels permutation346 hz
    mixedMoment B raw20806step0 raw20806step0Labels = mixedMoment B raw20806step1 raw20806step1Labels := by
      have hz : ∀ j, raw20806step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20806step1 = (fun i j => raw20806step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20806step1 raw20806step0; decide +kernel
      have hl : raw20806step1Labels = raw20806step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20806step0 raw20806step0Labels permutation56 hz
    mixedMoment B raw20806step1 raw20806step1Labels = mixedMoment B raw20806step2 raw20806step2Labels := by
      have ha : raw20806step2 = (fun i j => raw20806step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20806step2 raw20806step1; decide +kernel
      have hl : raw20806step2Labels = raw20806step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20806step1 raw20806step1Labels permutation8 permutation6
    mixedMoment B raw20806step2 raw20806step2Labels = mixedMoment B raw20806step3 raw20806step3Labels := by
      have ha : raw20806step3 = raw20806step2 := by apply Matrix.ext; unfold raw20806step3 raw20806step2; decide +kernel
      have hl : raw20806step2Labels = labelEmbedding9 ∘ raw20806step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20806step2 raw20806step2Labels raw20806step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4573 node4573Labels := by rfl

def raw20807 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20807step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20807step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20807step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20807step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20807step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20807step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20807 raw20807Labels = mixedMoment B node4609 node4609Labels := by
  calc
    mixedMoment B raw20807 raw20807Labels = mixedMoment B raw20807step0 raw20807step0Labels := by
      have hz : ∀ j, raw20807 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20807step0 = (fun i j => raw20807 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20807step0 raw20807; decide +kernel
      have hl : raw20807step0Labels = raw20807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20807 raw20807Labels permutation346 hz
    mixedMoment B raw20807step0 raw20807step0Labels = mixedMoment B raw20807step1 raw20807step1Labels := by
      have hz : ∀ j, raw20807step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20807step1 = (fun i j => raw20807step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20807step1 raw20807step0; decide +kernel
      have hl : raw20807step1Labels = raw20807step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20807step0 raw20807step0Labels permutation56 hz
    mixedMoment B raw20807step1 raw20807step1Labels = mixedMoment B raw20807step2 raw20807step2Labels := by
      have ha : raw20807step2 = (fun i j => raw20807step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20807step2 raw20807step1; decide +kernel
      have hl : raw20807step2Labels = raw20807step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20807step1 raw20807step1Labels permutation8 permutation6
    mixedMoment B raw20807step2 raw20807step2Labels = mixedMoment B raw20807step3 raw20807step3Labels := by
      have ha : raw20807step3 = raw20807step2 := by apply Matrix.ext; unfold raw20807step3 raw20807step2; decide +kernel
      have hl : raw20807step2Labels = labelEmbedding9 ∘ raw20807step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20807step2 raw20807step2Labels raw20807step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4609 node4609Labels := by rfl

def raw20808 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20808step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20808step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20808step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20808step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20808step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20808step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20808step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20808 raw20808Labels = mixedMoment B node4426 node4426Labels := by
  calc
    mixedMoment B raw20808 raw20808Labels = mixedMoment B raw20808step0 raw20808step0Labels := by
      have hz : ∀ j, raw20808 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20808step0 = (fun i j => raw20808 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20808step0 raw20808; decide +kernel
      have hl : raw20808step0Labels = raw20808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20808 raw20808Labels permutation346 hz
    mixedMoment B raw20808step0 raw20808step0Labels = mixedMoment B raw20808step1 raw20808step1Labels := by
      have hz : ∀ j, raw20808step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20808step1 = (fun i j => raw20808step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20808step1 raw20808step0; decide +kernel
      have hl : raw20808step1Labels = raw20808step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20808step0 raw20808step0Labels permutation56 hz
    mixedMoment B raw20808step1 raw20808step1Labels = mixedMoment B raw20808step2 raw20808step2Labels := by
      have ha : raw20808step2 = (fun i j => raw20808step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20808step2 raw20808step1; decide +kernel
      have hl : raw20808step2Labels = raw20808step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20808step1 raw20808step1Labels permutation8 permutation6
    mixedMoment B raw20808step2 raw20808step2Labels = mixedMoment B raw20808step3 raw20808step3Labels := by
      have ha : raw20808step3 = raw20808step2 := by apply Matrix.ext; unfold raw20808step3 raw20808step2; decide +kernel
      have hl : raw20808step2Labels = labelEmbedding9 ∘ raw20808step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20808step2 raw20808step2Labels raw20808step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4426 node4426Labels := by rfl

def raw20809 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20809step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20809step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20809step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20809step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20809 raw20809Labels = mixedMoment B node4583 node4583Labels := by
  calc
    mixedMoment B raw20809 raw20809Labels = mixedMoment B raw20809step0 raw20809step0Labels := by
      have hz : ∀ j, raw20809 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20809step0 = (fun i j => raw20809 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20809step0 raw20809; decide +kernel
      have hl : raw20809step0Labels = raw20809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20809 raw20809Labels permutation346 hz
    mixedMoment B raw20809step0 raw20809step0Labels = mixedMoment B raw20809step1 raw20809step1Labels := by
      have ha : raw20809step1 = (fun i j => raw20809step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20809step1 raw20809step0; decide +kernel
      have hl : raw20809step1Labels = raw20809step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20809step0 raw20809step0Labels permutation32 permutation6
    mixedMoment B raw20809step1 raw20809step1Labels = mixedMoment B raw20809step2 raw20809step2Labels := by
      have ha : raw20809step2 = raw20809step1 := by apply Matrix.ext; unfold raw20809step2 raw20809step1; decide +kernel
      have hl : raw20809step1Labels = labelEmbedding9 ∘ raw20809step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20809step1 raw20809step1Labels raw20809step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4583 node4583Labels := by rfl

def raw20810 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20810step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20810step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20810step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20810 raw20810Labels = mixedMoment B node4583 node4583Labels := by
  calc
    mixedMoment B raw20810 raw20810Labels = mixedMoment B raw20810step0 raw20810step0Labels := by
      have hz : ∀ j, raw20810 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20810step0 = (fun i j => raw20810 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20810step0 raw20810; decide +kernel
      have hl : raw20810step0Labels = raw20810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20810 raw20810Labels permutation265 hz
    mixedMoment B raw20810step0 raw20810step0Labels = mixedMoment B raw20810step1 raw20810step1Labels := by
      have ha : raw20810step1 = (fun i j => raw20810step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20810step1 raw20810step0; decide +kernel
      have hl : raw20810step1Labels = raw20810step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20810step0 raw20810step0Labels permutation32 permutation6
    mixedMoment B raw20810step1 raw20810step1Labels = mixedMoment B raw20810step2 raw20810step2Labels := by
      have ha : raw20810step2 = raw20810step1 := by apply Matrix.ext; unfold raw20810step2 raw20810step1; decide +kernel
      have hl : raw20810step1Labels = labelEmbedding9 ∘ raw20810step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20810step1 raw20810step1Labels raw20810step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4583 node4583Labels := by rfl

def raw20811 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20811step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20811step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20811step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20811step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw20811step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20811step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw20811step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20811 raw20811Labels = mixedMoment B node4572 node4572Labels := by
  calc
    mixedMoment B raw20811 raw20811Labels = mixedMoment B raw20811step0 raw20811step0Labels := by
      have hz : ∀ j, raw20811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20811step0 = (fun i j => raw20811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20811step0 raw20811; decide +kernel
      have hl : raw20811step0Labels = raw20811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20811 raw20811Labels permutation346 hz
    mixedMoment B raw20811step0 raw20811step0Labels = mixedMoment B raw20811step1 raw20811step1Labels := by
      have hz : ∀ j, raw20811step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20811step1 = (fun i j => raw20811step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20811step1 raw20811step0; decide +kernel
      have hl : raw20811step1Labels = raw20811step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20811step0 raw20811step0Labels permutation56 hz
    mixedMoment B raw20811step1 raw20811step1Labels = mixedMoment B raw20811step2 raw20811step2Labels := by
      have ha : raw20811step2 = (fun i j => raw20811step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20811step2 raw20811step1; decide +kernel
      have hl : raw20811step2Labels = raw20811step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20811step1 raw20811step1Labels permutation8 permutation6
    mixedMoment B raw20811step2 raw20811step2Labels = mixedMoment B raw20811step3 raw20811step3Labels := by
      have ha : raw20811step3 = raw20811step2 := by apply Matrix.ext; unfold raw20811step3 raw20811step2; decide +kernel
      have hl : raw20811step2Labels = labelEmbedding9 ∘ raw20811step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20811step2 raw20811step2Labels raw20811step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4572 node4572Labels := by rfl

def raw20812 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20812Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20812step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20812step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20812 raw20812Labels = mixedMoment B node1388 node1388Labels := by
  calc
    mixedMoment B raw20812 raw20812Labels = mixedMoment B raw20812step0 raw20812step0Labels := by
      have hz : ∀ j, raw20812 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20812step0 = (fun i j => raw20812 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20812step0 raw20812; decide +kernel
      have hl : raw20812step0Labels = raw20812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20812 raw20812Labels permutation346 hz
    mixedMoment B raw20812step0 raw20812step0Labels = mixedMoment B raw20812step1 raw20812step1Labels := by
      have ha : raw20812step1 = (fun i j => raw20812step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20812step1 raw20812step0; decide +kernel
      have hl : raw20812step1Labels = raw20812step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20812step0 raw20812step0Labels permutation32 permutation6
    _ = mixedMoment B node1388 node1388Labels := by rfl

def raw20813 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20813Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20813step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20813step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20813 raw20813Labels = mixedMoment B node1388 node1388Labels := by
  calc
    mixedMoment B raw20813 raw20813Labels = mixedMoment B raw20813step0 raw20813step0Labels := by
      have hz : ∀ j, raw20813 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20813step0 = (fun i j => raw20813 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20813step0 raw20813; decide +kernel
      have hl : raw20813step0Labels = raw20813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20813 raw20813Labels permutation265 hz
    mixedMoment B raw20813step0 raw20813step0Labels = mixedMoment B raw20813step1 raw20813step1Labels := by
      have ha : raw20813step1 = (fun i j => raw20813step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20813step1 raw20813step0; decide +kernel
      have hl : raw20813step1Labels = raw20813step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20813step0 raw20813step0Labels permutation32 permutation6
    _ = mixedMoment B node1388 node1388Labels := by rfl

def raw20814 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20814Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20814step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20814step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20814step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20814step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20814step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20814 raw20814Labels = mixedMoment B node1372 node1372Labels := by
  calc
    mixedMoment B raw20814 raw20814Labels = mixedMoment B raw20814step0 raw20814step0Labels := by
      have hz : ∀ j, raw20814 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20814step0 = (fun i j => raw20814 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20814step0 raw20814; decide +kernel
      have hl : raw20814step0Labels = raw20814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20814 raw20814Labels permutation346 hz
    mixedMoment B raw20814step0 raw20814step0Labels = mixedMoment B raw20814step1 raw20814step1Labels := by
      have hz : ∀ j, raw20814step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20814step1 = (fun i j => raw20814step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20814step1 raw20814step0; decide +kernel
      have hl : raw20814step1Labels = raw20814step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20814step0 raw20814step0Labels permutation56 hz
    mixedMoment B raw20814step1 raw20814step1Labels = mixedMoment B raw20814step2 raw20814step2Labels := by
      have ha : raw20814step2 = (fun i j => raw20814step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20814step2 raw20814step1; decide +kernel
      have hl : raw20814step2Labels = raw20814step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20814step1 raw20814step1Labels permutation8 permutation6
    _ = mixedMoment B node1372 node1372Labels := by rfl

def raw20815 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20815Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20815step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20815step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20815step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20815step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw20815step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20815 raw20815Labels = mixedMoment B node1413 node1413Labels := by
  calc
    mixedMoment B raw20815 raw20815Labels = mixedMoment B raw20815step0 raw20815step0Labels := by
      have hz : ∀ j, raw20815 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20815step0 = (fun i j => raw20815 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20815step0 raw20815; decide +kernel
      have hl : raw20815step0Labels = raw20815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20815 raw20815Labels permutation346 hz
    mixedMoment B raw20815step0 raw20815step0Labels = mixedMoment B raw20815step1 raw20815step1Labels := by
      have hz : ∀ j, raw20815step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20815step1 = (fun i j => raw20815step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20815step1 raw20815step0; decide +kernel
      have hl : raw20815step1Labels = raw20815step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20815step0 raw20815step0Labels permutation56 hz
    mixedMoment B raw20815step1 raw20815step1Labels = mixedMoment B raw20815step2 raw20815step2Labels := by
      have ha : raw20815step2 = (fun i j => raw20815step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20815step2 raw20815step1; decide +kernel
      have hl : raw20815step2Labels = raw20815step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20815step1 raw20815step1Labels permutation8 permutation6
    _ = mixedMoment B node1413 node1413Labels := by rfl

def raw20816 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20816Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20816step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20816step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20816step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20816step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20816step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20816 raw20816Labels = mixedMoment B node1416 node1416Labels := by
  calc
    mixedMoment B raw20816 raw20816Labels = mixedMoment B raw20816step0 raw20816step0Labels := by
      have hz : ∀ j, raw20816 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20816step0 = (fun i j => raw20816 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20816step0 raw20816; decide +kernel
      have hl : raw20816step0Labels = raw20816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20816 raw20816Labels permutation346 hz
    mixedMoment B raw20816step0 raw20816step0Labels = mixedMoment B raw20816step1 raw20816step1Labels := by
      have hz : ∀ j, raw20816step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20816step1 = (fun i j => raw20816step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20816step1 raw20816step0; decide +kernel
      have hl : raw20816step1Labels = raw20816step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20816step0 raw20816step0Labels permutation56 hz
    mixedMoment B raw20816step1 raw20816step1Labels = mixedMoment B raw20816step2 raw20816step2Labels := by
      have ha : raw20816step2 = (fun i j => raw20816step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20816step2 raw20816step1; decide +kernel
      have hl : raw20816step2Labels = raw20816step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20816step1 raw20816step1Labels permutation8 permutation6
    _ = mixedMoment B node1416 node1416Labels := by rfl

def raw20817 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20817Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20817step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20817step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20817 raw20817Labels = mixedMoment B node982 node982Labels := by
  calc
    mixedMoment B raw20817 raw20817Labels = mixedMoment B raw20817step0 raw20817step0Labels := by
      have hz : ∀ j, raw20817 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20817step0 = (fun i j => raw20817 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20817step0 raw20817; decide +kernel
      have hl : raw20817step0Labels = raw20817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20817 raw20817Labels permutation346 hz
    mixedMoment B raw20817step0 raw20817step0Labels = mixedMoment B raw20817step1 raw20817step1Labels := by
      have ha : raw20817step1 = (fun i j => raw20817step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20817step1 raw20817step0; decide +kernel
      have hl : raw20817step1Labels = raw20817step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20817step0 raw20817step0Labels permutation38 permutation6
    _ = mixedMoment B node982 node982Labels := by rfl

def raw20818 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20818Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20818step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20818 raw20818Labels = mixedMoment B node1195 node1195Labels := by
  calc
    mixedMoment B raw20818 raw20818Labels = mixedMoment B raw20818step0 raw20818step0Labels := by
      have ha : raw20818step0 = (fun i j => raw20818 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20818step0 raw20818; decide +kernel
      have hl : raw20818step0Labels = raw20818Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20818 raw20818Labels permutation182 permutation6
    _ = mixedMoment B node1195 node1195Labels := by rfl

def raw20819 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20819Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20819step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20819step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20819 raw20819Labels = mixedMoment B node1181 node1181Labels := by
  calc
    mixedMoment B raw20819 raw20819Labels = mixedMoment B raw20819step0 raw20819step0Labels := by
      have hz : ∀ j, raw20819 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20819step0 = (fun i j => raw20819 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20819step0 raw20819; decide +kernel
      have hl : raw20819step0Labels = raw20819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20819 raw20819Labels permutation346 hz
    mixedMoment B raw20819step0 raw20819step0Labels = mixedMoment B raw20819step1 raw20819step1Labels := by
      have ha : raw20819step1 = (fun i j => raw20819step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20819step1 raw20819step0; decide +kernel
      have hl : raw20819step1Labels = raw20819step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20819step0 raw20819step0Labels permutation38 permutation6
    _ = mixedMoment B node1181 node1181Labels := by rfl

def raw20820 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20820Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20820step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20820step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20820 raw20820Labels = mixedMoment B node1215 node1215Labels := by
  calc
    mixedMoment B raw20820 raw20820Labels = mixedMoment B raw20820step0 raw20820step0Labels := by
      have hz : ∀ j, raw20820 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20820step0 = (fun i j => raw20820 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20820step0 raw20820; decide +kernel
      have hl : raw20820step0Labels = raw20820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20820 raw20820Labels permutation346 hz
    mixedMoment B raw20820step0 raw20820step0Labels = mixedMoment B raw20820step1 raw20820step1Labels := by
      have ha : raw20820step1 = (fun i j => raw20820step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20820step1 raw20820step0; decide +kernel
      have hl : raw20820step1Labels = raw20820step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20820step0 raw20820step0Labels permutation38 permutation6
    _ = mixedMoment B node1215 node1215Labels := by rfl

def raw20821 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20821Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20821step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20821step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20821 raw20821Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw20821 raw20821Labels = mixedMoment B raw20821step0 raw20821step0Labels := by
      have hz : ∀ j, raw20821 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20821step0 = (fun i j => raw20821 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20821step0 raw20821; decide +kernel
      have hl : raw20821step0Labels = raw20821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20821 raw20821Labels permutation346 hz
    mixedMoment B raw20821step0 raw20821step0Labels = mixedMoment B raw20821step1 raw20821step1Labels := by
      have ha : raw20821step1 = (fun i j => raw20821step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20821step1 raw20821step0; decide +kernel
      have hl : raw20821step1Labels = raw20821step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20821step0 raw20821step0Labels permutation38 permutation6
    _ = mixedMoment B node1217 node1217Labels := by rfl

def raw20822 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20822Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20822step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20822step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20822 raw20822Labels = mixedMoment B node982 node982Labels := by
  calc
    mixedMoment B raw20822 raw20822Labels = mixedMoment B raw20822step0 raw20822step0Labels := by
      have hz : ∀ j, raw20822 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20822step0 = (fun i j => raw20822 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20822step0 raw20822; decide +kernel
      have hl : raw20822step0Labels = raw20822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20822 raw20822Labels permutation265 hz
    mixedMoment B raw20822step0 raw20822step0Labels = mixedMoment B raw20822step1 raw20822step1Labels := by
      have ha : raw20822step1 = (fun i j => raw20822step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20822step1 raw20822step0; decide +kernel
      have hl : raw20822step1Labels = raw20822step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20822step0 raw20822step0Labels permutation38 permutation6
    _ = mixedMoment B node982 node982Labels := by rfl

def raw20823 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20823Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20823step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20823 raw20823Labels = mixedMoment B node1195 node1195Labels := by
  calc
    mixedMoment B raw20823 raw20823Labels = mixedMoment B raw20823step0 raw20823step0Labels := by
      have ha : raw20823step0 = (fun i j => raw20823 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20823step0 raw20823; decide +kernel
      have hl : raw20823step0Labels = raw20823Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20823 raw20823Labels permutation158 permutation6
    _ = mixedMoment B node1195 node1195Labels := by rfl

def raw20824 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20824Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20824step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20824 raw20824Labels = mixedMoment B node1181 node1181Labels := by
  calc
    mixedMoment B raw20824 raw20824Labels = mixedMoment B raw20824step0 raw20824step0Labels := by
      have hz : ∀ j, raw20824 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20824step0 = (fun i j => raw20824 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20824step0 raw20824; decide +kernel
      have hl : raw20824step0Labels = raw20824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20824 raw20824Labels permutation265 hz
    mixedMoment B raw20824step0 raw20824step0Labels = mixedMoment B raw20824step1 raw20824step1Labels := by
      have ha : raw20824step1 = (fun i j => raw20824step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20824step1 raw20824step0; decide +kernel
      have hl : raw20824step1Labels = raw20824step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20824step0 raw20824step0Labels permutation38 permutation6
    _ = mixedMoment B node1181 node1181Labels := by rfl

def raw20825 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20825Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20825step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20825step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20825 raw20825Labels = mixedMoment B node1215 node1215Labels := by
  calc
    mixedMoment B raw20825 raw20825Labels = mixedMoment B raw20825step0 raw20825step0Labels := by
      have hz : ∀ j, raw20825 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20825step0 = (fun i j => raw20825 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20825step0 raw20825; decide +kernel
      have hl : raw20825step0Labels = raw20825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20825 raw20825Labels permutation265 hz
    mixedMoment B raw20825step0 raw20825step0Labels = mixedMoment B raw20825step1 raw20825step1Labels := by
      have ha : raw20825step1 = (fun i j => raw20825step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20825step1 raw20825step0; decide +kernel
      have hl : raw20825step1Labels = raw20825step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20825step0 raw20825step0Labels permutation38 permutation6
    _ = mixedMoment B node1215 node1215Labels := by rfl

def raw20826 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20826Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20826step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20826step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20826 raw20826Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw20826 raw20826Labels = mixedMoment B raw20826step0 raw20826step0Labels := by
      have hz : ∀ j, raw20826 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20826step0 = (fun i j => raw20826 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20826step0 raw20826; decide +kernel
      have hl : raw20826step0Labels = raw20826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20826 raw20826Labels permutation265 hz
    mixedMoment B raw20826step0 raw20826step0Labels = mixedMoment B raw20826step1 raw20826step1Labels := by
      have ha : raw20826step1 = (fun i j => raw20826step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20826step1 raw20826step0; decide +kernel
      have hl : raw20826step1Labels = raw20826step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20826step0 raw20826step0Labels permutation38 permutation6
    _ = mixedMoment B node1217 node1217Labels := by rfl

def raw20827 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20827Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20827step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20827step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20827step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20827step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, -2, 3]]
def raw20827step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20827step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw20827step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20827 raw20827Labels = mixedMoment B node1089 node1089Labels := by
  calc
    mixedMoment B raw20827 raw20827Labels = mixedMoment B raw20827step0 raw20827step0Labels := by
      have hz : ∀ j, raw20827 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20827step0 = (fun i j => raw20827 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20827step0 raw20827; decide +kernel
      have hl : raw20827step0Labels = raw20827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20827 raw20827Labels permutation434 hz
    mixedMoment B raw20827step0 raw20827step0Labels = mixedMoment B raw20827step1 raw20827step1Labels := by
      have hz : ∀ j, raw20827step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20827step1 = (fun i j => raw20827step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20827step1 raw20827step0; decide +kernel
      have hl : raw20827step1Labels = raw20827step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20827step0 raw20827step0Labels permutation80 hz
    mixedMoment B raw20827step1 raw20827step1Labels = mixedMoment B raw20827step2 raw20827step2Labels := by
      have hz : ∀ j, raw20827step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20827step2 = (fun i j => raw20827step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20827step2 raw20827step1; decide +kernel
      have hl : raw20827step2Labels = raw20827step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20827step1 raw20827step1Labels permutation14 hz
    mixedMoment B raw20827step2 raw20827step2Labels = mixedMoment B raw20827step3 raw20827step3Labels := by
      have ha : raw20827step3 = (fun i j => raw20827step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20827step3 raw20827step2; decide +kernel
      have hl : raw20827step3Labels = raw20827step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20827step2 raw20827step2Labels permutation2 permutation6
    _ = mixedMoment B node1089 node1089Labels := by rfl

def raw20828 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20828Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20828step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20828step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20828step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20828step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20828step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20828 raw20828Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw20828 raw20828Labels = mixedMoment B raw20828step0 raw20828step0Labels := by
      have hz : ∀ j, raw20828 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20828step0 = (fun i j => raw20828 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20828step0 raw20828; decide +kernel
      have hl : raw20828step0Labels = raw20828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20828 raw20828Labels permutation434 hz
    mixedMoment B raw20828step0 raw20828step0Labels = mixedMoment B raw20828step1 raw20828step1Labels := by
      have hz : ∀ j, raw20828step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20828step1 = (fun i j => raw20828step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20828step1 raw20828step0; decide +kernel
      have hl : raw20828step1Labels = raw20828step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20828step0 raw20828step0Labels permutation80 hz
    mixedMoment B raw20828step1 raw20828step1Labels = mixedMoment B raw20828step2 raw20828step2Labels := by
      have ha : raw20828step2 = (fun i j => raw20828step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20828step2 raw20828step1; decide +kernel
      have hl : raw20828step2Labels = raw20828step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20828step1 raw20828step1Labels permutation8 permutation6
    _ = mixedMoment B node1242 node1242Labels := by rfl

def raw20829 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20829Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20829step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20829step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20829step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20829step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20829step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20829 raw20829Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw20829 raw20829Labels = mixedMoment B raw20829step0 raw20829step0Labels := by
      have hz : ∀ j, raw20829 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20829step0 = (fun i j => raw20829 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20829step0 raw20829; decide +kernel
      have hl : raw20829step0Labels = raw20829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20829 raw20829Labels permutation434 hz
    mixedMoment B raw20829step0 raw20829step0Labels = mixedMoment B raw20829step1 raw20829step1Labels := by
      have hz : ∀ j, raw20829step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20829step1 = (fun i j => raw20829step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20829step1 raw20829step0; decide +kernel
      have hl : raw20829step1Labels = raw20829step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20829step0 raw20829step0Labels permutation56 hz
    mixedMoment B raw20829step1 raw20829step1Labels = mixedMoment B raw20829step2 raw20829step2Labels := by
      have ha : raw20829step2 = (fun i j => raw20829step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20829step2 raw20829step1; decide +kernel
      have hl : raw20829step2Labels = raw20829step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20829step1 raw20829step1Labels permutation8 permutation6
    _ = mixedMoment B node1242 node1242Labels := by rfl

def raw20830 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20830Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20830step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20830step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20830step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20830step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-2, -1, 3]]
def raw20830step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20830step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw20830step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20830 raw20830Labels = mixedMoment B node1307 node1307Labels := by
  calc
    mixedMoment B raw20830 raw20830Labels = mixedMoment B raw20830step0 raw20830step0Labels := by
      have hz : ∀ j, raw20830 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20830step0 = (fun i j => raw20830 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20830step0 raw20830; decide +kernel
      have hl : raw20830step0Labels = raw20830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20830 raw20830Labels permutation434 hz
    mixedMoment B raw20830step0 raw20830step0Labels = mixedMoment B raw20830step1 raw20830step1Labels := by
      have hz : ∀ j, raw20830step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20830step1 = (fun i j => raw20830step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20830step1 raw20830step0; decide +kernel
      have hl : raw20830step1Labels = raw20830step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20830step0 raw20830step0Labels permutation80 hz
    mixedMoment B raw20830step1 raw20830step1Labels = mixedMoment B raw20830step2 raw20830step2Labels := by
      have hz : ∀ j, raw20830step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20830step2 = (fun i j => raw20830step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20830step2 raw20830step1; decide +kernel
      have hl : raw20830step2Labels = raw20830step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20830step1 raw20830step1Labels permutation14 hz
    mixedMoment B raw20830step2 raw20830step2Labels = mixedMoment B raw20830step3 raw20830step3Labels := by
      have ha : raw20830step3 = (fun i j => raw20830step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20830step3 raw20830step2; decide +kernel
      have hl : raw20830step3Labels = raw20830step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20830step2 raw20830step2Labels permutation2 permutation6
    _ = mixedMoment B node1307 node1307Labels := by rfl

def raw20831 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20831Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20831step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20831step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20831step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20831step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw20831step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20831 raw20831Labels = mixedMoment B node1009 node1009Labels := by
  calc
    mixedMoment B raw20831 raw20831Labels = mixedMoment B raw20831step0 raw20831step0Labels := by
      have hz : ∀ j, raw20831 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20831step0 = (fun i j => raw20831 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20831step0 raw20831; decide +kernel
      have hl : raw20831step0Labels = raw20831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20831 raw20831Labels permutation346 hz
    mixedMoment B raw20831step0 raw20831step0Labels = mixedMoment B raw20831step1 raw20831step1Labels := by
      have hz : ∀ j, raw20831step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20831step1 = (fun i j => raw20831step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20831step1 raw20831step0; decide +kernel
      have hl : raw20831step1Labels = raw20831step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20831step0 raw20831step0Labels permutation56 hz
    mixedMoment B raw20831step1 raw20831step1Labels = mixedMoment B raw20831step2 raw20831step2Labels := by
      have ha : raw20831step2 = (fun i j => raw20831step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20831step2 raw20831step1; decide +kernel
      have hl : raw20831step2Labels = raw20831step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20831step1 raw20831step1Labels permutation8 permutation6
    _ = mixedMoment B node1009 node1009Labels := by rfl

def raw20832 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20832Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20832step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw20832step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20832 raw20832Labels = mixedMoment B node1203 node1203Labels := by
  calc
    mixedMoment B raw20832 raw20832Labels = mixedMoment B raw20832step0 raw20832step0Labels := by
      have hz : ∀ j, raw20832 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20832step0 = (fun i j => raw20832 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20832step0 raw20832; decide +kernel
      have hl : raw20832step0Labels = raw20832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20832 raw20832Labels permutation346 hz
    mixedMoment B raw20832step0 raw20832step0Labels = mixedMoment B raw20832step1 raw20832step1Labels := by
      have ha : raw20832step1 = (fun i j => raw20832step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20832step1 raw20832step0; decide +kernel
      have hl : raw20832step1Labels = raw20832step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20832step0 raw20832step0Labels permutation32 permutation6
    _ = mixedMoment B node1203 node1203Labels := by rfl

def raw20833 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20833Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20833step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw20833step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20833 raw20833Labels = mixedMoment B node1203 node1203Labels := by
  calc
    mixedMoment B raw20833 raw20833Labels = mixedMoment B raw20833step0 raw20833step0Labels := by
      have hz : ∀ j, raw20833 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20833step0 = (fun i j => raw20833 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20833step0 raw20833; decide +kernel
      have hl : raw20833step0Labels = raw20833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20833 raw20833Labels permutation265 hz
    mixedMoment B raw20833step0 raw20833step0Labels = mixedMoment B raw20833step1 raw20833step1Labels := by
      have ha : raw20833step1 = (fun i j => raw20833step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20833step1 raw20833step0; decide +kernel
      have hl : raw20833step1Labels = raw20833step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20833step0 raw20833step0Labels permutation32 permutation6
    _ = mixedMoment B node1203 node1203Labels := by rfl

def raw20834 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20834Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20834step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20834step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20834step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw20834step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20834 raw20834Labels = mixedMoment B node1191 node1191Labels := by
  calc
    mixedMoment B raw20834 raw20834Labels = mixedMoment B raw20834step0 raw20834step0Labels := by
      have hz : ∀ j, raw20834 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20834step0 = (fun i j => raw20834 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20834step0 raw20834; decide +kernel
      have hl : raw20834step0Labels = raw20834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20834 raw20834Labels permutation346 hz
    mixedMoment B raw20834step0 raw20834step0Labels = mixedMoment B raw20834step1 raw20834step1Labels := by
      have hz : ∀ j, raw20834step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20834step1 = (fun i j => raw20834step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20834step1 raw20834step0; decide +kernel
      have hl : raw20834step1Labels = raw20834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20834step0 raw20834step0Labels permutation56 hz
    mixedMoment B raw20834step1 raw20834step1Labels = mixedMoment B raw20834step2 raw20834step2Labels := by
      have ha : raw20834step2 = (fun i j => raw20834step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20834step2 raw20834step1; decide +kernel
      have hl : raw20834step2Labels = raw20834step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20834step1 raw20834step1Labels permutation8 permutation6
    _ = mixedMoment B node1191 node1191Labels := by rfl

def raw20835 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20835Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20835step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20835step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20835step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20835step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20835 raw20835Labels = mixedMoment B node1243 node1243Labels := by
  calc
    mixedMoment B raw20835 raw20835Labels = mixedMoment B raw20835step0 raw20835step0Labels := by
      have hz : ∀ j, raw20835 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20835step0 = (fun i j => raw20835 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20835step0 raw20835; decide +kernel
      have hl : raw20835step0Labels = raw20835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20835 raw20835Labels permutation346 hz
    mixedMoment B raw20835step0 raw20835step0Labels = mixedMoment B raw20835step1 raw20835step1Labels := by
      have hz : ∀ j, raw20835step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20835step1 = (fun i j => raw20835step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20835step1 raw20835step0; decide +kernel
      have hl : raw20835step1Labels = raw20835step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20835step0 raw20835step0Labels permutation56 hz
    mixedMoment B raw20835step1 raw20835step1Labels = mixedMoment B raw20835step2 raw20835step2Labels := by
      have ha : raw20835step2 = (fun i j => raw20835step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20835step2 raw20835step1; decide +kernel
      have hl : raw20835step2Labels = raw20835step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20835step1 raw20835step1Labels permutation8 permutation6
    _ = mixedMoment B node1243 node1243Labels := by rfl

def raw20836 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20836Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20836step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20836step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20836step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20836step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20836step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20836 raw20836Labels = mixedMoment B node1007 node1007Labels := by
  calc
    mixedMoment B raw20836 raw20836Labels = mixedMoment B raw20836step0 raw20836step0Labels := by
      have hz : ∀ j, raw20836 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20836step0 = (fun i j => raw20836 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20836step0 raw20836; decide +kernel
      have hl : raw20836step0Labels = raw20836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20836 raw20836Labels permutation346 hz
    mixedMoment B raw20836step0 raw20836step0Labels = mixedMoment B raw20836step1 raw20836step1Labels := by
      have hz : ∀ j, raw20836step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20836step1 = (fun i j => raw20836step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20836step1 raw20836step0; decide +kernel
      have hl : raw20836step1Labels = raw20836step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20836step0 raw20836step0Labels permutation56 hz
    mixedMoment B raw20836step1 raw20836step1Labels = mixedMoment B raw20836step2 raw20836step2Labels := by
      have ha : raw20836step2 = (fun i j => raw20836step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20836step2 raw20836step1; decide +kernel
      have hl : raw20836step2Labels = raw20836step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20836step1 raw20836step1Labels permutation8 permutation6
    _ = mixedMoment B node1007 node1007Labels := by rfl

def raw20837 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20837Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20837step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20837step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20837 raw20837Labels = mixedMoment B node1202 node1202Labels := by
  calc
    mixedMoment B raw20837 raw20837Labels = mixedMoment B raw20837step0 raw20837step0Labels := by
      have hz : ∀ j, raw20837 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20837step0 = (fun i j => raw20837 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20837step0 raw20837; decide +kernel
      have hl : raw20837step0Labels = raw20837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20837 raw20837Labels permutation346 hz
    mixedMoment B raw20837step0 raw20837step0Labels = mixedMoment B raw20837step1 raw20837step1Labels := by
      have ha : raw20837step1 = (fun i j => raw20837step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20837step1 raw20837step0; decide +kernel
      have hl : raw20837step1Labels = raw20837step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20837step0 raw20837step0Labels permutation32 permutation6
    _ = mixedMoment B node1202 node1202Labels := by rfl

def raw20838 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20838Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20838step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20838step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20838step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20838 raw20838Labels = mixedMoment B node1202 node1202Labels := by
  calc
    mixedMoment B raw20838 raw20838Labels = mixedMoment B raw20838step0 raw20838step0Labels := by
      have hz : ∀ j, raw20838 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20838step0 = (fun i j => raw20838 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20838step0 raw20838; decide +kernel
      have hl : raw20838step0Labels = raw20838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20838 raw20838Labels permutation265 hz
    mixedMoment B raw20838step0 raw20838step0Labels = mixedMoment B raw20838step1 raw20838step1Labels := by
      have ha : raw20838step1 = (fun i j => raw20838step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20838step1 raw20838step0; decide +kernel
      have hl : raw20838step1Labels = raw20838step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20838step0 raw20838step0Labels permutation32 permutation6
    _ = mixedMoment B node1202 node1202Labels := by rfl

def raw20839 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20839Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20839step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20839step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20839step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20839step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw20839step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20839 raw20839Labels = mixedMoment B node1190 node1190Labels := by
  calc
    mixedMoment B raw20839 raw20839Labels = mixedMoment B raw20839step0 raw20839step0Labels := by
      have hz : ∀ j, raw20839 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20839step0 = (fun i j => raw20839 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20839step0 raw20839; decide +kernel
      have hl : raw20839step0Labels = raw20839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20839 raw20839Labels permutation346 hz
    mixedMoment B raw20839step0 raw20839step0Labels = mixedMoment B raw20839step1 raw20839step1Labels := by
      have hz : ∀ j, raw20839step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20839step1 = (fun i j => raw20839step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20839step1 raw20839step0; decide +kernel
      have hl : raw20839step1Labels = raw20839step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20839step0 raw20839step0Labels permutation56 hz
    mixedMoment B raw20839step1 raw20839step1Labels = mixedMoment B raw20839step2 raw20839step2Labels := by
      have ha : raw20839step2 = (fun i j => raw20839step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20839step2 raw20839step1; decide +kernel
      have hl : raw20839step2Labels = raw20839step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20839step1 raw20839step1Labels permutation8 permutation6
    _ = mixedMoment B node1190 node1190Labels := by rfl

def raw20840 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20840Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20840step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20840step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20840step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20840 raw20840Labels = mixedMoment B node1617 node1617Labels := by
  calc
    mixedMoment B raw20840 raw20840Labels = mixedMoment B raw20840step0 raw20840step0Labels := by
      have hz : ∀ j, raw20840 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20840step0 = (fun i j => raw20840 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20840step0 raw20840; decide +kernel
      have hl : raw20840step0Labels = raw20840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20840 raw20840Labels permutation346 hz
    mixedMoment B raw20840step0 raw20840step0Labels = mixedMoment B raw20840step1 raw20840step1Labels := by
      have ha : raw20840step1 = (fun i j => raw20840step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20840step1 raw20840step0; decide +kernel
      have hl : raw20840step1Labels = raw20840step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20840step0 raw20840step0Labels permutation38 permutation4
    mixedMoment B raw20840step1 raw20840step1Labels = mixedMoment B raw20840step2 raw20840step2Labels := by
      have ha : raw20840step2 = -raw20840step1 := by apply Matrix.ext; change ∀ i j, raw20840step2 i j = -(raw20840step1 i j); unfold raw20840step2 raw20840step1; decide +kernel
      have hl : raw20840step2Labels = raw20840step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1617 node1617Labels := by rfl

def raw20841 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20841Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20841step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20841step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20841step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20841step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20841 raw20841Labels = mixedMoment B node1617 node1617Labels := by
  calc
    mixedMoment B raw20841 raw20841Labels = mixedMoment B raw20841step0 raw20841step0Labels := by
      have hz : ∀ j, raw20841 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20841step0 = (fun i j => raw20841 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20841step0 raw20841; decide +kernel
      have hl : raw20841step0Labels = raw20841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20841 raw20841Labels permutation265 hz
    mixedMoment B raw20841step0 raw20841step0Labels = mixedMoment B raw20841step1 raw20841step1Labels := by
      have ha : raw20841step1 = (fun i j => raw20841step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20841step1 raw20841step0; decide +kernel
      have hl : raw20841step1Labels = raw20841step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20841step0 raw20841step0Labels permutation38 permutation4
    mixedMoment B raw20841step1 raw20841step1Labels = mixedMoment B raw20841step2 raw20841step2Labels := by
      have ha : raw20841step2 = -raw20841step1 := by apply Matrix.ext; change ∀ i j, raw20841step2 i j = -(raw20841step1 i j); unfold raw20841step2 raw20841step1; decide +kernel
      have hl : raw20841step2Labels = raw20841step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1617 node1617Labels := by rfl

def raw20842 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20842Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20842step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20842step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20842step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20842step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw20842step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20842step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw20842step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20842 raw20842Labels = mixedMoment B node1630 node1630Labels := by
  calc
    mixedMoment B raw20842 raw20842Labels = mixedMoment B raw20842step0 raw20842step0Labels := by
      have hz : ∀ j, raw20842 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20842step0 = (fun i j => raw20842 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20842step0 raw20842; decide +kernel
      have hl : raw20842step0Labels = raw20842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20842 raw20842Labels permutation346 hz
    mixedMoment B raw20842step0 raw20842step0Labels = mixedMoment B raw20842step1 raw20842step1Labels := by
      have hz : ∀ j, raw20842step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20842step1 = (fun i j => raw20842step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20842step1 raw20842step0; decide +kernel
      have hl : raw20842step1Labels = raw20842step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20842step0 raw20842step0Labels permutation56 hz
    mixedMoment B raw20842step1 raw20842step1Labels = mixedMoment B raw20842step2 raw20842step2Labels := by
      have ha : raw20842step2 = (fun i j => raw20842step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20842step2 raw20842step1; decide +kernel
      have hl : raw20842step2Labels = raw20842step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20842step1 raw20842step1Labels permutation8 permutation4
    mixedMoment B raw20842step2 raw20842step2Labels = mixedMoment B raw20842step3 raw20842step3Labels := by
      have ha : raw20842step3 = -raw20842step2 := by apply Matrix.ext; change ∀ i j, raw20842step3 i j = -(raw20842step2 i j); unfold raw20842step3 raw20842step2; decide +kernel
      have hl : raw20842step3Labels = raw20842step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1630 node1630Labels := by rfl

def raw20843 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20843Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20843step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw20843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20843step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw20843step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20843step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw20843step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20843 raw20843Labels = mixedMoment B node1625 node1625Labels := by
  calc
    mixedMoment B raw20843 raw20843Labels = mixedMoment B raw20843step0 raw20843step0Labels := by
      have hz : ∀ j, raw20843 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20843step0 = (fun i j => raw20843 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20843step0 raw20843; decide +kernel
      have hl : raw20843step0Labels = raw20843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20843 raw20843Labels permutation346 hz
    mixedMoment B raw20843step0 raw20843step0Labels = mixedMoment B raw20843step1 raw20843step1Labels := by
      have hz : ∀ j, raw20843step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20843step1 = (fun i j => raw20843step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20843step1 raw20843step0; decide +kernel
      have hl : raw20843step1Labels = raw20843step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20843step0 raw20843step0Labels permutation56 hz
    mixedMoment B raw20843step1 raw20843step1Labels = mixedMoment B raw20843step2 raw20843step2Labels := by
      have ha : raw20843step2 = (fun i j => raw20843step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20843step2 raw20843step1; decide +kernel
      have hl : raw20843step2Labels = raw20843step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20843step1 raw20843step1Labels permutation8 permutation4
    mixedMoment B raw20843step2 raw20843step2Labels = mixedMoment B raw20843step3 raw20843step3Labels := by
      have ha : raw20843step3 = -raw20843step2 := by apply Matrix.ext; change ∀ i j, raw20843step3 i j = -(raw20843step2 i j); unfold raw20843step3 raw20843step2; decide +kernel
      have hl : raw20843step3Labels = raw20843step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1625 node1625Labels := by rfl

def raw20844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20844Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20844step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20844step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20844step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20844 raw20844Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw20844 raw20844Labels = mixedMoment B raw20844step0 raw20844step0Labels := by
      have hz : ∀ j, raw20844 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20844step0 = (fun i j => raw20844 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20844step0 raw20844; decide +kernel
      have hl : raw20844step0Labels = raw20844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20844 raw20844Labels permutation346 hz
    mixedMoment B raw20844step0 raw20844step0Labels = mixedMoment B raw20844step1 raw20844step1Labels := by
      have hz : ∀ j, raw20844step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20844step1 = (fun i j => raw20844step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20844step1 raw20844step0; decide +kernel
      have hl : raw20844step1Labels = raw20844step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20844step0 raw20844step0Labels permutation56 hz
    _ = mixedMoment B node5272 node5272Labels := by rfl

def raw20845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20845step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20845step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20845step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20845step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20845 raw20845Labels = mixedMoment B node4157 node4157Labels := by
  calc
    mixedMoment B raw20845 raw20845Labels = mixedMoment B raw20845step0 raw20845step0Labels := by
      have hz : ∀ j, raw20845 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20845step0 = (fun i j => raw20845 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20845step0 raw20845; decide +kernel
      have hl : raw20845step0Labels = raw20845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20845 raw20845Labels permutation346 hz
    mixedMoment B raw20845step0 raw20845step0Labels = mixedMoment B raw20845step1 raw20845step1Labels := by
      have ha : raw20845step1 = (fun i j => raw20845step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20845step1 raw20845step0; decide +kernel
      have hl : raw20845step1Labels = raw20845step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20845step0 raw20845step0Labels permutation38 permutation3
    mixedMoment B raw20845step1 raw20845step1Labels = mixedMoment B raw20845step2 raw20845step2Labels := by
      have ha : raw20845step2 = raw20845step1 := by apply Matrix.ext; unfold raw20845step2 raw20845step1; decide +kernel
      have hl : raw20845step1Labels = labelEmbedding6 ∘ raw20845step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20845step1 raw20845step1Labels raw20845step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4157 node4157Labels := by rfl

def raw20846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20846step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20846step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20846step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20846 raw20846Labels = mixedMoment B node4532 node4532Labels := by
  calc
    mixedMoment B raw20846 raw20846Labels = mixedMoment B raw20846step0 raw20846step0Labels := by
      have ha : raw20846step0 = (fun i j => raw20846 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20846step0 raw20846; decide +kernel
      have hl : raw20846step0Labels = raw20846Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20846 raw20846Labels permutation182 permutation3
    mixedMoment B raw20846step0 raw20846step0Labels = mixedMoment B raw20846step1 raw20846step1Labels := by
      have ha : raw20846step1 = raw20846step0 := by apply Matrix.ext; unfold raw20846step1 raw20846step0; decide +kernel
      have hl : raw20846step0Labels = labelEmbedding6 ∘ raw20846step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20846step0 raw20846step0Labels raw20846step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4532 node4532Labels := by rfl

def raw20847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20847step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20847step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20847 raw20847Labels = mixedMoment B node4543 node4543Labels := by
  calc
    mixedMoment B raw20847 raw20847Labels = mixedMoment B raw20847step0 raw20847step0Labels := by
      have hz : ∀ j, raw20847 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20847step0 = (fun i j => raw20847 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20847step0 raw20847; decide +kernel
      have hl : raw20847step0Labels = raw20847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20847 raw20847Labels permutation346 hz
    mixedMoment B raw20847step0 raw20847step0Labels = mixedMoment B raw20847step1 raw20847step1Labels := by
      have ha : raw20847step1 = (fun i j => raw20847step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20847step1 raw20847step0; decide +kernel
      have hl : raw20847step1Labels = raw20847step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20847step0 raw20847step0Labels permutation38 permutation2
    _ = mixedMoment B node4543 node4543Labels := by rfl

def raw20848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20848step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20848step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20848step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20848step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20848 raw20848Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw20848 raw20848Labels = mixedMoment B raw20848step0 raw20848step0Labels := by
      have hz : ∀ j, raw20848 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20848step0 = (fun i j => raw20848 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20848step0 raw20848; decide +kernel
      have hl : raw20848step0Labels = raw20848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20848 raw20848Labels permutation520 hz
    mixedMoment B raw20848step0 raw20848step0Labels = mixedMoment B raw20848step1 raw20848step1Labels := by
      have hz : ∀ j, raw20848step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20848step1 = (fun i j => raw20848step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20848step1 raw20848step0; decide +kernel
      have hl : raw20848step1Labels = raw20848step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20848step0 raw20848step0Labels permutation80 hz
    mixedMoment B raw20848step1 raw20848step1Labels = mixedMoment B raw20848step2 raw20848step2Labels := by
      have ha : raw20848step2 = (fun i j => raw20848step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20848step2 raw20848step1; decide +kernel
      have hl : raw20848step2Labels = raw20848step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20848step1 raw20848step1Labels permutation10 permutation2
    _ = mixedMoment B node4605 node4605Labels := by rfl

def raw20849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20849step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20849step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20849step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20849step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20849 raw20849Labels = mixedMoment B node4157 node4157Labels := by
  calc
    mixedMoment B raw20849 raw20849Labels = mixedMoment B raw20849step0 raw20849step0Labels := by
      have hz : ∀ j, raw20849 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20849step0 = (fun i j => raw20849 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20849step0 raw20849; decide +kernel
      have hl : raw20849step0Labels = raw20849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20849 raw20849Labels permutation265 hz
    mixedMoment B raw20849step0 raw20849step0Labels = mixedMoment B raw20849step1 raw20849step1Labels := by
      have ha : raw20849step1 = (fun i j => raw20849step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20849step1 raw20849step0; decide +kernel
      have hl : raw20849step1Labels = raw20849step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20849step0 raw20849step0Labels permutation38 permutation3
    mixedMoment B raw20849step1 raw20849step1Labels = mixedMoment B raw20849step2 raw20849step2Labels := by
      have ha : raw20849step2 = raw20849step1 := by apply Matrix.ext; unfold raw20849step2 raw20849step1; decide +kernel
      have hl : raw20849step1Labels = labelEmbedding6 ∘ raw20849step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20849step1 raw20849step1Labels raw20849step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4157 node4157Labels := by rfl

def raw20850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20850step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20850step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20850step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20850 raw20850Labels = mixedMoment B node4532 node4532Labels := by
  calc
    mixedMoment B raw20850 raw20850Labels = mixedMoment B raw20850step0 raw20850step0Labels := by
      have ha : raw20850step0 = (fun i j => raw20850 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20850step0 raw20850; decide +kernel
      have hl : raw20850step0Labels = raw20850Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20850 raw20850Labels permutation158 permutation3
    mixedMoment B raw20850step0 raw20850step0Labels = mixedMoment B raw20850step1 raw20850step1Labels := by
      have ha : raw20850step1 = raw20850step0 := by apply Matrix.ext; unfold raw20850step1 raw20850step0; decide +kernel
      have hl : raw20850step0Labels = labelEmbedding6 ∘ raw20850step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20850step0 raw20850step0Labels raw20850step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4532 node4532Labels := by rfl

def raw20851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20851step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw20851step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20851 raw20851Labels = mixedMoment B node4543 node4543Labels := by
  calc
    mixedMoment B raw20851 raw20851Labels = mixedMoment B raw20851step0 raw20851step0Labels := by
      have hz : ∀ j, raw20851 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20851step0 = (fun i j => raw20851 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20851step0 raw20851; decide +kernel
      have hl : raw20851step0Labels = raw20851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20851 raw20851Labels permutation265 hz
    mixedMoment B raw20851step0 raw20851step0Labels = mixedMoment B raw20851step1 raw20851step1Labels := by
      have ha : raw20851step1 = (fun i j => raw20851step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20851step1 raw20851step0; decide +kernel
      have hl : raw20851step1Labels = raw20851step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20851step0 raw20851step0Labels permutation38 permutation2
    _ = mixedMoment B node4543 node4543Labels := by rfl

def raw20852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20852step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20852step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw20852step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20852step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20852step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20852 raw20852Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw20852 raw20852Labels = mixedMoment B raw20852step0 raw20852step0Labels := by
      have hz : ∀ j, raw20852 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20852step0 = (fun i j => raw20852 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20852step0 raw20852; decide +kernel
      have hl : raw20852step0Labels = raw20852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20852 raw20852Labels permutation520 hz
    mixedMoment B raw20852step0 raw20852step0Labels = mixedMoment B raw20852step1 raw20852step1Labels := by
      have hz : ∀ j, raw20852step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20852step1 = (fun i j => raw20852step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20852step1 raw20852step0; decide +kernel
      have hl : raw20852step1Labels = raw20852step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20852step0 raw20852step0Labels permutation56 hz
    mixedMoment B raw20852step1 raw20852step1Labels = mixedMoment B raw20852step2 raw20852step2Labels := by
      have ha : raw20852step2 = (fun i j => raw20852step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20852step2 raw20852step1; decide +kernel
      have hl : raw20852step2Labels = raw20852step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20852step1 raw20852step1Labels permutation10 permutation2
    _ = mixedMoment B node4605 node4605Labels := by rfl

def raw20853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20853step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20853step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20853step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20853step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20853step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20853step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20853step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20853 raw20853Labels = mixedMoment B node4184 node4184Labels := by
  calc
    mixedMoment B raw20853 raw20853Labels = mixedMoment B raw20853step0 raw20853step0Labels := by
      have hz : ∀ j, raw20853 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20853step0 = (fun i j => raw20853 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20853step0 raw20853; decide +kernel
      have hl : raw20853step0Labels = raw20853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20853 raw20853Labels permutation346 hz
    mixedMoment B raw20853step0 raw20853step0Labels = mixedMoment B raw20853step1 raw20853step1Labels := by
      have hz : ∀ j, raw20853step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20853step1 = (fun i j => raw20853step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20853step1 raw20853step0; decide +kernel
      have hl : raw20853step1Labels = raw20853step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20853step0 raw20853step0Labels permutation56 hz
    mixedMoment B raw20853step1 raw20853step1Labels = mixedMoment B raw20853step2 raw20853step2Labels := by
      have ha : raw20853step2 = (fun i j => raw20853step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20853step2 raw20853step1; decide +kernel
      have hl : raw20853step2Labels = raw20853step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20853step1 raw20853step1Labels permutation10 permutation3
    mixedMoment B raw20853step2 raw20853step2Labels = mixedMoment B raw20853step3 raw20853step3Labels := by
      have ha : raw20853step3 = raw20853step2 := by apply Matrix.ext; unfold raw20853step3 raw20853step2; decide +kernel
      have hl : raw20853step2Labels = labelEmbedding6 ∘ raw20853step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20853step2 raw20853step2Labels raw20853step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4184 node4184Labels := by rfl

def raw20854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20854step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20854step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20854step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20854step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20854 raw20854Labels = mixedMoment B node4552 node4552Labels := by
  calc
    mixedMoment B raw20854 raw20854Labels = mixedMoment B raw20854step0 raw20854step0Labels := by
      have hz : ∀ j, raw20854 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20854step0 = (fun i j => raw20854 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20854step0 raw20854; decide +kernel
      have hl : raw20854step0Labels = raw20854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20854 raw20854Labels permutation346 hz
    mixedMoment B raw20854step0 raw20854step0Labels = mixedMoment B raw20854step1 raw20854step1Labels := by
      have ha : raw20854step1 = (fun i j => raw20854step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20854step1 raw20854step0; decide +kernel
      have hl : raw20854step1Labels = raw20854step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20854step0 raw20854step0Labels permutation34 permutation3
    mixedMoment B raw20854step1 raw20854step1Labels = mixedMoment B raw20854step2 raw20854step2Labels := by
      have ha : raw20854step2 = raw20854step1 := by apply Matrix.ext; unfold raw20854step2 raw20854step1; decide +kernel
      have hl : raw20854step1Labels = labelEmbedding6 ∘ raw20854step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20854step1 raw20854step1Labels raw20854step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4552 node4552Labels := by rfl

def raw20855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20855step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20855step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20855step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw20855step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20855 raw20855Labels = mixedMoment B node4552 node4552Labels := by
  calc
    mixedMoment B raw20855 raw20855Labels = mixedMoment B raw20855step0 raw20855step0Labels := by
      have hz : ∀ j, raw20855 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20855step0 = (fun i j => raw20855 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20855step0 raw20855; decide +kernel
      have hl : raw20855step0Labels = raw20855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20855 raw20855Labels permutation265 hz
    mixedMoment B raw20855step0 raw20855step0Labels = mixedMoment B raw20855step1 raw20855step1Labels := by
      have ha : raw20855step1 = (fun i j => raw20855step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20855step1 raw20855step0; decide +kernel
      have hl : raw20855step1Labels = raw20855step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20855step0 raw20855step0Labels permutation34 permutation3
    mixedMoment B raw20855step1 raw20855step1Labels = mixedMoment B raw20855step2 raw20855step2Labels := by
      have ha : raw20855step2 = raw20855step1 := by apply Matrix.ext; unfold raw20855step2 raw20855step1; decide +kernel
      have hl : raw20855step1Labels = labelEmbedding6 ∘ raw20855step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20855step1 raw20855step1Labels raw20855step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4552 node4552Labels := by rfl

def raw20856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20856step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![3, 0, -3]]
def raw20856step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20856step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw20856step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20856 raw20856Labels = mixedMoment B node4621 node4621Labels := by
  calc
    mixedMoment B raw20856 raw20856Labels = mixedMoment B raw20856step0 raw20856step0Labels := by
      have hz : ∀ j, raw20856 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20856step0 = (fun i j => raw20856 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20856step0 raw20856; decide +kernel
      have hl : raw20856step0Labels = raw20856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20856 raw20856Labels permutation520 hz
    mixedMoment B raw20856step0 raw20856step0Labels = mixedMoment B raw20856step1 raw20856step1Labels := by
      have hz : ∀ j, raw20856step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20856step1 = (fun i j => raw20856step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20856step1 raw20856step0; decide +kernel
      have hl : raw20856step1Labels = raw20856step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20856step0 raw20856step0Labels permutation80 hz
    mixedMoment B raw20856step1 raw20856step1Labels = mixedMoment B raw20856step2 raw20856step2Labels := by
      have hz : ∀ j, raw20856step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20856step2 = (fun i j => raw20856step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20856step2 raw20856step1; decide +kernel
      have hl : raw20856step2Labels = raw20856step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20856step1 raw20856step1Labels permutation14 hz
    _ = mixedMoment B node4621 node4621Labels := by rfl

def raw20857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20857step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20857step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20857step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20857step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20857step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20857step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20857step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20857 raw20857Labels = mixedMoment B node4162 node4162Labels := by
  calc
    mixedMoment B raw20857 raw20857Labels = mixedMoment B raw20857step0 raw20857step0Labels := by
      have hz : ∀ j, raw20857 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20857step0 = (fun i j => raw20857 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20857step0 raw20857; decide +kernel
      have hl : raw20857step0Labels = raw20857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20857 raw20857Labels permutation346 hz
    mixedMoment B raw20857step0 raw20857step0Labels = mixedMoment B raw20857step1 raw20857step1Labels := by
      have hz : ∀ j, raw20857step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20857step1 = (fun i j => raw20857step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20857step1 raw20857step0; decide +kernel
      have hl : raw20857step1Labels = raw20857step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20857step0 raw20857step0Labels permutation56 hz
    mixedMoment B raw20857step1 raw20857step1Labels = mixedMoment B raw20857step2 raw20857step2Labels := by
      have ha : raw20857step2 = (fun i j => raw20857step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20857step2 raw20857step1; decide +kernel
      have hl : raw20857step2Labels = raw20857step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20857step1 raw20857step1Labels permutation8 permutation3
    mixedMoment B raw20857step2 raw20857step2Labels = mixedMoment B raw20857step3 raw20857step3Labels := by
      have ha : raw20857step3 = raw20857step2 := by apply Matrix.ext; unfold raw20857step3 raw20857step2; decide +kernel
      have hl : raw20857step2Labels = labelEmbedding6 ∘ raw20857step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20857step2 raw20857step2Labels raw20857step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4162 node4162Labels := by rfl

def raw20858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20858step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20858step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20858step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20858step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20858 raw20858Labels = mixedMoment B node4536 node4536Labels := by
  calc
    mixedMoment B raw20858 raw20858Labels = mixedMoment B raw20858step0 raw20858step0Labels := by
      have hz : ∀ j, raw20858 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20858step0 = (fun i j => raw20858 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20858step0 raw20858; decide +kernel
      have hl : raw20858step0Labels = raw20858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20858 raw20858Labels permutation346 hz
    mixedMoment B raw20858step0 raw20858step0Labels = mixedMoment B raw20858step1 raw20858step1Labels := by
      have ha : raw20858step1 = (fun i j => raw20858step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20858step1 raw20858step0; decide +kernel
      have hl : raw20858step1Labels = raw20858step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20858step0 raw20858step0Labels permutation32 permutation3
    mixedMoment B raw20858step1 raw20858step1Labels = mixedMoment B raw20858step2 raw20858step2Labels := by
      have ha : raw20858step2 = raw20858step1 := by apply Matrix.ext; unfold raw20858step2 raw20858step1; decide +kernel
      have hl : raw20858step1Labels = labelEmbedding6 ∘ raw20858step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20858step1 raw20858step1Labels raw20858step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4536 node4536Labels := by rfl

def raw20859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20859step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20859step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20859step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw20859step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20859 raw20859Labels = mixedMoment B node4536 node4536Labels := by
  calc
    mixedMoment B raw20859 raw20859Labels = mixedMoment B raw20859step0 raw20859step0Labels := by
      have hz : ∀ j, raw20859 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20859step0 = (fun i j => raw20859 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20859step0 raw20859; decide +kernel
      have hl : raw20859step0Labels = raw20859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20859 raw20859Labels permutation265 hz
    mixedMoment B raw20859step0 raw20859step0Labels = mixedMoment B raw20859step1 raw20859step1Labels := by
      have ha : raw20859step1 = (fun i j => raw20859step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20859step1 raw20859step0; decide +kernel
      have hl : raw20859step1Labels = raw20859step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20859step0 raw20859step0Labels permutation32 permutation3
    mixedMoment B raw20859step1 raw20859step1Labels = mixedMoment B raw20859step2 raw20859step2Labels := by
      have ha : raw20859step2 = raw20859step1 := by apply Matrix.ext; unfold raw20859step2 raw20859step1; decide +kernel
      have hl : raw20859step1Labels = labelEmbedding6 ∘ raw20859step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20859step1 raw20859step1Labels raw20859step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4536 node4536Labels := by rfl

def raw20860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20860step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20860step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw20860step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20860 raw20860Labels = mixedMoment B node4557 node4557Labels := by
  calc
    mixedMoment B raw20860 raw20860Labels = mixedMoment B raw20860step0 raw20860step0Labels := by
      have hz : ∀ j, raw20860 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20860step0 = (fun i j => raw20860 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20860step0 raw20860; decide +kernel
      have hl : raw20860step0Labels = raw20860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20860 raw20860Labels permutation346 hz
    mixedMoment B raw20860step0 raw20860step0Labels = mixedMoment B raw20860step1 raw20860step1Labels := by
      have hz : ∀ j, raw20860step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20860step1 = (fun i j => raw20860step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20860step1 raw20860step0; decide +kernel
      have hl : raw20860step1Labels = raw20860step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20860step0 raw20860step0Labels permutation56 hz
    _ = mixedMoment B node4557 node4557Labels := by rfl

def raw20861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20861step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20861step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20861step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw20861step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20861step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw20861step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20861 raw20861Labels = mixedMoment B node4159 node4159Labels := by
  calc
    mixedMoment B raw20861 raw20861Labels = mixedMoment B raw20861step0 raw20861step0Labels := by
      have hz : ∀ j, raw20861 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20861step0 = (fun i j => raw20861 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20861step0 raw20861; decide +kernel
      have hl : raw20861step0Labels = raw20861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20861 raw20861Labels permutation346 hz
    mixedMoment B raw20861step0 raw20861step0Labels = mixedMoment B raw20861step1 raw20861step1Labels := by
      have hz : ∀ j, raw20861step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20861step1 = (fun i j => raw20861step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20861step1 raw20861step0; decide +kernel
      have hl : raw20861step1Labels = raw20861step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20861step0 raw20861step0Labels permutation56 hz
    mixedMoment B raw20861step1 raw20861step1Labels = mixedMoment B raw20861step2 raw20861step2Labels := by
      have ha : raw20861step2 = (fun i j => raw20861step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20861step2 raw20861step1; decide +kernel
      have hl : raw20861step2Labels = raw20861step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20861step1 raw20861step1Labels permutation8 permutation3
    mixedMoment B raw20861step2 raw20861step2Labels = mixedMoment B raw20861step3 raw20861step3Labels := by
      have ha : raw20861step3 = raw20861step2 := by apply Matrix.ext; unfold raw20861step3 raw20861step2; decide +kernel
      have hl : raw20861step2Labels = labelEmbedding6 ∘ raw20861step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20861step2 raw20861step2Labels raw20861step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4159 node4159Labels := by rfl

def raw20862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20862step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw20862step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20862step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20862 raw20862Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw20862 raw20862Labels = mixedMoment B raw20862step0 raw20862step0Labels := by
      have hz : ∀ j, raw20862 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20862step0 = (fun i j => raw20862 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20862step0 raw20862; decide +kernel
      have hl : raw20862step0Labels = raw20862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20862 raw20862Labels permutation346 hz
    mixedMoment B raw20862step0 raw20862step0Labels = mixedMoment B raw20862step1 raw20862step1Labels := by
      have ha : raw20862step1 = (fun i j => raw20862step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20862step1 raw20862step0; decide +kernel
      have hl : raw20862step1Labels = raw20862step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20862step0 raw20862step0Labels permutation151 permutation2
    mixedMoment B raw20862step1 raw20862step1Labels = mixedMoment B raw20862step2 raw20862step2Labels := by
      have ha : raw20862step2 = -raw20862step1 := by apply Matrix.ext; change ∀ i j, raw20862step2 i j = -(raw20862step1 i j); unfold raw20862step2 raw20862step1; decide +kernel
      have hl : raw20862step2Labels = raw20862step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4330 node4330Labels := by rfl

def raw20863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 2, 2]]
def raw20863step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20863step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20863 raw20863Labels = mixedMoment B node4330 node4330Labels := by
  calc
    mixedMoment B raw20863 raw20863Labels = mixedMoment B raw20863step0 raw20863step0Labels := by
      have hz : ∀ j, raw20863 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20863step0 = (fun i j => raw20863 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20863step0 raw20863; decide +kernel
      have hl : raw20863step0Labels = raw20863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20863 raw20863Labels permutation265 hz
    mixedMoment B raw20863step0 raw20863step0Labels = mixedMoment B raw20863step1 raw20863step1Labels := by
      have ha : raw20863step1 = (fun i j => raw20863step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20863step1 raw20863step0; decide +kernel
      have hl : raw20863step1Labels = raw20863step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20863step0 raw20863step0Labels permutation151 permutation2
    mixedMoment B raw20863step1 raw20863step1Labels = mixedMoment B raw20863step2 raw20863step2Labels := by
      have ha : raw20863step2 = -raw20863step1 := by apply Matrix.ext; change ∀ i j, raw20863step2 i j = -(raw20863step1 i j); unfold raw20863step2 raw20863step1; decide +kernel
      have hl : raw20863step2Labels = raw20863step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4330 node4330Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
