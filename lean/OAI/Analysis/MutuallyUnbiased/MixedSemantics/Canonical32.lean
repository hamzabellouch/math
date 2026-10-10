import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw4096 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4096Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4096step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4096step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4096step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4096step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4096 raw4096Labels = mixedMoment B node3549 node3549Labels := by
  calc
    mixedMoment B raw4096 raw4096Labels = mixedMoment B raw4096step0 raw4096step0Labels := by
      have hz : ∀ j, raw4096 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4096step0 = (fun i j => raw4096 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4096step0 raw4096; decide +kernel
      have hl : raw4096step0Labels = raw4096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4096 raw4096Labels permutation346 hz
    mixedMoment B raw4096step0 raw4096step0Labels = mixedMoment B raw4096step1 raw4096step1Labels := by
      have hz : ∀ j, raw4096step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4096step1 = (fun i j => raw4096step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4096step1 raw4096step0; decide +kernel
      have hl : raw4096step1Labels = raw4096step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4096step0 raw4096step0Labels permutation56 hz
    mixedMoment B raw4096step1 raw4096step1Labels = mixedMoment B raw4096step2 raw4096step2Labels := by
      have ha : raw4096step2 = (fun i j => raw4096step1 (permutation28 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4096step2 raw4096step1; decide +kernel
      have hl : raw4096step2Labels = raw4096step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4096step1 raw4096step1Labels permutation28 permutation2
    _ = mixedMoment B node3549 node3549Labels := by rfl

def raw4097 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4097Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4097step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4097step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4097step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw4097step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4097step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -1, 0], ![1, 2, -3]]
def raw4097step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4097 raw4097Labels = mixedMoment B node3634 node3634Labels := by
  calc
    mixedMoment B raw4097 raw4097Labels = mixedMoment B raw4097step0 raw4097step0Labels := by
      have hz : ∀ j, raw4097 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4097step0 = (fun i j => raw4097 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4097step0 raw4097; decide +kernel
      have hl : raw4097step0Labels = raw4097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4097 raw4097Labels permutation434 hz
    mixedMoment B raw4097step0 raw4097step0Labels = mixedMoment B raw4097step1 raw4097step1Labels := by
      have hz : ∀ j, raw4097step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4097step1 = (fun i j => raw4097step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4097step1 raw4097step0; decide +kernel
      have hl : raw4097step1Labels = raw4097step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4097step0 raw4097step0Labels permutation80 hz
    mixedMoment B raw4097step1 raw4097step1Labels = mixedMoment B raw4097step2 raw4097step2Labels := by
      have hz : ∀ j, raw4097step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4097step2 = (fun i j => raw4097step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4097step2 raw4097step1; decide +kernel
      have hl : raw4097step2Labels = raw4097step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4097step1 raw4097step1Labels permutation14 hz
    mixedMoment B raw4097step2 raw4097step2Labels = mixedMoment B raw4097step3 raw4097step3Labels := by
      have ha : raw4097step3 = (fun i j => raw4097step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4097step3 raw4097step2; decide +kernel
      have hl : raw4097step3Labels = raw4097step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4097step2 raw4097step2Labels permutation7 permutation2
    _ = mixedMoment B node3634 node3634Labels := by rfl

def raw4098 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4098Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4098step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4098step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4098 raw4098Labels = mixedMoment B node3393 node3393Labels := by
  calc
    mixedMoment B raw4098 raw4098Labels = mixedMoment B raw4098step0 raw4098step0Labels := by
      have hz : ∀ j, raw4098 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4098step0 = (fun i j => raw4098 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4098step0 raw4098; decide +kernel
      have hl : raw4098step0Labels = raw4098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4098 raw4098Labels permutation434 hz
    mixedMoment B raw4098step0 raw4098step0Labels = mixedMoment B raw4098step1 raw4098step1Labels := by
      have ha : raw4098step1 = (fun i j => raw4098step0 (permutation136 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4098step1 raw4098step0; decide +kernel
      have hl : raw4098step1Labels = raw4098step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4098step0 raw4098step0Labels permutation136 permutation2
    _ = mixedMoment B node3393 node3393Labels := by rfl

def raw4099 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4099Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4099step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4099step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4099 raw4099Labels = mixedMoment B node3393 node3393Labels := by
  calc
    mixedMoment B raw4099 raw4099Labels = mixedMoment B raw4099step0 raw4099step0Labels := by
      have hz : ∀ j, raw4099 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4099step0 = (fun i j => raw4099 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4099step0 raw4099; decide +kernel
      have hl : raw4099step0Labels = raw4099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4099 raw4099Labels permutation346 hz
    mixedMoment B raw4099step0 raw4099step0Labels = mixedMoment B raw4099step1 raw4099step1Labels := by
      have ha : raw4099step1 = (fun i j => raw4099step0 (permutation136 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4099step1 raw4099step0; decide +kernel
      have hl : raw4099step1Labels = raw4099step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4099step0 raw4099step0Labels permutation136 permutation2
    _ = mixedMoment B node3393 node3393Labels := by rfl

def raw4100 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4100Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4100step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4100step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4100step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4100step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-2, 2, 0], ![-2, -1, 3]]
def raw4100step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4100step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -2, 0], ![2, 1, -3]]
def raw4100step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4100 raw4100Labels = mixedMoment B node3160 node3160Labels := by
  calc
    mixedMoment B raw4100 raw4100Labels = mixedMoment B raw4100step0 raw4100step0Labels := by
      have hz : ∀ j, raw4100 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4100step0 = (fun i j => raw4100 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4100step0 raw4100; decide +kernel
      have hl : raw4100step0Labels = raw4100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4100 raw4100Labels permutation434 hz
    mixedMoment B raw4100step0 raw4100step0Labels = mixedMoment B raw4100step1 raw4100step1Labels := by
      have hz : ∀ j, raw4100step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4100step1 = (fun i j => raw4100step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4100step1 raw4100step0; decide +kernel
      have hl : raw4100step1Labels = raw4100step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4100step0 raw4100step0Labels permutation80 hz
    mixedMoment B raw4100step1 raw4100step1Labels = mixedMoment B raw4100step2 raw4100step2Labels := by
      have ha : raw4100step2 = (fun i j => raw4100step1 (permutation20 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4100step2 raw4100step1; decide +kernel
      have hl : raw4100step2Labels = raw4100step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4100step1 raw4100step1Labels permutation20 permutation2
    mixedMoment B raw4100step2 raw4100step2Labels = mixedMoment B raw4100step3 raw4100step3Labels := by
      have ha : raw4100step3 = -raw4100step2 := by apply Matrix.ext; change ∀ i j, raw4100step3 i j = -(raw4100step2 i j); unfold raw4100step3 raw4100step2; decide +kernel
      have hl : raw4100step3Labels = raw4100step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3160 node3160Labels := by rfl

def raw4101 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4101Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4101step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4101step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4101step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4101 raw4101Labels = mixedMoment B node3396 node3396Labels := by
  calc
    mixedMoment B raw4101 raw4101Labels = mixedMoment B raw4101step0 raw4101step0Labels := by
      have hz : ∀ j, raw4101 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4101step0 = (fun i j => raw4101 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4101step0 raw4101; decide +kernel
      have hl : raw4101step0Labels = raw4101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4101 raw4101Labels permutation434 hz
    mixedMoment B raw4101step0 raw4101step0Labels = mixedMoment B raw4101step1 raw4101step1Labels := by
      have hz : ∀ j, raw4101step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4101step1 = (fun i j => raw4101step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4101step1 raw4101step0; decide +kernel
      have hl : raw4101step1Labels = raw4101step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4101step0 raw4101step0Labels permutation80 hz
    mixedMoment B raw4101step1 raw4101step1Labels = mixedMoment B raw4101step2 raw4101step2Labels := by
      have ha : raw4101step2 = (fun i j => raw4101step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4101step2 raw4101step1; decide +kernel
      have hl : raw4101step2Labels = raw4101step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4101step1 raw4101step1Labels permutation31 permutation4
    _ = mixedMoment B node3396 node3396Labels := by rfl

def raw4102 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4102Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4102step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4102 raw4102Labels = mixedMoment B node3495 node3495Labels := by
  calc
    mixedMoment B raw4102 raw4102Labels = mixedMoment B raw4102step0 raw4102step0Labels := by
      have ha : raw4102step0 = (fun i j => raw4102 (permutation613 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4102step0 raw4102; decide +kernel
      have hl : raw4102step0Labels = raw4102Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4102 raw4102Labels permutation613 permutation2
    _ = mixedMoment B node3495 node3495Labels := by rfl

def raw4103 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4103Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4103step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4103step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4103 raw4103Labels = mixedMoment B node3543 node3543Labels := by
  calc
    mixedMoment B raw4103 raw4103Labels = mixedMoment B raw4103step0 raw4103step0Labels := by
      have hz : ∀ j, raw4103 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4103step0 = (fun i j => raw4103 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4103step0 raw4103; decide +kernel
      have hl : raw4103step0Labels = raw4103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4103 raw4103Labels permutation434 hz
    mixedMoment B raw4103step0 raw4103step0Labels = mixedMoment B raw4103step1 raw4103step1Labels := by
      have ha : raw4103step1 = (fun i j => raw4103step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4103step1 raw4103step0; decide +kernel
      have hl : raw4103step1Labels = raw4103step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4103step0 raw4103step0Labels permutation137 permutation2
    _ = mixedMoment B node3543 node3543Labels := by rfl

def raw4104 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4104Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4104step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4104step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4104 raw4104Labels = mixedMoment B node2055 node2055Labels := by
  calc
    mixedMoment B raw4104 raw4104Labels = mixedMoment B raw4104step0 raw4104step0Labels := by
      have hz : ∀ j, raw4104 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4104step0 = (fun i j => raw4104 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4104step0 raw4104; decide +kernel
      have hl : raw4104step0Labels = raw4104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4104 raw4104Labels permutation434 hz
    mixedMoment B raw4104step0 raw4104step0Labels = mixedMoment B raw4104step1 raw4104step1Labels := by
      have ha : raw4104step1 = (fun i j => raw4104step0 (permutation136 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4104step1 raw4104step0; decide +kernel
      have hl : raw4104step1Labels = raw4104step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4104step0 raw4104step0Labels permutation136 permutation2
    _ = mixedMoment B node2055 node2055Labels := by rfl

def raw4105 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4105Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4105step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4105step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4105 raw4105Labels = mixedMoment B node3495 node3495Labels := by
  calc
    mixedMoment B raw4105 raw4105Labels = mixedMoment B raw4105step0 raw4105step0Labels := by
      have ha : raw4105step0 = (fun i j => raw4105 (permutation608 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4105step0 raw4105; decide +kernel
      have hl : raw4105step0Labels = raw4105Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4105 raw4105Labels permutation608 permutation2
    _ = mixedMoment B node3495 node3495Labels := by rfl

def raw4106 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4106Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4106step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4106step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4106step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4106step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4106 raw4106Labels = mixedMoment B node3154 node3154Labels := by
  calc
    mixedMoment B raw4106 raw4106Labels = mixedMoment B raw4106step0 raw4106step0Labels := by
      have hz : ∀ j, raw4106 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4106step0 = (fun i j => raw4106 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4106step0 raw4106; decide +kernel
      have hl : raw4106step0Labels = raw4106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4106 raw4106Labels permutation434 hz
    mixedMoment B raw4106step0 raw4106step0Labels = mixedMoment B raw4106step1 raw4106step1Labels := by
      have ha : raw4106step1 = (fun i j => raw4106step0 (permutation104 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4106step1 raw4106step0; decide +kernel
      have hl : raw4106step1Labels = raw4106step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4106step0 raw4106step0Labels permutation104 permutation2
    mixedMoment B raw4106step1 raw4106step1Labels = mixedMoment B raw4106step2 raw4106step2Labels := by
      have ha : raw4106step2 = -raw4106step1 := by apply Matrix.ext; change ∀ i j, raw4106step2 i j = -(raw4106step1 i j); unfold raw4106step2 raw4106step1; decide +kernel
      have hl : raw4106step2Labels = raw4106step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3154 node3154Labels := by rfl

def raw4107 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4107Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4107step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4107 raw4107Labels = mixedMoment B node3389 node3389Labels := by
  calc
    mixedMoment B raw4107 raw4107Labels = mixedMoment B raw4107step0 raw4107step0Labels := by
      have hz : ∀ j, raw4107 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4107step0 = (fun i j => raw4107 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4107step0 raw4107; decide +kernel
      have hl : raw4107step0Labels = raw4107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4107 raw4107Labels permutation434 hz
    mixedMoment B raw4107step0 raw4107step0Labels = mixedMoment B raw4107step1 raw4107step1Labels := by
      have ha : raw4107step1 = (fun i j => raw4107step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4107step1 raw4107step0; decide +kernel
      have hl : raw4107step1Labels = raw4107step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4107step0 raw4107step0Labels permutation149 permutation4
    _ = mixedMoment B node3389 node3389Labels := by rfl

def raw4108 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4108Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4108step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4108step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4108step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4108 raw4108Labels = mixedMoment B node3154 node3154Labels := by
  calc
    mixedMoment B raw4108 raw4108Labels = mixedMoment B raw4108step0 raw4108step0Labels := by
      have hz : ∀ j, raw4108 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4108step0 = (fun i j => raw4108 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4108step0 raw4108; decide +kernel
      have hl : raw4108step0Labels = raw4108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4108 raw4108Labels permutation346 hz
    mixedMoment B raw4108step0 raw4108step0Labels = mixedMoment B raw4108step1 raw4108step1Labels := by
      have ha : raw4108step1 = (fun i j => raw4108step0 (permutation104 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4108step1 raw4108step0; decide +kernel
      have hl : raw4108step1Labels = raw4108step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4108step0 raw4108step0Labels permutation104 permutation2
    mixedMoment B raw4108step1 raw4108step1Labels = mixedMoment B raw4108step2 raw4108step2Labels := by
      have ha : raw4108step2 = -raw4108step1 := by apply Matrix.ext; change ∀ i j, raw4108step2 i j = -(raw4108step1 i j); unfold raw4108step2 raw4108step1; decide +kernel
      have hl : raw4108step2Labels = raw4108step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3154 node3154Labels := by rfl

def raw4109 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4109Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4109step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4109step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw4109step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4109 raw4109Labels = mixedMoment B node2063 node2063Labels := by
  calc
    mixedMoment B raw4109 raw4109Labels = mixedMoment B raw4109step0 raw4109step0Labels := by
      have hz : ∀ j, raw4109 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4109step0 = (fun i j => raw4109 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4109step0 raw4109; decide +kernel
      have hl : raw4109step0Labels = raw4109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4109 raw4109Labels permutation434 hz
    mixedMoment B raw4109step0 raw4109step0Labels = mixedMoment B raw4109step1 raw4109step1Labels := by
      have hz : ∀ j, raw4109step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4109step1 = (fun i j => raw4109step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4109step1 raw4109step0; decide +kernel
      have hl : raw4109step1Labels = raw4109step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4109step0 raw4109step0Labels permutation80 hz
    mixedMoment B raw4109step1 raw4109step1Labels = mixedMoment B raw4109step2 raw4109step2Labels := by
      have ha : raw4109step2 = (fun i j => raw4109step1 (permutation28 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4109step2 raw4109step1; decide +kernel
      have hl : raw4109step2Labels = raw4109step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4109step1 raw4109step1Labels permutation28 permutation2
    _ = mixedMoment B node2063 node2063Labels := by rfl

def raw4110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4110step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw4110step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4110step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw4110step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4110step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw4110step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4110 raw4110Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw4110 raw4110Labels = mixedMoment B raw4110step0 raw4110step0Labels := by
      have hz : ∀ j, raw4110 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4110step0 = (fun i j => raw4110 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4110step0 raw4110; decide +kernel
      have hl : raw4110step0Labels = raw4110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4110 raw4110Labels permutation346 hz
    mixedMoment B raw4110step0 raw4110step0Labels = mixedMoment B raw4110step1 raw4110step1Labels := by
      have ha : raw4110step1 = (fun i j => raw4110step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4110step1 raw4110step0; decide +kernel
      have hl : raw4110step1Labels = raw4110step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4110step0 raw4110step0Labels permutation145 permutation3
    mixedMoment B raw4110step1 raw4110step1Labels = mixedMoment B raw4110step2 raw4110step2Labels := by
      have ha : raw4110step2 = -raw4110step1 := by apply Matrix.ext; change ∀ i j, raw4110step2 i j = -(raw4110step1 i j); unfold raw4110step2 raw4110step1; decide +kernel
      have hl : raw4110step2Labels = raw4110step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4110step2 raw4110step2Labels = mixedMoment B raw4110step3 raw4110step3Labels := by
      have ha : raw4110step3 = raw4110step2 := by apply Matrix.ext; unfold raw4110step3 raw4110step2; decide +kernel
      have hl : raw4110step2Labels = labelEmbedding6 ∘ raw4110step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4110step2 raw4110step2Labels raw4110step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw4111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4111Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4111step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw4111step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4111step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4111step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4111step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4111step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4111 raw4111Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw4111 raw4111Labels = mixedMoment B raw4111step0 raw4111step0Labels := by
      have ha : raw4111step0 = (fun i j => raw4111 (permutation616 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4111step0 raw4111; decide +kernel
      have hl : raw4111step0Labels = raw4111Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4111 raw4111Labels permutation616 permutation3
    mixedMoment B raw4111step0 raw4111step0Labels = mixedMoment B raw4111step1 raw4111step1Labels := by
      have ha : raw4111step1 = -raw4111step0 := by apply Matrix.ext; change ∀ i j, raw4111step1 i j = -(raw4111step0 i j); unfold raw4111step1 raw4111step0; decide +kernel
      have hl : raw4111step1Labels = raw4111step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4111step1 raw4111step1Labels = mixedMoment B raw4111step2 raw4111step2Labels := by
      have ha : raw4111step2 = raw4111step1 := by apply Matrix.ext; unfold raw4111step2 raw4111step1; decide +kernel
      have hl : raw4111step1Labels = labelEmbedding6 ∘ raw4111step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4111step1 raw4111step1Labels raw4111step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw4112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4112step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw4112step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4112step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4112step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4112step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4112 raw4112Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw4112 raw4112Labels = mixedMoment B raw4112step0 raw4112step0Labels := by
      have hz : ∀ j, raw4112 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4112step0 = (fun i j => raw4112 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4112step0 raw4112; decide +kernel
      have hl : raw4112step0Labels = raw4112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4112 raw4112Labels permutation346 hz
    mixedMoment B raw4112step0 raw4112step0Labels = mixedMoment B raw4112step1 raw4112step1Labels := by
      have ha : raw4112step1 = (fun i j => raw4112step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4112step1 raw4112step0; decide +kernel
      have hl : raw4112step1Labels = raw4112step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4112step0 raw4112step0Labels permutation139 permutation3
    mixedMoment B raw4112step1 raw4112step1Labels = mixedMoment B raw4112step2 raw4112step2Labels := by
      have ha : raw4112step2 = -raw4112step1 := by apply Matrix.ext; change ∀ i j, raw4112step2 i j = -(raw4112step1 i j); unfold raw4112step2 raw4112step1; decide +kernel
      have hl : raw4112step2Labels = raw4112step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4112step2 raw4112step2Labels = mixedMoment B raw4112step3 raw4112step3Labels := by
      have ha : raw4112step3 = raw4112step2 := by apply Matrix.ext; unfold raw4112step3 raw4112step2; decide +kernel
      have hl : raw4112step2Labels = labelEmbedding6 ∘ raw4112step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4112step2 raw4112step2Labels raw4112step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw4113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4113step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw4113step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4113step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4113step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4113step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4113 raw4113Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw4113 raw4113Labels = mixedMoment B raw4113step0 raw4113step0Labels := by
      have hz : ∀ j, raw4113 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4113step0 = (fun i j => raw4113 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4113step0 raw4113; decide +kernel
      have hl : raw4113step0Labels = raw4113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4113 raw4113Labels permutation346 hz
    mixedMoment B raw4113step0 raw4113step0Labels = mixedMoment B raw4113step1 raw4113step1Labels := by
      have ha : raw4113step1 = (fun i j => raw4113step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4113step1 raw4113step0; decide +kernel
      have hl : raw4113step1Labels = raw4113step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4113step0 raw4113step0Labels permutation137 permutation3
    mixedMoment B raw4113step1 raw4113step1Labels = mixedMoment B raw4113step2 raw4113step2Labels := by
      have ha : raw4113step2 = -raw4113step1 := by apply Matrix.ext; change ∀ i j, raw4113step2 i j = -(raw4113step1 i j); unfold raw4113step2 raw4113step1; decide +kernel
      have hl : raw4113step2Labels = raw4113step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4113step2 raw4113step2Labels = mixedMoment B raw4113step3 raw4113step3Labels := by
      have ha : raw4113step3 = raw4113step2 := by apply Matrix.ext; unfold raw4113step3 raw4113step2; decide +kernel
      have hl : raw4113step2Labels = labelEmbedding6 ∘ raw4113step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4113step2 raw4113step2Labels raw4113step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw4114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4114Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4114step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw4114step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4114step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4114step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4114step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4114step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4114 raw4114Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw4114 raw4114Labels = mixedMoment B raw4114step0 raw4114step0Labels := by
      have hz : ∀ j, raw4114 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4114step0 = (fun i j => raw4114 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4114step0 raw4114; decide +kernel
      have hl : raw4114step0Labels = raw4114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4114 raw4114Labels permutation346 hz
    mixedMoment B raw4114step0 raw4114step0Labels = mixedMoment B raw4114step1 raw4114step1Labels := by
      have ha : raw4114step1 = (fun i j => raw4114step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4114step1 raw4114step0; decide +kernel
      have hl : raw4114step1Labels = raw4114step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4114step0 raw4114step0Labels permutation32 permutation7
    mixedMoment B raw4114step1 raw4114step1Labels = mixedMoment B raw4114step2 raw4114step2Labels := by
      have ha : raw4114step2 = -raw4114step1 := by apply Matrix.ext; change ∀ i j, raw4114step2 i j = -(raw4114step1 i j); unfold raw4114step2 raw4114step1; decide +kernel
      have hl : raw4114step2Labels = raw4114step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4114step2 raw4114step2Labels = mixedMoment B raw4114step3 raw4114step3Labels := by
      have ha : raw4114step3 = raw4114step2 := by apply Matrix.ext; unfold raw4114step3 raw4114step2; decide +kernel
      have hl : raw4114step2Labels = labelEmbedding10 ∘ raw4114step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4114step2 raw4114step2Labels raw4114step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw4115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4115step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw4115step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4115step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw4115step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4115 raw4115Labels = mixedMoment B node4584 node4584Labels := by
  calc
    mixedMoment B raw4115 raw4115Labels = mixedMoment B raw4115step0 raw4115step0Labels := by
      have hz : ∀ j, raw4115 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4115step0 = (fun i j => raw4115 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4115step0 raw4115; decide +kernel
      have hl : raw4115step0Labels = raw4115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4115 raw4115Labels permutation346 hz
    mixedMoment B raw4115step0 raw4115step0Labels = mixedMoment B raw4115step1 raw4115step1Labels := by
      have ha : raw4115step1 = (fun i j => raw4115step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4115step1 raw4115step0; decide +kernel
      have hl : raw4115step1Labels = raw4115step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4115step0 raw4115step0Labels permutation40 permutation3
    mixedMoment B raw4115step1 raw4115step1Labels = mixedMoment B raw4115step2 raw4115step2Labels := by
      have ha : raw4115step2 = raw4115step1 := by apply Matrix.ext; unfold raw4115step2 raw4115step1; decide +kernel
      have hl : raw4115step1Labels = labelEmbedding6 ∘ raw4115step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4115step1 raw4115step1Labels raw4115step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4584 node4584Labels := by rfl

def raw4116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4116step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4116step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4116step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4116step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4116step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4116step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4116 raw4116Labels = mixedMoment B node4992 node4992Labels := by
  calc
    mixedMoment B raw4116 raw4116Labels = mixedMoment B raw4116step0 raw4116step0Labels := by
      have ha : raw4116step0 = (fun i j => raw4116 (permutation616 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4116step0 raw4116; decide +kernel
      have hl : raw4116step0Labels = raw4116Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4116 raw4116Labels permutation616 permutation3
    mixedMoment B raw4116step0 raw4116step0Labels = mixedMoment B raw4116step1 raw4116step1Labels := by
      have ha : raw4116step1 = -raw4116step0 := by apply Matrix.ext; change ∀ i j, raw4116step1 i j = -(raw4116step0 i j); unfold raw4116step1 raw4116step0; decide +kernel
      have hl : raw4116step1Labels = raw4116step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4116step1 raw4116step1Labels = mixedMoment B raw4116step2 raw4116step2Labels := by
      have ha : raw4116step2 = raw4116step1 := by apply Matrix.ext; unfold raw4116step2 raw4116step1; decide +kernel
      have hl : raw4116step1Labels = labelEmbedding6 ∘ raw4116step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4116step1 raw4116step1Labels raw4116step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4992 node4992Labels := by rfl

def raw4117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4117Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4117step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4117step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4117step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4117step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4117step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4117step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4117 raw4117Labels = mixedMoment B node5001 node5001Labels := by
  calc
    mixedMoment B raw4117 raw4117Labels = mixedMoment B raw4117step0 raw4117step0Labels := by
      have hz : ∀ j, raw4117 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4117step0 = (fun i j => raw4117 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4117step0 raw4117; decide +kernel
      have hl : raw4117step0Labels = raw4117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4117 raw4117Labels permutation346 hz
    mixedMoment B raw4117step0 raw4117step0Labels = mixedMoment B raw4117step1 raw4117step1Labels := by
      have ha : raw4117step1 = (fun i j => raw4117step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4117step1 raw4117step0; decide +kernel
      have hl : raw4117step1Labels = raw4117step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4117step0 raw4117step0Labels permutation139 permutation3
    mixedMoment B raw4117step1 raw4117step1Labels = mixedMoment B raw4117step2 raw4117step2Labels := by
      have ha : raw4117step2 = -raw4117step1 := by apply Matrix.ext; change ∀ i j, raw4117step2 i j = -(raw4117step1 i j); unfold raw4117step2 raw4117step1; decide +kernel
      have hl : raw4117step2Labels = raw4117step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4117step2 raw4117step2Labels = mixedMoment B raw4117step3 raw4117step3Labels := by
      have ha : raw4117step3 = raw4117step2 := by apply Matrix.ext; unfold raw4117step3 raw4117step2; decide +kernel
      have hl : raw4117step2Labels = labelEmbedding6 ∘ raw4117step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4117step2 raw4117step2Labels raw4117step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5001 node5001Labels := by rfl

def raw4118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4118step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4118step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4118step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4118step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4118step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4118 raw4118Labels = mixedMoment B node5001 node5001Labels := by
  calc
    mixedMoment B raw4118 raw4118Labels = mixedMoment B raw4118step0 raw4118step0Labels := by
      have hz : ∀ j, raw4118 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4118step0 = (fun i j => raw4118 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4118step0 raw4118; decide +kernel
      have hl : raw4118step0Labels = raw4118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4118 raw4118Labels permutation346 hz
    mixedMoment B raw4118step0 raw4118step0Labels = mixedMoment B raw4118step1 raw4118step1Labels := by
      have ha : raw4118step1 = (fun i j => raw4118step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4118step1 raw4118step0; decide +kernel
      have hl : raw4118step1Labels = raw4118step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4118step0 raw4118step0Labels permutation137 permutation3
    mixedMoment B raw4118step1 raw4118step1Labels = mixedMoment B raw4118step2 raw4118step2Labels := by
      have ha : raw4118step2 = -raw4118step1 := by apply Matrix.ext; change ∀ i j, raw4118step2 i j = -(raw4118step1 i j); unfold raw4118step2 raw4118step1; decide +kernel
      have hl : raw4118step2Labels = raw4118step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4118step2 raw4118step2Labels = mixedMoment B raw4118step3 raw4118step3Labels := by
      have ha : raw4118step3 = raw4118step2 := by apply Matrix.ext; unfold raw4118step3 raw4118step2; decide +kernel
      have hl : raw4118step2Labels = labelEmbedding6 ∘ raw4118step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4118step2 raw4118step2Labels raw4118step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5001 node5001Labels := by rfl

def raw4119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4119step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw4119step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4119 raw4119Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw4119 raw4119Labels = mixedMoment B raw4119step0 raw4119step0Labels := by
      have hz : ∀ j, raw4119 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4119step0 = (fun i j => raw4119 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4119step0 raw4119; decide +kernel
      have hl : raw4119step0Labels = raw4119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4119 raw4119Labels permutation346 hz
    mixedMoment B raw4119step0 raw4119step0Labels = mixedMoment B raw4119step1 raw4119step1Labels := by
      have ha : raw4119step1 = (fun i j => raw4119step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4119step1 raw4119step0; decide +kernel
      have hl : raw4119step1Labels = raw4119step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4119step0 raw4119step0Labels permutation40 permutation2
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw4120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4120step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4120step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4120step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4120 raw4120Labels = mixedMoment B node4577 node4577Labels := by
  calc
    mixedMoment B raw4120 raw4120Labels = mixedMoment B raw4120step0 raw4120step0Labels := by
      have ha : raw4120step0 = (fun i j => raw4120 (permutation212 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4120step0 raw4120; decide +kernel
      have hl : raw4120step0Labels = raw4120Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4120 raw4120Labels permutation212 permutation3
    mixedMoment B raw4120step0 raw4120step0Labels = mixedMoment B raw4120step1 raw4120step1Labels := by
      have ha : raw4120step1 = raw4120step0 := by apply Matrix.ext; unfold raw4120step1 raw4120step0; decide +kernel
      have hl : raw4120step0Labels = labelEmbedding6 ∘ raw4120step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4120step0 raw4120step0Labels raw4120step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4577 node4577Labels := by rfl

def raw4121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4121step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4121step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4121 raw4121Labels = mixedMoment B node5065 node5065Labels := by
  calc
    mixedMoment B raw4121 raw4121Labels = mixedMoment B raw4121step0 raw4121step0Labels := by
      have ha : raw4121step0 = (fun i j => raw4121 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4121step0 raw4121; decide +kernel
      have hl : raw4121step0Labels = raw4121Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4121 raw4121Labels permutation160 permutation2
    _ = mixedMoment B node5065 node5065Labels := by rfl

def raw4122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4122step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4122step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4122step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4122step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4122step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4122 raw4122Labels = mixedMoment B node5048 node5048Labels := by
  calc
    mixedMoment B raw4122 raw4122Labels = mixedMoment B raw4122step0 raw4122step0Labels := by
      have ha : raw4122step0 = (fun i j => raw4122 (permutation634 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4122step0 raw4122; decide +kernel
      have hl : raw4122step0Labels = raw4122Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4122 raw4122Labels permutation634 permutation3
    mixedMoment B raw4122step0 raw4122step0Labels = mixedMoment B raw4122step1 raw4122step1Labels := by
      have ha : raw4122step1 = -raw4122step0 := by apply Matrix.ext; change ∀ i j, raw4122step1 i j = -(raw4122step0 i j); unfold raw4122step1 raw4122step0; decide +kernel
      have hl : raw4122step1Labels = raw4122step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4122step1 raw4122step1Labels = mixedMoment B raw4122step2 raw4122step2Labels := by
      have ha : raw4122step2 = raw4122step1 := by apply Matrix.ext; unfold raw4122step2 raw4122step1; decide +kernel
      have hl : raw4122step1Labels = labelEmbedding6 ∘ raw4122step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4122step1 raw4122step1Labels raw4122step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5048 node5048Labels := by rfl

def raw4123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4123step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4123step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4123step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4123step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4123step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4123 raw4123Labels = mixedMoment B node5048 node5048Labels := by
  calc
    mixedMoment B raw4123 raw4123Labels = mixedMoment B raw4123step0 raw4123step0Labels := by
      have ha : raw4123step0 = (fun i j => raw4123 (permutation632 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4123step0 raw4123; decide +kernel
      have hl : raw4123step0Labels = raw4123Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4123 raw4123Labels permutation632 permutation3
    mixedMoment B raw4123step0 raw4123step0Labels = mixedMoment B raw4123step1 raw4123step1Labels := by
      have ha : raw4123step1 = -raw4123step0 := by apply Matrix.ext; change ∀ i j, raw4123step1 i j = -(raw4123step0 i j); unfold raw4123step1 raw4123step0; decide +kernel
      have hl : raw4123step1Labels = raw4123step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4123step1 raw4123step1Labels = mixedMoment B raw4123step2 raw4123step2Labels := by
      have ha : raw4123step2 = raw4123step1 := by apply Matrix.ext; unfold raw4123step2 raw4123step1; decide +kernel
      have hl : raw4123step1Labels = labelEmbedding6 ∘ raw4123step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4123step1 raw4123step1Labels raw4123step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5048 node5048Labels := by rfl

def raw4124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw4124step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4124 raw4124Labels = mixedMoment B node5250 node5250Labels := by
  calc
    mixedMoment B raw4124 raw4124Labels = mixedMoment B raw4124step0 raw4124step0Labels := by
      have ha : raw4124step0 = (fun i j => raw4124 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4124step0 raw4124; decide +kernel
      have hl : raw4124step0Labels = raw4124Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4124 raw4124Labels permutation160 permutation2
    _ = mixedMoment B node5250 node5250Labels := by rfl

def raw4125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4125step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4125step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4125step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4125step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4125 raw4125Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw4125 raw4125Labels = mixedMoment B raw4125step0 raw4125step0Labels := by
      have hz : ∀ j, raw4125 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4125step0 = (fun i j => raw4125 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4125step0 raw4125; decide +kernel
      have hl : raw4125step0Labels = raw4125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4125 raw4125Labels permutation346 hz
    mixedMoment B raw4125step0 raw4125step0Labels = mixedMoment B raw4125step1 raw4125step1Labels := by
      have ha : raw4125step1 = (fun i j => raw4125step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4125step1 raw4125step0; decide +kernel
      have hl : raw4125step1Labels = raw4125step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4125step0 raw4125step0Labels permutation44 permutation3
    mixedMoment B raw4125step1 raw4125step1Labels = mixedMoment B raw4125step2 raw4125step2Labels := by
      have ha : raw4125step2 = raw4125step1 := by apply Matrix.ext; unfold raw4125step2 raw4125step1; decide +kernel
      have hl : raw4125step1Labels = labelEmbedding6 ∘ raw4125step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4125step1 raw4125step1Labels raw4125step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw4126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4126step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4126step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4126 raw4126Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw4126 raw4126Labels = mixedMoment B raw4126step0 raw4126step0Labels := by
      have hz : ∀ j, raw4126 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4126step0 = (fun i j => raw4126 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4126step0 raw4126; decide +kernel
      have hl : raw4126step0Labels = raw4126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4126 raw4126Labels permutation346 hz
    mixedMoment B raw4126step0 raw4126step0Labels = mixedMoment B raw4126step1 raw4126step1Labels := by
      have ha : raw4126step1 = (fun i j => raw4126step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4126step1 raw4126step0; decide +kernel
      have hl : raw4126step1Labels = raw4126step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4126step0 raw4126step0Labels permutation34 permutation2
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw4127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4127step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4127step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4127 raw4127Labels = mixedMoment B node5128 node5128Labels := by
  calc
    mixedMoment B raw4127 raw4127Labels = mixedMoment B raw4127step0 raw4127step0Labels := by
      have ha : raw4127step0 = (fun i j => raw4127 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4127step0 raw4127; decide +kernel
      have hl : raw4127step0Labels = raw4127Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4127 raw4127Labels permutation178 permutation2
    _ = mixedMoment B node5128 node5128Labels := by rfl

def raw4128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4128step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4128step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4128step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4128step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4128 raw4128Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw4128 raw4128Labels = mixedMoment B raw4128step0 raw4128step0Labels := by
      have hz : ∀ j, raw4128 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4128step0 = (fun i j => raw4128 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4128step0 raw4128; decide +kernel
      have hl : raw4128step0Labels = raw4128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4128 raw4128Labels permutation346 hz
    mixedMoment B raw4128step0 raw4128step0Labels = mixedMoment B raw4128step1 raw4128step1Labels := by
      have ha : raw4128step1 = (fun i j => raw4128step0 (permutation143 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4128step1 raw4128step0; decide +kernel
      have hl : raw4128step1Labels = raw4128step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4128step0 raw4128step0Labels permutation143 permutation3
    mixedMoment B raw4128step1 raw4128step1Labels = mixedMoment B raw4128step2 raw4128step2Labels := by
      have ha : raw4128step2 = -raw4128step1 := by apply Matrix.ext; change ∀ i j, raw4128step2 i j = -(raw4128step1 i j); unfold raw4128step2 raw4128step1; decide +kernel
      have hl : raw4128step2Labels = raw4128step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4128step2 raw4128step2Labels = mixedMoment B raw4128step3 raw4128step3Labels := by
      have ha : raw4128step3 = raw4128step2 := by apply Matrix.ext; unfold raw4128step3 raw4128step2; decide +kernel
      have hl : raw4128step2Labels = labelEmbedding6 ∘ raw4128step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4128step2 raw4128step2Labels raw4128step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5139 node5139Labels := by rfl

def raw4129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4129step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw4129step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4129 raw4129Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw4129 raw4129Labels = mixedMoment B raw4129step0 raw4129step0Labels := by
      have hz : ∀ j, raw4129 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4129step0 = (fun i j => raw4129 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4129step0 raw4129; decide +kernel
      have hl : raw4129step0Labels = raw4129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4129 raw4129Labels permutation346 hz
    mixedMoment B raw4129step0 raw4129step0Labels = mixedMoment B raw4129step1 raw4129step1Labels := by
      have ha : raw4129step1 = (fun i j => raw4129step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4129step1 raw4129step0; decide +kernel
      have hl : raw4129step1Labels = raw4129step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4129step0 raw4129step0Labels permutation34 permutation2
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw4130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4130step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4130step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4130step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4130 raw4130Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw4130 raw4130Labels = mixedMoment B raw4130step0 raw4130step0Labels := by
      have hz : ∀ j, raw4130 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4130step0 = (fun i j => raw4130 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4130step0 raw4130; decide +kernel
      have hl : raw4130step0Labels = raw4130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4130 raw4130Labels permutation346 hz
    mixedMoment B raw4130step0 raw4130step0Labels = mixedMoment B raw4130step1 raw4130step1Labels := by
      have ha : raw4130step1 = (fun i j => raw4130step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4130step1 raw4130step0; decide +kernel
      have hl : raw4130step1Labels = raw4130step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4130step0 raw4130step0Labels permutation38 permutation3
    mixedMoment B raw4130step1 raw4130step1Labels = mixedMoment B raw4130step2 raw4130step2Labels := by
      have ha : raw4130step2 = raw4130step1 := by apply Matrix.ext; unfold raw4130step2 raw4130step1; decide +kernel
      have hl : raw4130step1Labels = labelEmbedding6 ∘ raw4130step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4130step1 raw4130step1Labels raw4130step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw4131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4131step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4131 raw4131Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw4131 raw4131Labels = mixedMoment B raw4131step0 raw4131step0Labels := by
      have hz : ∀ j, raw4131 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4131step0 = (fun i j => raw4131 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4131step0 raw4131; decide +kernel
      have hl : raw4131step0Labels = raw4131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4131 raw4131Labels permutation346 hz
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw4132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4132step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4132 raw4132Labels = mixedMoment B node5128 node5128Labels := by
  calc
    mixedMoment B raw4132 raw4132Labels = mixedMoment B raw4132step0 raw4132step0Labels := by
      have ha : raw4132step0 = (fun i j => raw4132 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4132step0 raw4132; decide +kernel
      have hl : raw4132step0Labels = raw4132Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4132 raw4132Labels permutation176 permutation2
    _ = mixedMoment B node5128 node5128Labels := by rfl

def raw4133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4133step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4133step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4133step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4133step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4133step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4133step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4133 raw4133Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw4133 raw4133Labels = mixedMoment B raw4133step0 raw4133step0Labels := by
      have hz : ∀ j, raw4133 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4133step0 = (fun i j => raw4133 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4133step0 raw4133; decide +kernel
      have hl : raw4133step0Labels = raw4133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4133 raw4133Labels permutation346 hz
    mixedMoment B raw4133step0 raw4133step0Labels = mixedMoment B raw4133step1 raw4133step1Labels := by
      have ha : raw4133step1 = (fun i j => raw4133step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4133step1 raw4133step0; decide +kernel
      have hl : raw4133step1Labels = raw4133step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4133step0 raw4133step0Labels permutation149 permutation3
    mixedMoment B raw4133step1 raw4133step1Labels = mixedMoment B raw4133step2 raw4133step2Labels := by
      have ha : raw4133step2 = -raw4133step1 := by apply Matrix.ext; change ∀ i j, raw4133step2 i j = -(raw4133step1 i j); unfold raw4133step2 raw4133step1; decide +kernel
      have hl : raw4133step2Labels = raw4133step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4133step2 raw4133step2Labels = mixedMoment B raw4133step3 raw4133step3Labels := by
      have ha : raw4133step3 = raw4133step2 := by apply Matrix.ext; unfold raw4133step3 raw4133step2; decide +kernel
      have hl : raw4133step2Labels = labelEmbedding6 ∘ raw4133step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4133step2 raw4133step2Labels raw4133step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5139 node5139Labels := by rfl

def raw4134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw4134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw4134step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4134 raw4134Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw4134 raw4134Labels = mixedMoment B raw4134step0 raw4134step0Labels := by
      have hz : ∀ j, raw4134 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4134step0 = (fun i j => raw4134 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4134step0 raw4134; decide +kernel
      have hl : raw4134step0Labels = raw4134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4134 raw4134Labels permutation346 hz
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw4135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw4135step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4135step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw4135step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4135step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw4135step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4135 raw4135Labels = mixedMoment B node4394 node4394Labels := by
  calc
    mixedMoment B raw4135 raw4135Labels = mixedMoment B raw4135step0 raw4135step0Labels := by
      have hz : ∀ j, raw4135 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4135step0 = (fun i j => raw4135 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4135step0 raw4135; decide +kernel
      have hl : raw4135step0Labels = raw4135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4135 raw4135Labels permutation346 hz
    mixedMoment B raw4135step0 raw4135step0Labels = mixedMoment B raw4135step1 raw4135step1Labels := by
      have ha : raw4135step1 = (fun i j => raw4135step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4135step1 raw4135step0; decide +kernel
      have hl : raw4135step1Labels = raw4135step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4135step0 raw4135step0Labels permutation137 permutation3
    mixedMoment B raw4135step1 raw4135step1Labels = mixedMoment B raw4135step2 raw4135step2Labels := by
      have ha : raw4135step2 = -raw4135step1 := by apply Matrix.ext; change ∀ i j, raw4135step2 i j = -(raw4135step1 i j); unfold raw4135step2 raw4135step1; decide +kernel
      have hl : raw4135step2Labels = raw4135step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4135step2 raw4135step2Labels = mixedMoment B raw4135step3 raw4135step3Labels := by
      have ha : raw4135step3 = raw4135step2 := by apply Matrix.ext; unfold raw4135step3 raw4135step2; decide +kernel
      have hl : raw4135step2Labels = labelEmbedding6 ∘ raw4135step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4135step2 raw4135step2Labels raw4135step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4394 node4394Labels := by rfl

def raw4136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4136step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4136step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4136step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4136step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4136step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4136step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4136step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4136 raw4136Labels = mixedMoment B node4440 node4440Labels := by
  calc
    mixedMoment B raw4136 raw4136Labels = mixedMoment B raw4136step0 raw4136step0Labels := by
      have hz : ∀ j, raw4136 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4136step0 = (fun i j => raw4136 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4136step0 raw4136; decide +kernel
      have hl : raw4136step0Labels = raw4136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4136 raw4136Labels permutation346 hz
    mixedMoment B raw4136step0 raw4136step0Labels = mixedMoment B raw4136step1 raw4136step1Labels := by
      have ha : raw4136step1 = (fun i j => raw4136step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4136step1 raw4136step0; decide +kernel
      have hl : raw4136step1Labels = raw4136step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4136step0 raw4136step0Labels permutation145 permutation3
    mixedMoment B raw4136step1 raw4136step1Labels = mixedMoment B raw4136step2 raw4136step2Labels := by
      have ha : raw4136step2 = -raw4136step1 := by apply Matrix.ext; change ∀ i j, raw4136step2 i j = -(raw4136step1 i j); unfold raw4136step2 raw4136step1; decide +kernel
      have hl : raw4136step2Labels = raw4136step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4136step2 raw4136step2Labels = mixedMoment B raw4136step3 raw4136step3Labels := by
      have ha : raw4136step3 = raw4136step2 := by apply Matrix.ext; unfold raw4136step3 raw4136step2; decide +kernel
      have hl : raw4136step2Labels = labelEmbedding6 ∘ raw4136step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4136step2 raw4136step2Labels raw4136step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4440 node4440Labels := by rfl

def raw4137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4137step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4137step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4137step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4137step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4137step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4137 raw4137Labels = mixedMoment B node4391 node4391Labels := by
  calc
    mixedMoment B raw4137 raw4137Labels = mixedMoment B raw4137step0 raw4137step0Labels := by
      have ha : raw4137step0 = (fun i j => raw4137 (permutation616 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4137step0 raw4137; decide +kernel
      have hl : raw4137step0Labels = raw4137Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4137 raw4137Labels permutation616 permutation3
    mixedMoment B raw4137step0 raw4137step0Labels = mixedMoment B raw4137step1 raw4137step1Labels := by
      have ha : raw4137step1 = -raw4137step0 := by apply Matrix.ext; change ∀ i j, raw4137step1 i j = -(raw4137step0 i j); unfold raw4137step1 raw4137step0; decide +kernel
      have hl : raw4137step1Labels = raw4137step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4137step1 raw4137step1Labels = mixedMoment B raw4137step2 raw4137step2Labels := by
      have ha : raw4137step2 = raw4137step1 := by apply Matrix.ext; unfold raw4137step2 raw4137step1; decide +kernel
      have hl : raw4137step1Labels = labelEmbedding6 ∘ raw4137step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4137step1 raw4137step1Labels raw4137step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4391 node4391Labels := by rfl

def raw4138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4138step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4138step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4138step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4138step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4138step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4138 raw4138Labels = mixedMoment B node4402 node4402Labels := by
  calc
    mixedMoment B raw4138 raw4138Labels = mixedMoment B raw4138step0 raw4138step0Labels := by
      have hz : ∀ j, raw4138 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4138step0 = (fun i j => raw4138 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4138step0 raw4138; decide +kernel
      have hl : raw4138step0Labels = raw4138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4138 raw4138Labels permutation346 hz
    mixedMoment B raw4138step0 raw4138step0Labels = mixedMoment B raw4138step1 raw4138step1Labels := by
      have ha : raw4138step1 = (fun i j => raw4138step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4138step1 raw4138step0; decide +kernel
      have hl : raw4138step1Labels = raw4138step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4138step0 raw4138step0Labels permutation139 permutation3
    mixedMoment B raw4138step1 raw4138step1Labels = mixedMoment B raw4138step2 raw4138step2Labels := by
      have ha : raw4138step2 = -raw4138step1 := by apply Matrix.ext; change ∀ i j, raw4138step2 i j = -(raw4138step1 i j); unfold raw4138step2 raw4138step1; decide +kernel
      have hl : raw4138step2Labels = raw4138step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4138step2 raw4138step2Labels = mixedMoment B raw4138step3 raw4138step3Labels := by
      have ha : raw4138step3 = raw4138step2 := by apply Matrix.ext; unfold raw4138step3 raw4138step2; decide +kernel
      have hl : raw4138step2Labels = labelEmbedding6 ∘ raw4138step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4138step2 raw4138step2Labels raw4138step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4402 node4402Labels := by rfl

def raw4139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![4, -3, -1]]
def raw4139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![4, -3, -1]]
def raw4139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4139step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4139step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4139step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4139step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4139step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4139 raw4139Labels = mixedMoment B node4402 node4402Labels := by
  calc
    mixedMoment B raw4139 raw4139Labels = mixedMoment B raw4139step0 raw4139step0Labels := by
      have hz : ∀ j, raw4139 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4139step0 = (fun i j => raw4139 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4139step0 raw4139; decide +kernel
      have hl : raw4139step0Labels = raw4139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4139 raw4139Labels permutation346 hz
    mixedMoment B raw4139step0 raw4139step0Labels = mixedMoment B raw4139step1 raw4139step1Labels := by
      have ha : raw4139step1 = (fun i j => raw4139step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4139step1 raw4139step0; decide +kernel
      have hl : raw4139step1Labels = raw4139step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4139step0 raw4139step0Labels permutation137 permutation3
    mixedMoment B raw4139step1 raw4139step1Labels = mixedMoment B raw4139step2 raw4139step2Labels := by
      have ha : raw4139step2 = -raw4139step1 := by apply Matrix.ext; change ∀ i j, raw4139step2 i j = -(raw4139step1 i j); unfold raw4139step2 raw4139step1; decide +kernel
      have hl : raw4139step2Labels = raw4139step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4139step2 raw4139step2Labels = mixedMoment B raw4139step3 raw4139step3Labels := by
      have ha : raw4139step3 = raw4139step2 := by apply Matrix.ext; unfold raw4139step3 raw4139step2; decide +kernel
      have hl : raw4139step2Labels = labelEmbedding6 ∘ raw4139step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4139step2 raw4139step2Labels raw4139step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4402 node4402Labels := by rfl

def raw4140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4140Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4140step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw4140step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw4140step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4140 raw4140Labels = mixedMoment B node2753 node2753Labels := by
  calc
    mixedMoment B raw4140 raw4140Labels = mixedMoment B raw4140step0 raw4140step0Labels := by
      have hz : ∀ j, raw4140 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4140step0 = (fun i j => raw4140 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4140step0 raw4140; decide +kernel
      have hl : raw4140step0Labels = raw4140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4140 raw4140Labels permutation346 hz
    mixedMoment B raw4140step0 raw4140step0Labels = mixedMoment B raw4140step1 raw4140step1Labels := by
      have ha : raw4140step1 = (fun i j => raw4140step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4140step1 raw4140step0; decide +kernel
      have hl : raw4140step1Labels = raw4140step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4140step0 raw4140step0Labels permutation145 permutation3
    mixedMoment B raw4140step1 raw4140step1Labels = mixedMoment B raw4140step2 raw4140step2Labels := by
      have ha : raw4140step2 = -raw4140step1 := by apply Matrix.ext; change ∀ i j, raw4140step2 i j = -(raw4140step1 i j); unfold raw4140step2 raw4140step1; decide +kernel
      have hl : raw4140step2Labels = raw4140step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2753 node2753Labels := by rfl

def raw4141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4141Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw4141step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw4141step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4141 raw4141Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw4141 raw4141Labels = mixedMoment B raw4141step0 raw4141step0Labels := by
      have ha : raw4141step0 = (fun i j => raw4141 (permutation616 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4141step0 raw4141; decide +kernel
      have hl : raw4141step0Labels = raw4141Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4141 raw4141Labels permutation616 permutation3
    mixedMoment B raw4141step0 raw4141step0Labels = mixedMoment B raw4141step1 raw4141step1Labels := by
      have ha : raw4141step1 = -raw4141step0 := by apply Matrix.ext; change ∀ i j, raw4141step1 i j = -(raw4141step0 i j); unfold raw4141step1 raw4141step0; decide +kernel
      have hl : raw4141step1Labels = raw4141step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2710 node2710Labels := by rfl

def raw4142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4142Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4142step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw4142step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4142step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4142 raw4142Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw4142 raw4142Labels = mixedMoment B raw4142step0 raw4142step0Labels := by
      have hz : ∀ j, raw4142 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4142step0 = (fun i j => raw4142 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4142step0 raw4142; decide +kernel
      have hl : raw4142step0Labels = raw4142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4142 raw4142Labels permutation346 hz
    mixedMoment B raw4142step0 raw4142step0Labels = mixedMoment B raw4142step1 raw4142step1Labels := by
      have ha : raw4142step1 = (fun i j => raw4142step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4142step1 raw4142step0; decide +kernel
      have hl : raw4142step1Labels = raw4142step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4142step0 raw4142step0Labels permutation139 permutation3
    mixedMoment B raw4142step1 raw4142step1Labels = mixedMoment B raw4142step2 raw4142step2Labels := by
      have ha : raw4142step2 = -raw4142step1 := by apply Matrix.ext; change ∀ i j, raw4142step2 i j = -(raw4142step1 i j); unfold raw4142step2 raw4142step1; decide +kernel
      have hl : raw4142step2Labels = raw4142step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw4143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4143Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4143step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw4143step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw4143step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4143 raw4143Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw4143 raw4143Labels = mixedMoment B raw4143step0 raw4143step0Labels := by
      have hz : ∀ j, raw4143 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4143step0 = (fun i j => raw4143 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4143step0 raw4143; decide +kernel
      have hl : raw4143step0Labels = raw4143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4143 raw4143Labels permutation346 hz
    mixedMoment B raw4143step0 raw4143step0Labels = mixedMoment B raw4143step1 raw4143step1Labels := by
      have ha : raw4143step1 = (fun i j => raw4143step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4143step1 raw4143step0; decide +kernel
      have hl : raw4143step1Labels = raw4143step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4143step0 raw4143step0Labels permutation137 permutation3
    mixedMoment B raw4143step1 raw4143step1Labels = mixedMoment B raw4143step2 raw4143step2Labels := by
      have ha : raw4143step2 = -raw4143step1 := by apply Matrix.ext; change ∀ i j, raw4143step2 i j = -(raw4143step1 i j); unfold raw4143step2 raw4143step1; decide +kernel
      have hl : raw4143step2Labels = raw4143step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw4144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4144Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4144step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw4144step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4144step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw4144step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4144 raw4144Labels = mixedMoment B node4012 node4012Labels := by
  calc
    mixedMoment B raw4144 raw4144Labels = mixedMoment B raw4144step0 raw4144step0Labels := by
      have hz : ∀ j, raw4144 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4144step0 = (fun i j => raw4144 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4144step0 raw4144; decide +kernel
      have hl : raw4144step0Labels = raw4144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4144 raw4144Labels permutation346 hz
    mixedMoment B raw4144step0 raw4144step0Labels = mixedMoment B raw4144step1 raw4144step1Labels := by
      have ha : raw4144step1 = (fun i j => raw4144step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4144step1 raw4144step0; decide +kernel
      have hl : raw4144step1Labels = raw4144step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4144step0 raw4144step0Labels permutation137 permutation3
    mixedMoment B raw4144step1 raw4144step1Labels = mixedMoment B raw4144step2 raw4144step2Labels := by
      have ha : raw4144step2 = -raw4144step1 := by apply Matrix.ext; change ∀ i j, raw4144step2 i j = -(raw4144step1 i j); unfold raw4144step2 raw4144step1; decide +kernel
      have hl : raw4144step2Labels = raw4144step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4012 node4012Labels := by rfl

def raw4145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4145Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4145step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw4145step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4145 raw4145Labels = mixedMoment B node1203 node1203Labels := by
  calc
    mixedMoment B raw4145 raw4145Labels = mixedMoment B raw4145step0 raw4145step0Labels := by
      have hz : ∀ j, raw4145 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4145step0 = (fun i j => raw4145 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4145step0 raw4145; decide +kernel
      have hl : raw4145step0Labels = raw4145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4145 raw4145Labels permutation346 hz
    mixedMoment B raw4145step0 raw4145step0Labels = mixedMoment B raw4145step1 raw4145step1Labels := by
      have ha : raw4145step1 = (fun i j => raw4145step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4145step1 raw4145step0; decide +kernel
      have hl : raw4145step1Labels = raw4145step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4145step0 raw4145step0Labels permutation40 permutation3
    _ = mixedMoment B node1203 node1203Labels := by rfl

def raw4146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4146Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4146step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4146step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4146step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4146 raw4146Labels = mixedMoment B node2378 node2378Labels := by
  calc
    mixedMoment B raw4146 raw4146Labels = mixedMoment B raw4146step0 raw4146step0Labels := by
      have ha : raw4146step0 = (fun i j => raw4146 (permutation616 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4146step0 raw4146; decide +kernel
      have hl : raw4146step0Labels = raw4146Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4146 raw4146Labels permutation616 permutation3
    mixedMoment B raw4146step0 raw4146step0Labels = mixedMoment B raw4146step1 raw4146step1Labels := by
      have ha : raw4146step1 = -raw4146step0 := by apply Matrix.ext; change ∀ i j, raw4146step1 i j = -(raw4146step0 i j); unfold raw4146step1 raw4146step0; decide +kernel
      have hl : raw4146step1Labels = raw4146step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2378 node2378Labels := by rfl

def raw4147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4147Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4147step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4147step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4147step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4147 raw4147Labels = mixedMoment B node2386 node2386Labels := by
  calc
    mixedMoment B raw4147 raw4147Labels = mixedMoment B raw4147step0 raw4147step0Labels := by
      have hz : ∀ j, raw4147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4147step0 = (fun i j => raw4147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4147step0 raw4147; decide +kernel
      have hl : raw4147step0Labels = raw4147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4147 raw4147Labels permutation346 hz
    mixedMoment B raw4147step0 raw4147step0Labels = mixedMoment B raw4147step1 raw4147step1Labels := by
      have ha : raw4147step1 = (fun i j => raw4147step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4147step1 raw4147step0; decide +kernel
      have hl : raw4147step1Labels = raw4147step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4147step0 raw4147step0Labels permutation139 permutation3
    mixedMoment B raw4147step1 raw4147step1Labels = mixedMoment B raw4147step2 raw4147step2Labels := by
      have ha : raw4147step2 = -raw4147step1 := by apply Matrix.ext; change ∀ i j, raw4147step2 i j = -(raw4147step1 i j); unfold raw4147step2 raw4147step1; decide +kernel
      have hl : raw4147step2Labels = raw4147step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2386 node2386Labels := by rfl

def raw4148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4148Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4148step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4148step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4148step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4148 raw4148Labels = mixedMoment B node2386 node2386Labels := by
  calc
    mixedMoment B raw4148 raw4148Labels = mixedMoment B raw4148step0 raw4148step0Labels := by
      have hz : ∀ j, raw4148 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4148step0 = (fun i j => raw4148 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4148step0 raw4148; decide +kernel
      have hl : raw4148step0Labels = raw4148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4148 raw4148Labels permutation346 hz
    mixedMoment B raw4148step0 raw4148step0Labels = mixedMoment B raw4148step1 raw4148step1Labels := by
      have ha : raw4148step1 = (fun i j => raw4148step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4148step1 raw4148step0; decide +kernel
      have hl : raw4148step1Labels = raw4148step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4148step0 raw4148step0Labels permutation137 permutation3
    mixedMoment B raw4148step1 raw4148step1Labels = mixedMoment B raw4148step2 raw4148step2Labels := by
      have ha : raw4148step2 = -raw4148step1 := by apply Matrix.ext; change ∀ i j, raw4148step2 i j = -(raw4148step1 i j); unfold raw4148step2 raw4148step1; decide +kernel
      have hl : raw4148step2Labels = raw4148step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2386 node2386Labels := by rfl

def raw4149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4149Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4149step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw4149step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4149 raw4149Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw4149 raw4149Labels = mixedMoment B raw4149step0 raw4149step0Labels := by
      have hz : ∀ j, raw4149 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4149step0 = (fun i j => raw4149 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4149step0 raw4149; decide +kernel
      have hl : raw4149step0Labels = raw4149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4149 raw4149Labels permutation346 hz
    mixedMoment B raw4149step0 raw4149step0Labels = mixedMoment B raw4149step1 raw4149step1Labels := by
      have ha : raw4149step1 = (fun i j => raw4149step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4149step1 raw4149step0; decide +kernel
      have hl : raw4149step1Labels = raw4149step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4149step0 raw4149step0Labels permutation40 permutation3
    _ = mixedMoment B node3078 node3078Labels := by rfl

def raw4150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4150Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4150step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw4150step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4150 raw4150Labels = mixedMoment B node1195 node1195Labels := by
  calc
    mixedMoment B raw4150 raw4150Labels = mixedMoment B raw4150step0 raw4150step0Labels := by
      have ha : raw4150step0 = (fun i j => raw4150 (permutation212 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4150step0 raw4150; decide +kernel
      have hl : raw4150step0Labels = raw4150Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4150 raw4150Labels permutation212 permutation3
    _ = mixedMoment B node1195 node1195Labels := by rfl

def raw4151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4151Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4151step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4151step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4151step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4151 raw4151Labels = mixedMoment B node2470 node2470Labels := by
  calc
    mixedMoment B raw4151 raw4151Labels = mixedMoment B raw4151step0 raw4151step0Labels := by
      have ha : raw4151step0 = (fun i j => raw4151 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4151step0 raw4151; decide +kernel
      have hl : raw4151step0Labels = raw4151Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4151 raw4151Labels permutation640 permutation3
    mixedMoment B raw4151step0 raw4151step0Labels = mixedMoment B raw4151step1 raw4151step1Labels := by
      have ha : raw4151step1 = -raw4151step0 := by apply Matrix.ext; change ∀ i j, raw4151step1 i j = -(raw4151step0 i j); unfold raw4151step1 raw4151step0; decide +kernel
      have hl : raw4151step1Labels = raw4151step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2470 node2470Labels := by rfl

def raw4152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4152Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4152step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4152step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4152step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4152step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4152 raw4152Labels = mixedMoment B node2450 node2450Labels := by
  calc
    mixedMoment B raw4152 raw4152Labels = mixedMoment B raw4152step0 raw4152step0Labels := by
      have ha : raw4152step0 = (fun i j => raw4152 (permutation634 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4152step0 raw4152; decide +kernel
      have hl : raw4152step0Labels = raw4152Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4152 raw4152Labels permutation634 permutation3
    mixedMoment B raw4152step0 raw4152step0Labels = mixedMoment B raw4152step1 raw4152step1Labels := by
      have ha : raw4152step1 = -raw4152step0 := by apply Matrix.ext; change ∀ i j, raw4152step1 i j = -(raw4152step0 i j); unfold raw4152step1 raw4152step0; decide +kernel
      have hl : raw4152step1Labels = raw4152step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2450 node2450Labels := by rfl

def raw4153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4153Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4153step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4153step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4153step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4153step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4153 raw4153Labels = mixedMoment B node2450 node2450Labels := by
  calc
    mixedMoment B raw4153 raw4153Labels = mixedMoment B raw4153step0 raw4153step0Labels := by
      have ha : raw4153step0 = (fun i j => raw4153 (permutation632 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4153step0 raw4153; decide +kernel
      have hl : raw4153step0Labels = raw4153Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4153 raw4153Labels permutation632 permutation3
    mixedMoment B raw4153step0 raw4153step0Labels = mixedMoment B raw4153step1 raw4153step1Labels := by
      have ha : raw4153step1 = -raw4153step0 := by apply Matrix.ext; change ∀ i j, raw4153step1 i j = -(raw4153step0 i j); unfold raw4153step1 raw4153step0; decide +kernel
      have hl : raw4153step1Labels = raw4153step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2450 node2450Labels := by rfl

def raw4154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4154Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw4154step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4154 raw4154Labels = mixedMoment B node3065 node3065Labels := by
  calc
    mixedMoment B raw4154 raw4154Labels = mixedMoment B raw4154step0 raw4154step0Labels := by
      have ha : raw4154step0 = (fun i j => raw4154 (permutation212 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4154step0 raw4154; decide +kernel
      have hl : raw4154step0Labels = raw4154Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4154 raw4154Labels permutation212 permutation3
    _ = mixedMoment B node3065 node3065Labels := by rfl

def raw4155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4155Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4155step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4155step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4155 raw4155Labels = mixedMoment B node1215 node1215Labels := by
  calc
    mixedMoment B raw4155 raw4155Labels = mixedMoment B raw4155step0 raw4155step0Labels := by
      have hz : ∀ j, raw4155 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4155step0 = (fun i j => raw4155 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4155step0 raw4155; decide +kernel
      have hl : raw4155step0Labels = raw4155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4155 raw4155Labels permutation346 hz
    mixedMoment B raw4155step0 raw4155step0Labels = mixedMoment B raw4155step1 raw4155step1Labels := by
      have ha : raw4155step1 = (fun i j => raw4155step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4155step1 raw4155step0; decide +kernel
      have hl : raw4155step1Labels = raw4155step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4155step0 raw4155step0Labels permutation44 permutation3
    _ = mixedMoment B node1215 node1215Labels := by rfl

def raw4156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4156Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4156step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4156step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4156step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4156step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4156 raw4156Labels = mixedMoment B node2572 node2572Labels := by
  calc
    mixedMoment B raw4156 raw4156Labels = mixedMoment B raw4156step0 raw4156step0Labels := by
      have hz : ∀ j, raw4156 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4156step0 = (fun i j => raw4156 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4156step0 raw4156; decide +kernel
      have hl : raw4156step0Labels = raw4156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4156 raw4156Labels permutation346 hz
    mixedMoment B raw4156step0 raw4156step0Labels = mixedMoment B raw4156step1 raw4156step1Labels := by
      have ha : raw4156step1 = (fun i j => raw4156step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4156step1 raw4156step0; decide +kernel
      have hl : raw4156step1Labels = raw4156step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4156step0 raw4156step0Labels permutation145 permutation3
    mixedMoment B raw4156step1 raw4156step1Labels = mixedMoment B raw4156step2 raw4156step2Labels := by
      have ha : raw4156step2 = -raw4156step1 := by apply Matrix.ext; change ∀ i j, raw4156step2 i j = -(raw4156step1 i j); unfold raw4156step2 raw4156step1; decide +kernel
      have hl : raw4156step2Labels = raw4156step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2572 node2572Labels := by rfl

def raw4157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4157Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4157step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4157step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4157step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4157 raw4157Labels = mixedMoment B node2543 node2543Labels := by
  calc
    mixedMoment B raw4157 raw4157Labels = mixedMoment B raw4157step0 raw4157step0Labels := by
      have ha : raw4157step0 = (fun i j => raw4157 (permutation654 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4157step0 raw4157; decide +kernel
      have hl : raw4157step0Labels = raw4157Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4157 raw4157Labels permutation654 permutation3
    mixedMoment B raw4157step0 raw4157step0Labels = mixedMoment B raw4157step1 raw4157step1Labels := by
      have ha : raw4157step1 = -raw4157step0 := by apply Matrix.ext; change ∀ i j, raw4157step1 i j = -(raw4157step0 i j); unfold raw4157step1 raw4157step0; decide +kernel
      have hl : raw4157step1Labels = raw4157step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2543 node2543Labels := by rfl

def raw4158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4158Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4158step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4158step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4158step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4158step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4158 raw4158Labels = mixedMoment B node2558 node2558Labels := by
  calc
    mixedMoment B raw4158 raw4158Labels = mixedMoment B raw4158step0 raw4158step0Labels := by
      have hz : ∀ j, raw4158 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4158step0 = (fun i j => raw4158 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4158step0 raw4158; decide +kernel
      have hl : raw4158step0Labels = raw4158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4158 raw4158Labels permutation346 hz
    mixedMoment B raw4158step0 raw4158step0Labels = mixedMoment B raw4158step1 raw4158step1Labels := by
      have ha : raw4158step1 = (fun i j => raw4158step0 (permutation143 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4158step1 raw4158step0; decide +kernel
      have hl : raw4158step1Labels = raw4158step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4158step0 raw4158step0Labels permutation143 permutation3
    mixedMoment B raw4158step1 raw4158step1Labels = mixedMoment B raw4158step2 raw4158step2Labels := by
      have ha : raw4158step2 = -raw4158step1 := by apply Matrix.ext; change ∀ i j, raw4158step2 i j = -(raw4158step1 i j); unfold raw4158step2 raw4158step1; decide +kernel
      have hl : raw4158step2Labels = raw4158step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2558 node2558Labels := by rfl

def raw4159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4159Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4159step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw4159step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4159 raw4159Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw4159 raw4159Labels = mixedMoment B raw4159step0 raw4159step0Labels := by
      have hz : ∀ j, raw4159 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4159step0 = (fun i j => raw4159 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4159step0 raw4159; decide +kernel
      have hl : raw4159step0Labels = raw4159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4159 raw4159Labels permutation346 hz
    mixedMoment B raw4159step0 raw4159step0Labels = mixedMoment B raw4159step1 raw4159step1Labels := by
      have ha : raw4159step1 = (fun i j => raw4159step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4159step1 raw4159step0; decide +kernel
      have hl : raw4159step1Labels = raw4159step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4159step0 raw4159step0Labels permutation44 permutation3
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw4160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4160Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4160step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4160step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4160 raw4160Labels = mixedMoment B node1215 node1215Labels := by
  calc
    mixedMoment B raw4160 raw4160Labels = mixedMoment B raw4160step0 raw4160step0Labels := by
      have hz : ∀ j, raw4160 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4160step0 = (fun i j => raw4160 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4160step0 raw4160; decide +kernel
      have hl : raw4160step0Labels = raw4160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4160 raw4160Labels permutation346 hz
    mixedMoment B raw4160step0 raw4160step0Labels = mixedMoment B raw4160step1 raw4160step1Labels := by
      have ha : raw4160step1 = (fun i j => raw4160step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4160step1 raw4160step0; decide +kernel
      have hl : raw4160step1Labels = raw4160step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4160step0 raw4160step0Labels permutation38 permutation3
    _ = mixedMoment B node1215 node1215Labels := by rfl

def raw4161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4161Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4161step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4161step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4161step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4161step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4161 raw4161Labels = mixedMoment B node2572 node2572Labels := by
  calc
    mixedMoment B raw4161 raw4161Labels = mixedMoment B raw4161step0 raw4161step0Labels := by
      have hz : ∀ j, raw4161 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4161step0 = (fun i j => raw4161 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4161step0 raw4161; decide +kernel
      have hl : raw4161step0Labels = raw4161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4161 raw4161Labels permutation346 hz
    mixedMoment B raw4161step0 raw4161step0Labels = mixedMoment B raw4161step1 raw4161step1Labels := by
      have ha : raw4161step1 = (fun i j => raw4161step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4161step1 raw4161step0; decide +kernel
      have hl : raw4161step1Labels = raw4161step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4161step0 raw4161step0Labels permutation151 permutation3
    mixedMoment B raw4161step1 raw4161step1Labels = mixedMoment B raw4161step2 raw4161step2Labels := by
      have ha : raw4161step2 = -raw4161step1 := by apply Matrix.ext; change ∀ i j, raw4161step2 i j = -(raw4161step1 i j); unfold raw4161step2 raw4161step1; decide +kernel
      have hl : raw4161step2Labels = raw4161step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2572 node2572Labels := by rfl

def raw4162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4162Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4162step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4162step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4162step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4162step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4162 raw4162Labels = mixedMoment B node2543 node2543Labels := by
  calc
    mixedMoment B raw4162 raw4162Labels = mixedMoment B raw4162step0 raw4162step0Labels := by
      have ha : raw4162step0 = (fun i j => raw4162 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4162step0 raw4162; decide +kernel
      have hl : raw4162step0Labels = raw4162Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4162 raw4162Labels permutation676 permutation3
    mixedMoment B raw4162step0 raw4162step0Labels = mixedMoment B raw4162step1 raw4162step1Labels := by
      have ha : raw4162step1 = -raw4162step0 := by apply Matrix.ext; change ∀ i j, raw4162step1 i j = -(raw4162step0 i j); unfold raw4162step1 raw4162step0; decide +kernel
      have hl : raw4162step1Labels = raw4162step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2543 node2543Labels := by rfl

def raw4163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4163Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4163step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4163step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4163step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4163step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4163 raw4163Labels = mixedMoment B node2558 node2558Labels := by
  calc
    mixedMoment B raw4163 raw4163Labels = mixedMoment B raw4163step0 raw4163step0Labels := by
      have hz : ∀ j, raw4163 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4163step0 = (fun i j => raw4163 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4163step0 raw4163; decide +kernel
      have hl : raw4163step0Labels = raw4163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4163 raw4163Labels permutation346 hz
    mixedMoment B raw4163step0 raw4163step0Labels = mixedMoment B raw4163step1 raw4163step1Labels := by
      have ha : raw4163step1 = (fun i j => raw4163step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4163step1 raw4163step0; decide +kernel
      have hl : raw4163step1Labels = raw4163step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4163step0 raw4163step0Labels permutation149 permutation3
    mixedMoment B raw4163step1 raw4163step1Labels = mixedMoment B raw4163step2 raw4163step2Labels := by
      have ha : raw4163step2 = -raw4163step1 := by apply Matrix.ext; change ∀ i j, raw4163step2 i j = -(raw4163step1 i j); unfold raw4163step2 raw4163step1; decide +kernel
      have hl : raw4163step2Labels = raw4163step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2558 node2558Labels := by rfl

def raw4164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw4164Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw4164step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw4164step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4164 raw4164Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw4164 raw4164Labels = mixedMoment B raw4164step0 raw4164step0Labels := by
      have hz : ∀ j, raw4164 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4164step0 = (fun i j => raw4164 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4164step0 raw4164; decide +kernel
      have hl : raw4164step0Labels = raw4164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4164 raw4164Labels permutation346 hz
    mixedMoment B raw4164step0 raw4164step0Labels = mixedMoment B raw4164step1 raw4164step1Labels := by
      have ha : raw4164step1 = (fun i j => raw4164step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4164step1 raw4164step0; decide +kernel
      have hl : raw4164step1Labels = raw4164step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4164step0 raw4164step0Labels permutation38 permutation3
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw4165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4165step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-4, 2, 2]]
def raw4165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4165step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw4165step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4165 raw4165Labels = mixedMoment B node975 node975Labels := by
  calc
    mixedMoment B raw4165 raw4165Labels = mixedMoment B raw4165step0 raw4165step0Labels := by
      have hz : ∀ j, raw4165 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4165step0 = (fun i j => raw4165 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4165step0 raw4165; decide +kernel
      have hl : raw4165step0Labels = raw4165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4165 raw4165Labels permutation346 hz
    mixedMoment B raw4165step0 raw4165step0Labels = mixedMoment B raw4165step1 raw4165step1Labels := by
      have ha : raw4165step1 = (fun i j => raw4165step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4165step1 raw4165step0; decide +kernel
      have hl : raw4165step1Labels = raw4165step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4165step0 raw4165step0Labels permutation137 permutation3
    mixedMoment B raw4165step1 raw4165step1Labels = mixedMoment B raw4165step2 raw4165step2Labels := by
      have ha : raw4165step2 = -raw4165step1 := by apply Matrix.ext; change ∀ i j, raw4165step2 i j = -(raw4165step1 i j); unfold raw4165step2 raw4165step1; decide +kernel
      have hl : raw4165step2Labels = raw4165step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node975 node975Labels := by rfl

def raw4166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4166step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4166step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw4166step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4166step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4166 raw4166Labels = mixedMoment B node1022 node1022Labels := by
  calc
    mixedMoment B raw4166 raw4166Labels = mixedMoment B raw4166step0 raw4166step0Labels := by
      have hz : ∀ j, raw4166 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4166step0 = (fun i j => raw4166 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4166step0 raw4166; decide +kernel
      have hl : raw4166step0Labels = raw4166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4166 raw4166Labels permutation346 hz
    mixedMoment B raw4166step0 raw4166step0Labels = mixedMoment B raw4166step1 raw4166step1Labels := by
      have ha : raw4166step1 = (fun i j => raw4166step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4166step1 raw4166step0; decide +kernel
      have hl : raw4166step1Labels = raw4166step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4166step0 raw4166step0Labels permutation145 permutation3
    mixedMoment B raw4166step1 raw4166step1Labels = mixedMoment B raw4166step2 raw4166step2Labels := by
      have ha : raw4166step2 = -raw4166step1 := by apply Matrix.ext; change ∀ i j, raw4166step2 i j = -(raw4166step1 i j); unfold raw4166step2 raw4166step1; decide +kernel
      have hl : raw4166step2Labels = raw4166step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1022 node1022Labels := by rfl

def raw4167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4167step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw4167step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4167step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4167 raw4167Labels = mixedMoment B node972 node972Labels := by
  calc
    mixedMoment B raw4167 raw4167Labels = mixedMoment B raw4167step0 raw4167step0Labels := by
      have ha : raw4167step0 = (fun i j => raw4167 (permutation616 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4167step0 raw4167; decide +kernel
      have hl : raw4167step0Labels = raw4167Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4167 raw4167Labels permutation616 permutation3
    mixedMoment B raw4167step0 raw4167step0Labels = mixedMoment B raw4167step1 raw4167step1Labels := by
      have ha : raw4167step1 = -raw4167step0 := by apply Matrix.ext; change ∀ i j, raw4167step1 i j = -(raw4167step0 i j); unfold raw4167step1 raw4167step0; decide +kernel
      have hl : raw4167step1Labels = raw4167step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node972 node972Labels := by rfl

def raw4168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4168step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4168 raw4168Labels = mixedMoment B node983 node983Labels := by
  calc
    mixedMoment B raw4168 raw4168Labels = mixedMoment B raw4168step0 raw4168step0Labels := by
      have hz : ∀ j, raw4168 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4168step0 = (fun i j => raw4168 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4168step0 raw4168; decide +kernel
      have hl : raw4168step0Labels = raw4168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4168 raw4168Labels permutation346 hz
    mixedMoment B raw4168step0 raw4168step0Labels = mixedMoment B raw4168step1 raw4168step1Labels := by
      have ha : raw4168step1 = (fun i j => raw4168step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4168step1 raw4168step0; decide +kernel
      have hl : raw4168step1Labels = raw4168step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4168step0 raw4168step0Labels permutation139 permutation3
    mixedMoment B raw4168step1 raw4168step1Labels = mixedMoment B raw4168step2 raw4168step2Labels := by
      have ha : raw4168step2 = -raw4168step1 := by apply Matrix.ext; change ∀ i j, raw4168step2 i j = -(raw4168step1 i j); unfold raw4168step2 raw4168step1; decide +kernel
      have hl : raw4168step2Labels = raw4168step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node983 node983Labels := by rfl

def raw4169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![4, -3, -1]]
def raw4169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![4, -3, -1]]
def raw4169step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw4169step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw4169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4169 raw4169Labels = mixedMoment B node983 node983Labels := by
  calc
    mixedMoment B raw4169 raw4169Labels = mixedMoment B raw4169step0 raw4169step0Labels := by
      have hz : ∀ j, raw4169 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4169step0 = (fun i j => raw4169 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4169step0 raw4169; decide +kernel
      have hl : raw4169step0Labels = raw4169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4169 raw4169Labels permutation346 hz
    mixedMoment B raw4169step0 raw4169step0Labels = mixedMoment B raw4169step1 raw4169step1Labels := by
      have ha : raw4169step1 = (fun i j => raw4169step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4169step1 raw4169step0; decide +kernel
      have hl : raw4169step1Labels = raw4169step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4169step0 raw4169step0Labels permutation137 permutation3
    mixedMoment B raw4169step1 raw4169step1Labels = mixedMoment B raw4169step2 raw4169step2Labels := by
      have ha : raw4169step2 = -raw4169step1 := by apply Matrix.ext; change ∀ i j, raw4169step2 i j = -(raw4169step1 i j); unfold raw4169step2 raw4169step1; decide +kernel
      have hl : raw4169step2Labels = raw4169step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node983 node983Labels := by rfl

def raw4170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4170Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4170step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw4170step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4170step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw4170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4170 raw4170Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw4170 raw4170Labels = mixedMoment B raw4170step0 raw4170step0Labels := by
      have hz : ∀ j, raw4170 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4170step0 = (fun i j => raw4170 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4170step0 raw4170; decide +kernel
      have hl : raw4170step0Labels = raw4170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4170 raw4170Labels permutation346 hz
    mixedMoment B raw4170step0 raw4170step0Labels = mixedMoment B raw4170step1 raw4170step1Labels := by
      have ha : raw4170step1 = (fun i j => raw4170step0 (permutation134 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4170step1 raw4170step0; decide +kernel
      have hl : raw4170step1Labels = raw4170step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4170step0 raw4170step0Labels permutation134 permutation5
    mixedMoment B raw4170step1 raw4170step1Labels = mixedMoment B raw4170step2 raw4170step2Labels := by
      have ha : raw4170step2 = raw4170step1 := by apply Matrix.ext; unfold raw4170step2 raw4170step1; decide +kernel
      have hl : raw4170step1Labels = labelEmbedding1 ∘ raw4170step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4170step1 raw4170step1Labels raw4170step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

def raw4171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4171Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4171step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw4171step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4171step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw4171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4171 raw4171Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw4171 raw4171Labels = mixedMoment B raw4171step0 raw4171step0Labels := by
      have ha : raw4171step0 = (fun i j => raw4171 (permutation605 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4171step0 raw4171; decide +kernel
      have hl : raw4171step0Labels = raw4171Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4171 raw4171Labels permutation605 permutation5
    mixedMoment B raw4171step0 raw4171step0Labels = mixedMoment B raw4171step1 raw4171step1Labels := by
      have ha : raw4171step1 = raw4171step0 := by apply Matrix.ext; unfold raw4171step1 raw4171step0; decide +kernel
      have hl : raw4171step0Labels = labelEmbedding1 ∘ raw4171step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4171step0 raw4171step0Labels raw4171step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

def raw4172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4172Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4172step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw4172step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4172step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw4172step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4172 raw4172Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw4172 raw4172Labels = mixedMoment B raw4172step0 raw4172step0Labels := by
      have hz : ∀ j, raw4172 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4172step0 = (fun i j => raw4172 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4172step0 raw4172; decide +kernel
      have hl : raw4172step0Labels = raw4172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4172 raw4172Labels permutation346 hz
    mixedMoment B raw4172step0 raw4172step0Labels = mixedMoment B raw4172step1 raw4172step1Labels := by
      have ha : raw4172step1 = (fun i j => raw4172step0 (permutation135 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4172step1 raw4172step0; decide +kernel
      have hl : raw4172step1Labels = raw4172step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4172step0 raw4172step0Labels permutation135 permutation5
    mixedMoment B raw4172step1 raw4172step1Labels = mixedMoment B raw4172step2 raw4172step2Labels := by
      have ha : raw4172step2 = raw4172step1 := by apply Matrix.ext; unfold raw4172step2 raw4172step1; decide +kernel
      have hl : raw4172step1Labels = labelEmbedding1 ∘ raw4172step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4172step1 raw4172step1Labels raw4172step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw4173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4173Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4173step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw4173step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4173step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw4173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4173 raw4173Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw4173 raw4173Labels = mixedMoment B raw4173step0 raw4173step0Labels := by
      have hz : ∀ j, raw4173 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4173step0 = (fun i j => raw4173 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4173step0 raw4173; decide +kernel
      have hl : raw4173step0Labels = raw4173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4173 raw4173Labels permutation346 hz
    mixedMoment B raw4173step0 raw4173step0Labels = mixedMoment B raw4173step1 raw4173step1Labels := by
      have ha : raw4173step1 = (fun i j => raw4173step0 (permutation134 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4173step1 raw4173step0; decide +kernel
      have hl : raw4173step1Labels = raw4173step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4173step0 raw4173step0Labels permutation134 permutation5
    mixedMoment B raw4173step1 raw4173step1Labels = mixedMoment B raw4173step2 raw4173step2Labels := by
      have ha : raw4173step2 = raw4173step1 := by apply Matrix.ext; unfold raw4173step2 raw4173step1; decide +kernel
      have hl : raw4173step1Labels = labelEmbedding1 ∘ raw4173step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4173step1 raw4173step1Labels raw4173step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw4174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4174Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4174step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw4174step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4174step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4174step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4174step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4174 raw4174Labels = mixedMoment B node3858 node3858Labels := by
  calc
    mixedMoment B raw4174 raw4174Labels = mixedMoment B raw4174step0 raw4174step0Labels := by
      have hz : ∀ j, raw4174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4174step0 = (fun i j => raw4174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4174step0 raw4174; decide +kernel
      have hl : raw4174step0Labels = raw4174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4174 raw4174Labels permutation346 hz
    mixedMoment B raw4174step0 raw4174step0Labels = mixedMoment B raw4174step1 raw4174step1Labels := by
      have ha : raw4174step1 = (fun i j => raw4174step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4174step1 raw4174step0; decide +kernel
      have hl : raw4174step1Labels = raw4174step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4174step0 raw4174step0Labels permutation32 permutation7
    mixedMoment B raw4174step1 raw4174step1Labels = mixedMoment B raw4174step2 raw4174step2Labels := by
      have ha : raw4174step2 = -raw4174step1 := by apply Matrix.ext; change ∀ i j, raw4174step2 i j = -(raw4174step1 i j); unfold raw4174step2 raw4174step1; decide +kernel
      have hl : raw4174step2Labels = raw4174step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4174step2 raw4174step2Labels = mixedMoment B raw4174step3 raw4174step3Labels := by
      have ha : raw4174step3 = raw4174step2 := by apply Matrix.ext; unfold raw4174step3 raw4174step2; decide +kernel
      have hl : raw4174step2Labels = labelEmbedding1 ∘ raw4174step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4174step2 raw4174step2Labels raw4174step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3858 node3858Labels := by rfl

def raw4175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4175Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4175step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw4175step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4175step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw4175step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4175step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw4175step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4175 raw4175Labels = mixedMoment B node3283 node3283Labels := by
  calc
    mixedMoment B raw4175 raw4175Labels = mixedMoment B raw4175step0 raw4175step0Labels := by
      have hz : ∀ j, raw4175 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4175step0 = (fun i j => raw4175 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4175step0 raw4175; decide +kernel
      have hl : raw4175step0Labels = raw4175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4175 raw4175Labels permutation346 hz
    mixedMoment B raw4175step0 raw4175step0Labels = mixedMoment B raw4175step1 raw4175step1Labels := by
      have ha : raw4175step1 = (fun i j => raw4175step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4175step1 raw4175step0; decide +kernel
      have hl : raw4175step1Labels = raw4175step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4175step0 raw4175step0Labels permutation40 permutation5
    mixedMoment B raw4175step1 raw4175step1Labels = mixedMoment B raw4175step2 raw4175step2Labels := by
      have ha : raw4175step2 = -raw4175step1 := by apply Matrix.ext; change ∀ i j, raw4175step2 i j = -(raw4175step1 i j); unfold raw4175step2 raw4175step1; decide +kernel
      have hl : raw4175step2Labels = raw4175step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4175step2 raw4175step2Labels = mixedMoment B raw4175step3 raw4175step3Labels := by
      have ha : raw4175step3 = raw4175step2 := by apply Matrix.ext; unfold raw4175step3 raw4175step2; decide +kernel
      have hl : raw4175step2Labels = labelEmbedding1 ∘ raw4175step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4175step2 raw4175step2Labels raw4175step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3283 node3283Labels := by rfl

def raw4176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4176step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4176step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4176 raw4176Labels = mixedMoment B node3350 node3350Labels := by
  calc
    mixedMoment B raw4176 raw4176Labels = mixedMoment B raw4176step0 raw4176step0Labels := by
      have ha : raw4176step0 = (fun i j => raw4176 (permutation616 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4176step0 raw4176; decide +kernel
      have hl : raw4176step0Labels = raw4176Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4176 raw4176Labels permutation616 permutation5
    mixedMoment B raw4176step0 raw4176step0Labels = mixedMoment B raw4176step1 raw4176step1Labels := by
      have ha : raw4176step1 = raw4176step0 := by apply Matrix.ext; unfold raw4176step1 raw4176step0; decide +kernel
      have hl : raw4176step0Labels = labelEmbedding1 ∘ raw4176step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4176step0 raw4176step0Labels raw4176step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3350 node3350Labels := by rfl

def raw4177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4177Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4177step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4177step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4177 raw4177Labels = mixedMoment B node3355 node3355Labels := by
  calc
    mixedMoment B raw4177 raw4177Labels = mixedMoment B raw4177step0 raw4177step0Labels := by
      have hz : ∀ j, raw4177 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4177step0 = (fun i j => raw4177 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4177step0 raw4177; decide +kernel
      have hl : raw4177step0Labels = raw4177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4177 raw4177Labels permutation346 hz
    mixedMoment B raw4177step0 raw4177step0Labels = mixedMoment B raw4177step1 raw4177step1Labels := by
      have ha : raw4177step1 = (fun i j => raw4177step0 (permutation138 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4177step1 raw4177step0; decide +kernel
      have hl : raw4177step1Labels = raw4177step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4177step0 raw4177step0Labels permutation138 permutation5
    mixedMoment B raw4177step1 raw4177step1Labels = mixedMoment B raw4177step2 raw4177step2Labels := by
      have ha : raw4177step2 = raw4177step1 := by apply Matrix.ext; unfold raw4177step2 raw4177step1; decide +kernel
      have hl : raw4177step1Labels = labelEmbedding1 ∘ raw4177step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4177step1 raw4177step1Labels raw4177step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3355 node3355Labels := by rfl

def raw4178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4178step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4178step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4178 raw4178Labels = mixedMoment B node3355 node3355Labels := by
  calc
    mixedMoment B raw4178 raw4178Labels = mixedMoment B raw4178step0 raw4178step0Labels := by
      have hz : ∀ j, raw4178 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4178step0 = (fun i j => raw4178 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4178step0 raw4178; decide +kernel
      have hl : raw4178step0Labels = raw4178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4178 raw4178Labels permutation346 hz
    mixedMoment B raw4178step0 raw4178step0Labels = mixedMoment B raw4178step1 raw4178step1Labels := by
      have ha : raw4178step1 = (fun i j => raw4178step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4178step1 raw4178step0; decide +kernel
      have hl : raw4178step1Labels = raw4178step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4178step0 raw4178step0Labels permutation136 permutation5
    mixedMoment B raw4178step1 raw4178step1Labels = mixedMoment B raw4178step2 raw4178step2Labels := by
      have ha : raw4178step2 = raw4178step1 := by apply Matrix.ext; unfold raw4178step2 raw4178step1; decide +kernel
      have hl : raw4178step1Labels = labelEmbedding1 ∘ raw4178step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4178step1 raw4178step1Labels raw4178step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3355 node3355Labels := by rfl

def raw4179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4179Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4179step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw4179step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4179step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4179step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4179step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4179step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4179 raw4179Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw4179 raw4179Labels = mixedMoment B raw4179step0 raw4179step0Labels := by
      have hz : ∀ j, raw4179 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4179step0 = (fun i j => raw4179 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4179step0 raw4179; decide +kernel
      have hl : raw4179step0Labels = raw4179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4179 raw4179Labels permutation346 hz
    mixedMoment B raw4179step0 raw4179step0Labels = mixedMoment B raw4179step1 raw4179step1Labels := by
      have ha : raw4179step1 = (fun i j => raw4179step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4179step1 raw4179step0; decide +kernel
      have hl : raw4179step1Labels = raw4179step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4179step0 raw4179step0Labels permutation32 permutation7
    mixedMoment B raw4179step1 raw4179step1Labels = mixedMoment B raw4179step2 raw4179step2Labels := by
      have ha : raw4179step2 = -raw4179step1 := by apply Matrix.ext; change ∀ i j, raw4179step2 i j = -(raw4179step1 i j); unfold raw4179step2 raw4179step1; decide +kernel
      have hl : raw4179step2Labels = raw4179step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4179step2 raw4179step2Labels = mixedMoment B raw4179step3 raw4179step3Labels := by
      have ha : raw4179step3 = raw4179step2 := by apply Matrix.ext; unfold raw4179step3 raw4179step2; decide +kernel
      have hl : raw4179step2Labels = labelEmbedding1 ∘ raw4179step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4179step2 raw4179step2Labels raw4179step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3580 node3580Labels := by rfl

def raw4180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw4180step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4180step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw4180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4180step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw4180step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4180 raw4180Labels = mixedMoment B node3279 node3279Labels := by
  calc
    mixedMoment B raw4180 raw4180Labels = mixedMoment B raw4180step0 raw4180step0Labels := by
      have ha : raw4180step0 = (fun i j => raw4180 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4180step0 raw4180; decide +kernel
      have hl : raw4180step0Labels = raw4180Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4180 raw4180Labels permutation212 permutation5
    mixedMoment B raw4180step0 raw4180step0Labels = mixedMoment B raw4180step1 raw4180step1Labels := by
      have ha : raw4180step1 = -raw4180step0 := by apply Matrix.ext; change ∀ i j, raw4180step1 i j = -(raw4180step0 i j); unfold raw4180step1 raw4180step0; decide +kernel
      have hl : raw4180step1Labels = raw4180step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4180step1 raw4180step1Labels = mixedMoment B raw4180step2 raw4180step2Labels := by
      have ha : raw4180step2 = raw4180step1 := by apply Matrix.ext; unfold raw4180step2 raw4180step1; decide +kernel
      have hl : raw4180step1Labels = labelEmbedding1 ∘ raw4180step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4180step1 raw4180step1Labels raw4180step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3279 node3279Labels := by rfl

def raw4181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4181step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4181step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4181 raw4181Labels = mixedMoment B node3466 node3466Labels := by
  calc
    mixedMoment B raw4181 raw4181Labels = mixedMoment B raw4181step0 raw4181step0Labels := by
      have ha : raw4181step0 = (fun i j => raw4181 (permutation632 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4181step0 raw4181; decide +kernel
      have hl : raw4181step0Labels = raw4181Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4181 raw4181Labels permutation632 permutation5
    mixedMoment B raw4181step0 raw4181step0Labels = mixedMoment B raw4181step1 raw4181step1Labels := by
      have ha : raw4181step1 = raw4181step0 := by apply Matrix.ext; unfold raw4181step1 raw4181step0; decide +kernel
      have hl : raw4181step0Labels = labelEmbedding1 ∘ raw4181step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4181step0 raw4181step0Labels raw4181step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3466 node3466Labels := by rfl

def raw4182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4182step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4182step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4182step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4182 raw4182Labels = mixedMoment B node3434 node3434Labels := by
  calc
    mixedMoment B raw4182 raw4182Labels = mixedMoment B raw4182step0 raw4182step0Labels := by
      have ha : raw4182step0 = (fun i j => raw4182 (permutation633 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4182step0 raw4182; decide +kernel
      have hl : raw4182step0Labels = raw4182Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4182 raw4182Labels permutation633 permutation5
    mixedMoment B raw4182step0 raw4182step0Labels = mixedMoment B raw4182step1 raw4182step1Labels := by
      have ha : raw4182step1 = raw4182step0 := by apply Matrix.ext; unfold raw4182step1 raw4182step0; decide +kernel
      have hl : raw4182step0Labels = labelEmbedding1 ∘ raw4182step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4182step0 raw4182step0Labels raw4182step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3434 node3434Labels := by rfl

def raw4183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4183Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4183step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4183step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4183step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4183 raw4183Labels = mixedMoment B node3434 node3434Labels := by
  calc
    mixedMoment B raw4183 raw4183Labels = mixedMoment B raw4183step0 raw4183step0Labels := by
      have ha : raw4183step0 = (fun i j => raw4183 (permutation631 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4183step0 raw4183; decide +kernel
      have hl : raw4183step0Labels = raw4183Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4183 raw4183Labels permutation631 permutation5
    mixedMoment B raw4183step0 raw4183step0Labels = mixedMoment B raw4183step1 raw4183step1Labels := by
      have ha : raw4183step1 = raw4183step0 := by apply Matrix.ext; unfold raw4183step1 raw4183step0; decide +kernel
      have hl : raw4183step0Labels = labelEmbedding1 ∘ raw4183step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4183step0 raw4183step0Labels raw4183step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3434 node3434Labels := by rfl

def raw4184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4184Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4184step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw4184step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4184step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4184step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4184step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw4184step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4184 raw4184Labels = mixedMoment B node3531 node3531Labels := by
  calc
    mixedMoment B raw4184 raw4184Labels = mixedMoment B raw4184step0 raw4184step0Labels := by
      have ha : raw4184step0 = (fun i j => raw4184 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4184step0 raw4184; decide +kernel
      have hl : raw4184step0Labels = raw4184Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4184 raw4184Labels permutation152 permutation7
    mixedMoment B raw4184step0 raw4184step0Labels = mixedMoment B raw4184step1 raw4184step1Labels := by
      have ha : raw4184step1 = -raw4184step0 := by apply Matrix.ext; change ∀ i j, raw4184step1 i j = -(raw4184step0 i j); unfold raw4184step1 raw4184step0; decide +kernel
      have hl : raw4184step1Labels = raw4184step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4184step1 raw4184step1Labels = mixedMoment B raw4184step2 raw4184step2Labels := by
      have ha : raw4184step2 = raw4184step1 := by apply Matrix.ext; unfold raw4184step2 raw4184step1; decide +kernel
      have hl : raw4184step1Labels = labelEmbedding1 ∘ raw4184step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4184step1 raw4184step1Labels raw4184step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3531 node3531Labels := by rfl

def raw4185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4185Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4185step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw4185step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4185step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4185step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4185step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4185 raw4185Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw4185 raw4185Labels = mixedMoment B raw4185step0 raw4185step0Labels := by
      have hz : ∀ j, raw4185 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4185step0 = (fun i j => raw4185 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4185step0 raw4185; decide +kernel
      have hl : raw4185step0Labels = raw4185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4185 raw4185Labels permutation346 hz
    mixedMoment B raw4185step0 raw4185step0Labels = mixedMoment B raw4185step1 raw4185step1Labels := by
      have ha : raw4185step1 = (fun i j => raw4185step0 (permutation46 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4185step1 raw4185step0; decide +kernel
      have hl : raw4185step1Labels = raw4185step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4185step0 raw4185step0Labels permutation46 permutation5
    mixedMoment B raw4185step1 raw4185step1Labels = mixedMoment B raw4185step2 raw4185step2Labels := by
      have ha : raw4185step2 = -raw4185step1 := by apply Matrix.ext; change ∀ i j, raw4185step2 i j = -(raw4185step1 i j); unfold raw4185step2 raw4185step1; decide +kernel
      have hl : raw4185step2Labels = raw4185step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4185step2 raw4185step2Labels = mixedMoment B raw4185step3 raw4185step3Labels := by
      have ha : raw4185step3 = raw4185step2 := by apply Matrix.ext; unfold raw4185step3 raw4185step2; decide +kernel
      have hl : raw4185step2Labels = labelEmbedding1 ∘ raw4185step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4185step2 raw4185step2Labels raw4185step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

def raw4186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4186step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw4186step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4186step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4186step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4186step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4186 raw4186Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw4186 raw4186Labels = mixedMoment B raw4186step0 raw4186step0Labels := by
      have hz : ∀ j, raw4186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4186step0 = (fun i j => raw4186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4186step0 raw4186; decide +kernel
      have hl : raw4186step0Labels = raw4186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4186 raw4186Labels permutation346 hz
    mixedMoment B raw4186step0 raw4186step0Labels = mixedMoment B raw4186step1 raw4186step1Labels := by
      have ha : raw4186step1 = (fun i j => raw4186step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4186step1 raw4186step0; decide +kernel
      have hl : raw4186step1Labels = raw4186step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4186step0 raw4186step0Labels permutation34 permutation7
    mixedMoment B raw4186step1 raw4186step1Labels = mixedMoment B raw4186step2 raw4186step2Labels := by
      have ha : raw4186step2 = -raw4186step1 := by apply Matrix.ext; change ∀ i j, raw4186step2 i j = -(raw4186step1 i j); unfold raw4186step2 raw4186step1; decide +kernel
      have hl : raw4186step2Labels = raw4186step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4186step2 raw4186step2Labels = mixedMoment B raw4186step3 raw4186step3Labels := by
      have ha : raw4186step3 = raw4186step2 := by apply Matrix.ext; unfold raw4186step3 raw4186step2; decide +kernel
      have hl : raw4186step2Labels = labelEmbedding1 ∘ raw4186step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4186step2 raw4186step2Labels raw4186step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

def raw4187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4187Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4187step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4187step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4187 raw4187Labels = mixedMoment B node3519 node3519Labels := by
  calc
    mixedMoment B raw4187 raw4187Labels = mixedMoment B raw4187step0 raw4187step0Labels := by
      have ha : raw4187step0 = (fun i j => raw4187 (permutation616 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4187step0 raw4187; decide +kernel
      have hl : raw4187step0Labels = raw4187Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4187 raw4187Labels permutation616 permutation5
    mixedMoment B raw4187step0 raw4187step0Labels = mixedMoment B raw4187step1 raw4187step1Labels := by
      have ha : raw4187step1 = raw4187step0 := by apply Matrix.ext; unfold raw4187step1 raw4187step0; decide +kernel
      have hl : raw4187step0Labels = labelEmbedding1 ∘ raw4187step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4187step0 raw4187step0Labels raw4187step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3519 node3519Labels := by rfl

def raw4188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4188step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw4188step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw4188step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4188 raw4188Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw4188 raw4188Labels = mixedMoment B raw4188step0 raw4188step0Labels := by
      have hz : ∀ j, raw4188 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4188step0 = (fun i j => raw4188 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4188step0 raw4188; decide +kernel
      have hl : raw4188step0Labels = raw4188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4188 raw4188Labels permutation346 hz
    mixedMoment B raw4188step0 raw4188step0Labels = mixedMoment B raw4188step1 raw4188step1Labels := by
      have ha : raw4188step1 = (fun i j => raw4188step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4188step1 raw4188step0; decide +kernel
      have hl : raw4188step1Labels = raw4188step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4188step0 raw4188step0Labels permutation136 permutation5
    mixedMoment B raw4188step1 raw4188step1Labels = mixedMoment B raw4188step2 raw4188step2Labels := by
      have ha : raw4188step2 = raw4188step1 := by apply Matrix.ext; unfold raw4188step2 raw4188step1; decide +kernel
      have hl : raw4188step1Labels = labelEmbedding1 ∘ raw4188step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4188step1 raw4188step1Labels raw4188step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

def raw4189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4189step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw4189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw4189step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4189step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw4189step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4189 raw4189Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw4189 raw4189Labels = mixedMoment B raw4189step0 raw4189step0Labels := by
      have hz : ∀ j, raw4189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4189step0 = (fun i j => raw4189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4189step0 raw4189; decide +kernel
      have hl : raw4189step0Labels = raw4189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4189 raw4189Labels permutation346 hz
    mixedMoment B raw4189step0 raw4189step0Labels = mixedMoment B raw4189step1 raw4189step1Labels := by
      have ha : raw4189step1 = (fun i j => raw4189step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4189step1 raw4189step0; decide +kernel
      have hl : raw4189step1Labels = raw4189step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4189step0 raw4189step0Labels permutation34 permutation7
    mixedMoment B raw4189step1 raw4189step1Labels = mixedMoment B raw4189step2 raw4189step2Labels := by
      have ha : raw4189step2 = -raw4189step1 := by apply Matrix.ext; change ∀ i j, raw4189step2 i j = -(raw4189step1 i j); unfold raw4189step2 raw4189step1; decide +kernel
      have hl : raw4189step2Labels = raw4189step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4189step2 raw4189step2Labels = mixedMoment B raw4189step3 raw4189step3Labels := by
      have ha : raw4189step3 = raw4189step2 := by apply Matrix.ext; unfold raw4189step3 raw4189step2; decide +kernel
      have hl : raw4189step2Labels = labelEmbedding1 ∘ raw4189step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4189step2 raw4189step2Labels raw4189step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw4190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4190step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw4190step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4190step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4190step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw4190step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4190 raw4190Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw4190 raw4190Labels = mixedMoment B raw4190step0 raw4190step0Labels := by
      have hz : ∀ j, raw4190 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4190step0 = (fun i j => raw4190 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4190step0 raw4190; decide +kernel
      have hl : raw4190step0Labels = raw4190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4190 raw4190Labels permutation346 hz
    mixedMoment B raw4190step0 raw4190step0Labels = mixedMoment B raw4190step1 raw4190step1Labels := by
      have ha : raw4190step1 = (fun i j => raw4190step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4190step1 raw4190step0; decide +kernel
      have hl : raw4190step1Labels = raw4190step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4190step0 raw4190step0Labels permutation40 permutation5
    mixedMoment B raw4190step1 raw4190step1Labels = mixedMoment B raw4190step2 raw4190step2Labels := by
      have ha : raw4190step2 = -raw4190step1 := by apply Matrix.ext; change ∀ i j, raw4190step2 i j = -(raw4190step1 i j); unfold raw4190step2 raw4190step1; decide +kernel
      have hl : raw4190step2Labels = raw4190step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4190step2 raw4190step2Labels = mixedMoment B raw4190step3 raw4190step3Labels := by
      have ha : raw4190step3 = raw4190step2 := by apply Matrix.ext; unfold raw4190step3 raw4190step2; decide +kernel
      have hl : raw4190step2Labels = labelEmbedding1 ∘ raw4190step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4190step2 raw4190step2Labels raw4190step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

def raw4191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4191Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4191step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw4191step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4191step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4191step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4191step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4191 raw4191Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw4191 raw4191Labels = mixedMoment B raw4191step0 raw4191step0Labels := by
      have hz : ∀ j, raw4191 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4191step0 = (fun i j => raw4191 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4191step0 raw4191; decide +kernel
      have hl : raw4191step0Labels = raw4191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4191 raw4191Labels permutation346 hz
    mixedMoment B raw4191step0 raw4191step0Labels = mixedMoment B raw4191step1 raw4191step1Labels := by
      have ha : raw4191step1 = (fun i j => raw4191step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4191step1 raw4191step0; decide +kernel
      have hl : raw4191step1Labels = raw4191step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4191step0 raw4191step0Labels permutation32 permutation7
    mixedMoment B raw4191step1 raw4191step1Labels = mixedMoment B raw4191step2 raw4191step2Labels := by
      have ha : raw4191step2 = -raw4191step1 := by apply Matrix.ext; change ∀ i j, raw4191step2 i j = -(raw4191step1 i j); unfold raw4191step2 raw4191step1; decide +kernel
      have hl : raw4191step2Labels = raw4191step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4191step2 raw4191step2Labels = mixedMoment B raw4191step3 raw4191step3Labels := by
      have ha : raw4191step3 = raw4191step2 := by apply Matrix.ext; unfold raw4191step3 raw4191step2; decide +kernel
      have hl : raw4191step2Labels = labelEmbedding1 ∘ raw4191step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4191step2 raw4191step2Labels raw4191step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

def raw4192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4192step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4192step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4192 raw4192Labels = mixedMoment B node3519 node3519Labels := by
  calc
    mixedMoment B raw4192 raw4192Labels = mixedMoment B raw4192step0 raw4192step0Labels := by
      have ha : raw4192step0 = (fun i j => raw4192 (permutation622 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4192step0 raw4192; decide +kernel
      have hl : raw4192step0Labels = raw4192Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4192 raw4192Labels permutation622 permutation5
    mixedMoment B raw4192step0 raw4192step0Labels = mixedMoment B raw4192step1 raw4192step1Labels := by
      have ha : raw4192step1 = raw4192step0 := by apply Matrix.ext; unfold raw4192step1 raw4192step0; decide +kernel
      have hl : raw4192step0Labels = labelEmbedding1 ∘ raw4192step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4192step0 raw4192step0Labels raw4192step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3519 node3519Labels := by rfl

def raw4193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4193Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4193step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw4193step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw4193step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4193 raw4193Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw4193 raw4193Labels = mixedMoment B raw4193step0 raw4193step0Labels := by
      have hz : ∀ j, raw4193 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4193step0 = (fun i j => raw4193 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4193step0 raw4193; decide +kernel
      have hl : raw4193step0Labels = raw4193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4193 raw4193Labels permutation346 hz
    mixedMoment B raw4193step0 raw4193step0Labels = mixedMoment B raw4193step1 raw4193step1Labels := by
      have ha : raw4193step1 = (fun i j => raw4193step0 (permutation138 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4193step1 raw4193step0; decide +kernel
      have hl : raw4193step1Labels = raw4193step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4193step0 raw4193step0Labels permutation138 permutation5
    mixedMoment B raw4193step1 raw4193step1Labels = mixedMoment B raw4193step2 raw4193step2Labels := by
      have ha : raw4193step2 = raw4193step1 := by apply Matrix.ext; unfold raw4193step2 raw4193step1; decide +kernel
      have hl : raw4193step1Labels = labelEmbedding1 ∘ raw4193step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4193step1 raw4193step1Labels raw4193step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

def raw4194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw4194Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw4194step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw4194step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw4194step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4194step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw4194step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4194 raw4194Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw4194 raw4194Labels = mixedMoment B raw4194step0 raw4194step0Labels := by
      have hz : ∀ j, raw4194 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4194step0 = (fun i j => raw4194 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4194step0 raw4194; decide +kernel
      have hl : raw4194step0Labels = raw4194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4194 raw4194Labels permutation346 hz
    mixedMoment B raw4194step0 raw4194step0Labels = mixedMoment B raw4194step1 raw4194step1Labels := by
      have ha : raw4194step1 = (fun i j => raw4194step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4194step1 raw4194step0; decide +kernel
      have hl : raw4194step1Labels = raw4194step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4194step0 raw4194step0Labels permutation32 permutation7
    mixedMoment B raw4194step1 raw4194step1Labels = mixedMoment B raw4194step2 raw4194step2Labels := by
      have ha : raw4194step2 = -raw4194step1 := by apply Matrix.ext; change ∀ i j, raw4194step2 i j = -(raw4194step1 i j); unfold raw4194step2 raw4194step1; decide +kernel
      have hl : raw4194step2Labels = raw4194step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4194step2 raw4194step2Labels = mixedMoment B raw4194step3 raw4194step3Labels := by
      have ha : raw4194step3 = raw4194step2 := by apply Matrix.ext; unfold raw4194step3 raw4194step2; decide +kernel
      have hl : raw4194step2Labels = labelEmbedding1 ∘ raw4194step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4194step2 raw4194step2Labels raw4194step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw4195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4195Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4195step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw4195step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw4195step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4195 raw4195Labels = mixedMoment B node1615 node1615Labels := by
  calc
    mixedMoment B raw4195 raw4195Labels = mixedMoment B raw4195step0 raw4195step0Labels := by
      have hz : ∀ j, raw4195 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4195step0 = (fun i j => raw4195 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4195step0 raw4195; decide +kernel
      have hl : raw4195step0Labels = raw4195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4195 raw4195Labels permutation346 hz
    mixedMoment B raw4195step0 raw4195step0Labels = mixedMoment B raw4195step1 raw4195step1Labels := by
      have ha : raw4195step1 = (fun i j => raw4195step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4195step1 raw4195step0; decide +kernel
      have hl : raw4195step1Labels = raw4195step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4195step0 raw4195step0Labels permutation137 permutation5
    mixedMoment B raw4195step1 raw4195step1Labels = mixedMoment B raw4195step2 raw4195step2Labels := by
      have ha : raw4195step2 = raw4195step1 := by apply Matrix.ext; unfold raw4195step2 raw4195step1; decide +kernel
      have hl : raw4195step1Labels = labelEmbedding1 ∘ raw4195step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4195step1 raw4195step1Labels raw4195step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1615 node1615Labels := by rfl

def raw4196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4196step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4196step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4196step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw4196step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4196 raw4196Labels = mixedMoment B node1723 node1723Labels := by
  calc
    mixedMoment B raw4196 raw4196Labels = mixedMoment B raw4196step0 raw4196step0Labels := by
      have hz : ∀ j, raw4196 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4196step0 = (fun i j => raw4196 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4196step0 raw4196; decide +kernel
      have hl : raw4196step0Labels = raw4196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4196 raw4196Labels permutation346 hz
    mixedMoment B raw4196step0 raw4196step0Labels = mixedMoment B raw4196step1 raw4196step1Labels := by
      have ha : raw4196step1 = (fun i j => raw4196step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4196step1 raw4196step0; decide +kernel
      have hl : raw4196step1Labels = raw4196step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4196step0 raw4196step0Labels permutation137 permutation5
    mixedMoment B raw4196step1 raw4196step1Labels = mixedMoment B raw4196step2 raw4196step2Labels := by
      have ha : raw4196step2 = raw4196step1 := by apply Matrix.ext; unfold raw4196step2 raw4196step1; decide +kernel
      have hl : raw4196step1Labels = labelEmbedding1 ∘ raw4196step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4196step1 raw4196step1Labels raw4196step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1723 node1723Labels := by rfl

def raw4197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4197Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4197step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4197step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw4197step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4197 raw4197Labels = mixedMoment B node1613 node1613Labels := by
  calc
    mixedMoment B raw4197 raw4197Labels = mixedMoment B raw4197step0 raw4197step0Labels := by
      have ha : raw4197step0 = (fun i j => raw4197 (permutation616 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4197step0 raw4197; decide +kernel
      have hl : raw4197step0Labels = raw4197Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4197 raw4197Labels permutation616 permutation5
    mixedMoment B raw4197step0 raw4197step0Labels = mixedMoment B raw4197step1 raw4197step1Labels := by
      have ha : raw4197step1 = raw4197step0 := by apply Matrix.ext; unfold raw4197step1 raw4197step0; decide +kernel
      have hl : raw4197step0Labels = labelEmbedding1 ∘ raw4197step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4197step0 raw4197step0Labels raw4197step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1613 node1613Labels := by rfl

def raw4198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4198Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4198step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4198step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4198step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4198 raw4198Labels = mixedMoment B node1619 node1619Labels := by
  calc
    mixedMoment B raw4198 raw4198Labels = mixedMoment B raw4198step0 raw4198step0Labels := by
      have hz : ∀ j, raw4198 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4198step0 = (fun i j => raw4198 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4198step0 raw4198; decide +kernel
      have hl : raw4198step0Labels = raw4198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4198 raw4198Labels permutation346 hz
    mixedMoment B raw4198step0 raw4198step0Labels = mixedMoment B raw4198step1 raw4198step1Labels := by
      have ha : raw4198step1 = (fun i j => raw4198step0 (permutation138 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4198step1 raw4198step0; decide +kernel
      have hl : raw4198step1Labels = raw4198step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4198step0 raw4198step0Labels permutation138 permutation5
    mixedMoment B raw4198step1 raw4198step1Labels = mixedMoment B raw4198step2 raw4198step2Labels := by
      have ha : raw4198step2 = raw4198step1 := by apply Matrix.ext; unfold raw4198step2 raw4198step1; decide +kernel
      have hl : raw4198step1Labels = labelEmbedding1 ∘ raw4198step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4198step1 raw4198step1Labels raw4198step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1619 node1619Labels := by rfl

def raw4199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![4, -3, -1]]
def raw4199Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![4, -3, -1]]
def raw4199step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4199step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4199step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw4199step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4199 raw4199Labels = mixedMoment B node1619 node1619Labels := by
  calc
    mixedMoment B raw4199 raw4199Labels = mixedMoment B raw4199step0 raw4199step0Labels := by
      have hz : ∀ j, raw4199 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4199step0 = (fun i j => raw4199 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4199step0 raw4199; decide +kernel
      have hl : raw4199step0Labels = raw4199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4199 raw4199Labels permutation346 hz
    mixedMoment B raw4199step0 raw4199step0Labels = mixedMoment B raw4199step1 raw4199step1Labels := by
      have ha : raw4199step1 = (fun i j => raw4199step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4199step1 raw4199step0; decide +kernel
      have hl : raw4199step1Labels = raw4199step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4199step0 raw4199step0Labels permutation136 permutation5
    mixedMoment B raw4199step1 raw4199step1Labels = mixedMoment B raw4199step2 raw4199step2Labels := by
      have ha : raw4199step2 = raw4199step1 := by apply Matrix.ext; unfold raw4199step2 raw4199step1; decide +kernel
      have hl : raw4199step1Labels = labelEmbedding1 ∘ raw4199step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4199step1 raw4199step1Labels raw4199step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1619 node1619Labels := by rfl

def raw4200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4200step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4200 raw4200Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw4200 raw4200Labels = mixedMoment B raw4200step0 raw4200step0Labels := by
      have hz : ∀ j, raw4200 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4200step0 = (fun i j => raw4200 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4200step0 raw4200; decide +kernel
      have hl : raw4200step0Labels = raw4200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4200 raw4200Labels permutation346 hz
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw4201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw4201step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw4201step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4201 raw4201Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw4201 raw4201Labels = mixedMoment B raw4201step0 raw4201step0Labels := by
      have hz : ∀ j, raw4201 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4201step0 = (fun i j => raw4201 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4201step0 raw4201; decide +kernel
      have hl : raw4201step0Labels = raw4201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4201 raw4201Labels permutation346 hz
    mixedMoment B raw4201step0 raw4201step0Labels = mixedMoment B raw4201step1 raw4201step1Labels := by
      have ha : raw4201step1 = (fun i j => raw4201step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4201step1 raw4201step0; decide +kernel
      have hl : raw4201step1Labels = raw4201step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4201step0 raw4201step0Labels permutation145 permutation2
    mixedMoment B raw4201step1 raw4201step1Labels = mixedMoment B raw4201step2 raw4201step2Labels := by
      have ha : raw4201step2 = -raw4201step1 := by apply Matrix.ext; change ∀ i j, raw4201step2 i j = -(raw4201step1 i j); unfold raw4201step2 raw4201step1; decide +kernel
      have hl : raw4201step2Labels = raw4201step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw4202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4202Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw4202step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4202step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4202step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4202 raw4202Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw4202 raw4202Labels = mixedMoment B raw4202step0 raw4202step0Labels := by
      have ha : raw4202step0 = (fun i j => raw4202 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4202step0 raw4202; decide +kernel
      have hl : raw4202step0Labels = raw4202Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4202 raw4202Labels permutation662 permutation2
    mixedMoment B raw4202step0 raw4202step0Labels = mixedMoment B raw4202step1 raw4202step1Labels := by
      have ha : raw4202step1 = -raw4202step0 := by apply Matrix.ext; change ∀ i j, raw4202step1 i j = -(raw4202step0 i j); unfold raw4202step1 raw4202step0; decide +kernel
      have hl : raw4202step1Labels = raw4202step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3064 node3064Labels := by rfl

def raw4203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4203step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw4203step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw4203step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4203 raw4203Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw4203 raw4203Labels = mixedMoment B raw4203step0 raw4203step0Labels := by
      have hz : ∀ j, raw4203 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4203step0 = (fun i j => raw4203 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4203step0 raw4203; decide +kernel
      have hl : raw4203step0Labels = raw4203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4203 raw4203Labels permutation346 hz
    mixedMoment B raw4203step0 raw4203step0Labels = mixedMoment B raw4203step1 raw4203step1Labels := by
      have ha : raw4203step1 = (fun i j => raw4203step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4203step1 raw4203step0; decide +kernel
      have hl : raw4203step1Labels = raw4203step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4203step0 raw4203step0Labels permutation149 permutation2
    mixedMoment B raw4203step1 raw4203step1Labels = mixedMoment B raw4203step2 raw4203step2Labels := by
      have ha : raw4203step2 = -raw4203step1 := by apply Matrix.ext; change ∀ i j, raw4203step2 i j = -(raw4203step1 i j); unfold raw4203step2 raw4203step1; decide +kernel
      have hl : raw4203step2Labels = raw4203step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw4204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4204Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4204step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw4204step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw4204step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4204 raw4204Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw4204 raw4204Labels = mixedMoment B raw4204step0 raw4204step0Labels := by
      have hz : ∀ j, raw4204 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4204step0 = (fun i j => raw4204 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4204step0 raw4204; decide +kernel
      have hl : raw4204step0Labels = raw4204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4204 raw4204Labels permutation346 hz
    mixedMoment B raw4204step0 raw4204step0Labels = mixedMoment B raw4204step1 raw4204step1Labels := by
      have ha : raw4204step1 = (fun i j => raw4204step0 (permutation143 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4204step1 raw4204step0; decide +kernel
      have hl : raw4204step1Labels = raw4204step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4204step0 raw4204step0Labels permutation143 permutation2
    mixedMoment B raw4204step1 raw4204step1Labels = mixedMoment B raw4204step2 raw4204step2Labels := by
      have ha : raw4204step2 = -raw4204step1 := by apply Matrix.ext; change ∀ i j, raw4204step2 i j = -(raw4204step1 i j); unfold raw4204step2 raw4204step1; decide +kernel
      have hl : raw4204step2Labels = raw4204step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw4205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4205step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4205 raw4205Labels = mixedMoment B node3902 node3902Labels := by
  calc
    mixedMoment B raw4205 raw4205Labels = mixedMoment B raw4205step0 raw4205step0Labels := by
      have hz : ∀ j, raw4205 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4205step0 = (fun i j => raw4205 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4205step0 raw4205; decide +kernel
      have hl : raw4205step0Labels = raw4205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4205 raw4205Labels permutation346 hz
    _ = mixedMoment B node3902 node3902Labels := by rfl

def raw4206 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]
def raw4206Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4206step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw4206step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical4206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4206 raw4206Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw4206 raw4206Labels = mixedMoment B raw4206step0 raw4206step0Labels := by
      have hz : ∀ j, raw4206 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4206step0 = (fun i j => raw4206 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4206step0 raw4206; decide +kernel
      have hl : raw4206step0Labels = raw4206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4206 raw4206Labels permutation346 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw4207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4207step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4207step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw4207step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4207 raw4207Labels = mixedMoment B node1249 node1249Labels := by
  calc
    mixedMoment B raw4207 raw4207Labels = mixedMoment B raw4207step0 raw4207step0Labels := by
      have hz : ∀ j, raw4207 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4207step0 = (fun i j => raw4207 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4207step0 raw4207; decide +kernel
      have hl : raw4207step0Labels = raw4207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4207 raw4207Labels permutation346 hz
    mixedMoment B raw4207step0 raw4207step0Labels = mixedMoment B raw4207step1 raw4207step1Labels := by
      have ha : raw4207step1 = (fun i j => raw4207step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4207step1 raw4207step0; decide +kernel
      have hl : raw4207step1Labels = raw4207step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4207step0 raw4207step0Labels permutation40 permutation2
    _ = mixedMoment B node1249 node1249Labels := by rfl

def raw4208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4208step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4208 raw4208Labels = mixedMoment B node1206 node1206Labels := by
  calc
    mixedMoment B raw4208 raw4208Labels = mixedMoment B raw4208step0 raw4208step0Labels := by
      have ha : raw4208step0 = (fun i j => raw4208 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4208step0 raw4208; decide +kernel
      have hl : raw4208step0Labels = raw4208Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4208 raw4208Labels permutation160 permutation2
    _ = mixedMoment B node1206 node1206Labels := by rfl

def raw4209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4209step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4209step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4209 raw4209Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw4209 raw4209Labels = mixedMoment B raw4209step0 raw4209step0Labels := by
      have hz : ∀ j, raw4209 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4209step0 = (fun i j => raw4209 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4209step0 raw4209; decide +kernel
      have hl : raw4209step0Labels = raw4209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4209 raw4209Labels permutation346 hz
    mixedMoment B raw4209step0 raw4209step0Labels = mixedMoment B raw4209step1 raw4209step1Labels := by
      have ha : raw4209step1 = (fun i j => raw4209step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4209step1 raw4209step0; decide +kernel
      have hl : raw4209step1Labels = raw4209step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4209step0 raw4209step0Labels permutation34 permutation2
    _ = mixedMoment B node1217 node1217Labels := by rfl

def raw4210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4210Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4210step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4210 raw4210Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw4210 raw4210Labels = mixedMoment B raw4210step0 raw4210step0Labels := by
      have hz : ∀ j, raw4210 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4210step0 = (fun i j => raw4210 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4210step0 raw4210; decide +kernel
      have hl : raw4210step0Labels = raw4210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4210 raw4210Labels permutation346 hz
    _ = mixedMoment B node1217 node1217Labels := by rfl

def raw4211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4211Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4211step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4211 raw4211Labels = mixedMoment B node1209 node1209Labels := by
  calc
    mixedMoment B raw4211 raw4211Labels = mixedMoment B raw4211step0 raw4211step0Labels := by
      have hz : ∀ j, raw4211 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4211step0 = (fun i j => raw4211 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4211step0 raw4211; decide +kernel
      have hl : raw4211step0Labels = raw4211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4211 raw4211Labels permutation346 hz
    _ = mixedMoment B node1209 node1209Labels := by rfl

def raw4212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw4212step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4212 raw4212Labels = mixedMoment B node2562 node2562Labels := by
  calc
    mixedMoment B raw4212 raw4212Labels = mixedMoment B raw4212step0 raw4212step0Labels := by
      have ha : raw4212step0 = (fun i j => raw4212 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4212step0 raw4212; decide +kernel
      have hl : raw4212step0Labels = raw4212Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4212 raw4212Labels permutation184 permutation2
    _ = mixedMoment B node2562 node2562Labels := by rfl

def raw4213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw4213step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4213 raw4213Labels = mixedMoment B node2624 node2624Labels := by
  calc
    mixedMoment B raw4213 raw4213Labels = mixedMoment B raw4213step0 raw4213step0Labels := by
      have hz : ∀ j, raw4213 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4213step0 = (fun i j => raw4213 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4213step0 raw4213; decide +kernel
      have hl : raw4213step0Labels = raw4213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4213 raw4213Labels permutation346 hz
    mixedMoment B raw4213step0 raw4213step0Labels = mixedMoment B raw4213step1 raw4213step1Labels := by
      have ha : raw4213step1 = (fun i j => raw4213step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4213step1 raw4213step0; decide +kernel
      have hl : raw4213step1Labels = raw4213step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4213step0 raw4213step0Labels permutation40 permutation2
    _ = mixedMoment B node2624 node2624Labels := by rfl

def raw4214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4214Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4214step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw4214step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4214 raw4214Labels = mixedMoment B node2624 node2624Labels := by
  calc
    mixedMoment B raw4214 raw4214Labels = mixedMoment B raw4214step0 raw4214step0Labels := by
      have hz : ∀ j, raw4214 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4214step0 = (fun i j => raw4214 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4214step0 raw4214; decide +kernel
      have hl : raw4214step0Labels = raw4214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4214 raw4214Labels permutation346 hz
    mixedMoment B raw4214step0 raw4214step0Labels = mixedMoment B raw4214step1 raw4214step1Labels := by
      have ha : raw4214step1 = (fun i j => raw4214step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4214step1 raw4214step0; decide +kernel
      have hl : raw4214step1Labels = raw4214step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4214step0 raw4214step0Labels permutation46 permutation2
    _ = mixedMoment B node2624 node2624Labels := by rfl

def raw4215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4215Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4215step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw4215step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4215 raw4215Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw4215 raw4215Labels = mixedMoment B raw4215step0 raw4215step0Labels := by
      have hz : ∀ j, raw4215 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4215step0 = (fun i j => raw4215 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4215step0 raw4215; decide +kernel
      have hl : raw4215step0Labels = raw4215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4215 raw4215Labels permutation346 hz
    mixedMoment B raw4215step0 raw4215step0Labels = mixedMoment B raw4215step1 raw4215step1Labels := by
      have ha : raw4215step1 = (fun i j => raw4215step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4215step1 raw4215step0; decide +kernel
      have hl : raw4215step1Labels = raw4215step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4215step0 raw4215step0Labels permutation40 permutation2
    _ = mixedMoment B node2751 node2751Labels := by rfl

def raw4216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4216Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4216step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4216 raw4216Labels = mixedMoment B node2470 node2470Labels := by
  calc
    mixedMoment B raw4216 raw4216Labels = mixedMoment B raw4216step0 raw4216step0Labels := by
      have ha : raw4216step0 = (fun i j => raw4216 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4216step0 raw4216; decide +kernel
      have hl : raw4216step0Labels = raw4216Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4216 raw4216Labels permutation160 permutation2
    _ = mixedMoment B node2470 node2470Labels := by rfl

def raw4217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4217Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4217step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4217step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4217 raw4217Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw4217 raw4217Labels = mixedMoment B raw4217step0 raw4217step0Labels := by
      have hz : ∀ j, raw4217 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4217step0 = (fun i j => raw4217 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4217step0 raw4217; decide +kernel
      have hl : raw4217step0Labels = raw4217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4217 raw4217Labels permutation346 hz
    mixedMoment B raw4217step0 raw4217step0Labels = mixedMoment B raw4217step1 raw4217step1Labels := by
      have ha : raw4217step1 = (fun i j => raw4217step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4217step1 raw4217step0; decide +kernel
      have hl : raw4217step1Labels = raw4217step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4217step0 raw4217step0Labels permutation34 permutation2
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw4218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4218 raw4218Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw4218 raw4218Labels = mixedMoment B raw4218step0 raw4218step0Labels := by
      have hz : ∀ j, raw4218 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4218step0 = (fun i j => raw4218 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4218step0 raw4218; decide +kernel
      have hl : raw4218step0Labels = raw4218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4218 raw4218Labels permutation346 hz
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw4219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4219Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![4, -3, -1]]
def raw4219step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw4219step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4219step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw4219step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4219 raw4219Labels = mixedMoment B node1388 node1388Labels := by
  calc
    mixedMoment B raw4219 raw4219Labels = mixedMoment B raw4219step0 raw4219step0Labels := by
      have hz : ∀ j, raw4219 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4219step0 = (fun i j => raw4219 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4219step0 raw4219; decide +kernel
      have hl : raw4219step0Labels = raw4219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4219 raw4219Labels permutation346 hz
    mixedMoment B raw4219step0 raw4219step0Labels = mixedMoment B raw4219step1 raw4219step1Labels := by
      have ha : raw4219step1 = (fun i j => raw4219step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4219step1 raw4219step0; decide +kernel
      have hl : raw4219step1Labels = raw4219step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4219step0 raw4219step0Labels permutation145 permutation2
    mixedMoment B raw4219step1 raw4219step1Labels = mixedMoment B raw4219step2 raw4219step2Labels := by
      have ha : raw4219step2 = -raw4219step1 := by apply Matrix.ext; change ∀ i j, raw4219step2 i j = -(raw4219step1 i j); unfold raw4219step2 raw4219step1; decide +kernel
      have hl : raw4219step2Labels = raw4219step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1388 node1388Labels := by rfl

def raw4220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4220Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4220step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4220 raw4220Labels = mixedMoment B node2610 node2610Labels := by
  calc
    mixedMoment B raw4220 raw4220Labels = mixedMoment B raw4220step0 raw4220step0Labels := by
      have ha : raw4220step0 = (fun i j => raw4220 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4220step0 raw4220; decide +kernel
      have hl : raw4220step0Labels = raw4220Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4220 raw4220Labels permutation202 permutation2
    _ = mixedMoment B node2610 node2610Labels := by rfl

def raw4221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -2, -1]]
def raw4221Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw4221step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4221 raw4221Labels = mixedMoment B node2610 node2610Labels := by
  calc
    mixedMoment B raw4221 raw4221Labels = mixedMoment B raw4221step0 raw4221step0Labels := by
      have ha : raw4221step0 = (fun i j => raw4221 (permutation226 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4221step0 raw4221; decide +kernel
      have hl : raw4221step0Labels = raw4221Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4221 raw4221Labels permutation226 permutation2
    _ = mixedMoment B node2610 node2610Labels := by rfl

def raw4222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw4222Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw4222step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4222 raw4222Labels = mixedMoment B node2709 node2709Labels := by
  calc
    mixedMoment B raw4222 raw4222Labels = mixedMoment B raw4222step0 raw4222step0Labels := by
      have ha : raw4222step0 = (fun i j => raw4222 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4222step0 raw4222; decide +kernel
      have hl : raw4222step0Labels = raw4222Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4222 raw4222Labels permutation160 permutation2
    _ = mixedMoment B node2709 node2709Labels := by rfl

def raw4223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4223Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4223step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw4223step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4223 raw4223Labels = mixedMoment B node2543 node2543Labels := by
  calc
    mixedMoment B raw4223 raw4223Labels = mixedMoment B raw4223step0 raw4223step0Labels := by
      have ha : raw4223step0 = (fun i j => raw4223 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4223step0 raw4223; decide +kernel
      have hl : raw4223step0Labels = raw4223Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4223 raw4223Labels permutation178 permutation2
    _ = mixedMoment B node2543 node2543Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
