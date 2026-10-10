import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw16640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw16640Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw16640step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw16640step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw16640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16640step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw16640step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16640 raw16640Labels = mixedMoment B node3912 node3912Labels := by
  calc
    mixedMoment B raw16640 raw16640Labels = mixedMoment B raw16640step0 raw16640step0Labels := by
      have hz : ∀ j, raw16640 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16640step0 = (fun i j => raw16640 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16640step0 raw16640; decide +kernel
      have hl : raw16640step0Labels = raw16640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16640 raw16640Labels permutation520 hz
    mixedMoment B raw16640step0 raw16640step0Labels = mixedMoment B raw16640step1 raw16640step1Labels := by
      have hz : ∀ j, raw16640step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16640step1 = (fun i j => raw16640step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16640step1 raw16640step0; decide +kernel
      have hl : raw16640step1Labels = raw16640step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16640step0 raw16640step0Labels permutation80 hz
    mixedMoment B raw16640step1 raw16640step1Labels = mixedMoment B raw16640step2 raw16640step2Labels := by
      have ha : raw16640step2 = (fun i j => raw16640step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16640step2 raw16640step1; decide +kernel
      have hl : raw16640step2Labels = raw16640step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16640step1 raw16640step1Labels permutation29 permutation3
    mixedMoment B raw16640step2 raw16640step2Labels = mixedMoment B raw16640step3 raw16640step3Labels := by
      have ha : raw16640step3 = -raw16640step2 := by apply Matrix.ext; change ∀ i j, raw16640step3 i j = -(raw16640step2 i j); unfold raw16640step3 raw16640step2; decide +kernel
      have hl : raw16640step3Labels = raw16640step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3912 node3912Labels := by rfl

def raw16641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16641Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16641step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16641step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16641 raw16641Labels = mixedMoment B node4039 node4039Labels := by
  calc
    mixedMoment B raw16641 raw16641Labels = mixedMoment B raw16641step0 raw16641step0Labels := by
      have hz : ∀ j, raw16641 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16641step0 = (fun i j => raw16641 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16641step0 raw16641; decide +kernel
      have hl : raw16641step0Labels = raw16641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16641 raw16641Labels permutation346 hz
    mixedMoment B raw16641step0 raw16641step0Labels = mixedMoment B raw16641step1 raw16641step1Labels := by
      have ha : raw16641step1 = (fun i j => raw16641step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16641step1 raw16641step0; decide +kernel
      have hl : raw16641step1Labels = raw16641step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16641step0 raw16641step0Labels permutation32 permutation3
    _ = mixedMoment B node4039 node4039Labels := by rfl

def raw16642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16642Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw16642step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16642 raw16642Labels = mixedMoment B node2853 node2853Labels := by
  calc
    mixedMoment B raw16642 raw16642Labels = mixedMoment B raw16642step0 raw16642step0Labels := by
      have ha : raw16642step0 = (fun i j => raw16642 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16642step0 raw16642; decide +kernel
      have hl : raw16642step0Labels = raw16642Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16642 raw16642Labels permutation158 permutation3
    _ = mixedMoment B node2853 node2853Labels := by rfl

def raw16643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw16643step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16643 raw16643Labels = mixedMoment B node3370 node3370Labels := by
  calc
    mixedMoment B raw16643 raw16643Labels = mixedMoment B raw16643step0 raw16643step0Labels := by
      have ha : raw16643step0 = (fun i j => raw16643 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16643step0 raw16643; decide +kernel
      have hl : raw16643step0Labels = raw16643Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16643 raw16643Labels permutation271 permutation3
    _ = mixedMoment B node3370 node3370Labels := by rfl

def raw16644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw16644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16644 raw16644Labels = mixedMoment B node3778 node3778Labels := by
  calc
    mixedMoment B raw16644 raw16644Labels = mixedMoment B raw16644step0 raw16644step0Labels := by
      have ha : raw16644step0 = (fun i j => raw16644 (permutation644 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16644step0 raw16644; decide +kernel
      have hl : raw16644step0Labels = raw16644Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16644 raw16644Labels permutation644 permutation3
    mixedMoment B raw16644step0 raw16644step0Labels = mixedMoment B raw16644step1 raw16644step1Labels := by
      have ha : raw16644step1 = -raw16644step0 := by apply Matrix.ext; change ∀ i j, raw16644step1 i j = -(raw16644step0 i j); unfold raw16644step1 raw16644step0; decide +kernel
      have hl : raw16644step1Labels = raw16644step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3778 node3778Labels := by rfl

def raw16645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw16645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw16645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16645step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16645step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16645 raw16645Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw16645 raw16645Labels = mixedMoment B raw16645step0 raw16645step0Labels := by
      have hz : ∀ j, raw16645 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16645step0 = (fun i j => raw16645 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16645step0 raw16645; decide +kernel
      have hl : raw16645step0Labels = raw16645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16645 raw16645Labels permutation520 hz
    mixedMoment B raw16645step0 raw16645step0Labels = mixedMoment B raw16645step1 raw16645step1Labels := by
      have ha : raw16645step1 = (fun i j => raw16645step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16645step1 raw16645step0; decide +kernel
      have hl : raw16645step1Labels = raw16645step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16645step0 raw16645step0Labels permutation145 permutation3
    mixedMoment B raw16645step1 raw16645step1Labels = mixedMoment B raw16645step2 raw16645step2Labels := by
      have ha : raw16645step2 = -raw16645step1 := by apply Matrix.ext; change ∀ i j, raw16645step2 i j = -(raw16645step1 i j); unfold raw16645step2 raw16645step1; decide +kernel
      have hl : raw16645step2Labels = raw16645step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw16646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw16646step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16646 raw16646Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw16646 raw16646Labels = mixedMoment B raw16646step0 raw16646step0Labels := by
      have ha : raw16646step0 = (fun i j => raw16646 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16646step0 raw16646; decide +kernel
      have hl : raw16646step0Labels = raw16646Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16646 raw16646Labels permutation158 permutation3
    _ = mixedMoment B node4025 node4025Labels := by rfl

def raw16647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw16647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16647 raw16647Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw16647 raw16647Labels = mixedMoment B raw16647step0 raw16647step0Labels := by
      have hz : ∀ j, raw16647 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16647step0 = (fun i j => raw16647 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16647step0 raw16647; decide +kernel
      have hl : raw16647step0Labels = raw16647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16647 raw16647Labels permutation346 hz
    mixedMoment B raw16647step0 raw16647step0Labels = mixedMoment B raw16647step1 raw16647step1Labels := by
      have ha : raw16647step1 = (fun i j => raw16647step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16647step1 raw16647step0; decide +kernel
      have hl : raw16647step1Labels = raw16647step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16647step0 raw16647step0Labels permutation32 permutation3
    _ = mixedMoment B node2881 node2881Labels := by rfl

def raw16648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16648step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw16648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16648 raw16648Labels = mixedMoment B node3391 node3391Labels := by
  calc
    mixedMoment B raw16648 raw16648Labels = mixedMoment B raw16648step0 raw16648step0Labels := by
      have hz : ∀ j, raw16648 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16648step0 = (fun i j => raw16648 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16648step0 raw16648; decide +kernel
      have hl : raw16648step0Labels = raw16648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16648 raw16648Labels permutation346 hz
    mixedMoment B raw16648step0 raw16648step0Labels = mixedMoment B raw16648step1 raw16648step1Labels := by
      have ha : raw16648step1 = (fun i j => raw16648step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16648step1 raw16648step0; decide +kernel
      have hl : raw16648step1Labels = raw16648step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16648step0 raw16648step0Labels permutation56 permutation3
    _ = mixedMoment B node3391 node3391Labels := by rfl

def raw16649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16649step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16649step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16649 raw16649Labels = mixedMoment B node3782 node3782Labels := by
  calc
    mixedMoment B raw16649 raw16649Labels = mixedMoment B raw16649step0 raw16649step0Labels := by
      have ha : raw16649step0 = (fun i j => raw16649 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16649step0 raw16649; decide +kernel
      have hl : raw16649step0Labels = raw16649Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16649 raw16649Labels permutation688 permutation3
    mixedMoment B raw16649step0 raw16649step0Labels = mixedMoment B raw16649step1 raw16649step1Labels := by
      have ha : raw16649step1 = -raw16649step0 := by apply Matrix.ext; change ∀ i j, raw16649step1 i j = -(raw16649step0 i j); unfold raw16649step1 raw16649step0; decide +kernel
      have hl : raw16649step1Labels = raw16649step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3782 node3782Labels := by rfl

def raw16650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw16650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16650step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16650step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16650step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16650step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16650step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16650step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16650 raw16650Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw16650 raw16650Labels = mixedMoment B raw16650step0 raw16650step0Labels := by
      have hz : ∀ j, raw16650 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16650step0 = (fun i j => raw16650 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16650step0 raw16650; decide +kernel
      have hl : raw16650step0Labels = raw16650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16650 raw16650Labels permutation520 hz
    mixedMoment B raw16650step0 raw16650step0Labels = mixedMoment B raw16650step1 raw16650step1Labels := by
      have hz : ∀ j, raw16650step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16650step1 = (fun i j => raw16650step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16650step1 raw16650step0; decide +kernel
      have hl : raw16650step1Labels = raw16650step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16650step0 raw16650step0Labels permutation80 hz
    mixedMoment B raw16650step1 raw16650step1Labels = mixedMoment B raw16650step2 raw16650step2Labels := by
      have ha : raw16650step2 = (fun i j => raw16650step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16650step2 raw16650step1; decide +kernel
      have hl : raw16650step2Labels = raw16650step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16650step1 raw16650step1Labels permutation31 permutation3
    mixedMoment B raw16650step2 raw16650step2Labels = mixedMoment B raw16650step3 raw16650step3Labels := by
      have ha : raw16650step3 = -raw16650step2 := by apply Matrix.ext; change ∀ i j, raw16650step3 i j = -(raw16650step2 i j); unfold raw16650step3 raw16650step2; decide +kernel
      have hl : raw16650step3Labels = raw16650step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3862 node3862Labels := by rfl

def raw16651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16651Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16651step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16651step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16651 raw16651Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw16651 raw16651Labels = mixedMoment B raw16651step0 raw16651step0Labels := by
      have hz : ∀ j, raw16651 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16651step0 = (fun i j => raw16651 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16651step0 raw16651; decide +kernel
      have hl : raw16651step0Labels = raw16651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16651 raw16651Labels permutation346 hz
    mixedMoment B raw16651step0 raw16651step0Labels = mixedMoment B raw16651step1 raw16651step1Labels := by
      have ha : raw16651step1 = (fun i j => raw16651step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16651step1 raw16651step0; decide +kernel
      have hl : raw16651step1Labels = raw16651step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16651step0 raw16651step0Labels permutation32 permutation3
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw16652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16652Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16652step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw16652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16652 raw16652Labels = mixedMoment B node2856 node2856Labels := by
  calc
    mixedMoment B raw16652 raw16652Labels = mixedMoment B raw16652step0 raw16652step0Labels := by
      have hz : ∀ j, raw16652 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16652step0 = (fun i j => raw16652 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16652step0 raw16652; decide +kernel
      have hl : raw16652step0Labels = raw16652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16652 raw16652Labels permutation346 hz
    mixedMoment B raw16652step0 raw16652step0Labels = mixedMoment B raw16652step1 raw16652step1Labels := by
      have ha : raw16652step1 = (fun i j => raw16652step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16652step1 raw16652step0; decide +kernel
      have hl : raw16652step1Labels = raw16652step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16652step0 raw16652step0Labels permutation32 permutation3
    _ = mixedMoment B node2856 node2856Labels := by rfl

def raw16653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16653Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16653step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw16653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16653 raw16653Labels = mixedMoment B node3372 node3372Labels := by
  calc
    mixedMoment B raw16653 raw16653Labels = mixedMoment B raw16653step0 raw16653step0Labels := by
      have hz : ∀ j, raw16653 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16653step0 = (fun i j => raw16653 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16653step0 raw16653; decide +kernel
      have hl : raw16653step0Labels = raw16653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16653 raw16653Labels permutation346 hz
    mixedMoment B raw16653step0 raw16653step0Labels = mixedMoment B raw16653step1 raw16653step1Labels := by
      have ha : raw16653step1 = (fun i j => raw16653step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16653step1 raw16653step0; decide +kernel
      have hl : raw16653step1Labels = raw16653step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16653step0 raw16653step0Labels permutation56 permutation3
    _ = mixedMoment B node3372 node3372Labels := by rfl

def raw16654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16654Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16654step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16654 raw16654Labels = mixedMoment B node3653 node3653Labels := by
  calc
    mixedMoment B raw16654 raw16654Labels = mixedMoment B raw16654step0 raw16654step0Labels := by
      have ha : raw16654step0 = (fun i j => raw16654 (permutation589 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16654step0 raw16654; decide +kernel
      have hl : raw16654step0Labels = raw16654Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16654 raw16654Labels permutation589 permutation3
    mixedMoment B raw16654step0 raw16654step0Labels = mixedMoment B raw16654step1 raw16654step1Labels := by
      have ha : raw16654step1 = -raw16654step0 := by apply Matrix.ext; change ∀ i j, raw16654step1 i j = -(raw16654step0 i j); unfold raw16654step1 raw16654step0; decide +kernel
      have hl : raw16654step1Labels = raw16654step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3653 node3653Labels := by rfl

def raw16655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16655Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -2, 0]]
def raw16655step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw16655step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16655step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16655step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16655 raw16655Labels = mixedMoment B node3666 node3666Labels := by
  calc
    mixedMoment B raw16655 raw16655Labels = mixedMoment B raw16655step0 raw16655step0Labels := by
      have hz : ∀ j, raw16655 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16655step0 = (fun i j => raw16655 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16655step0 raw16655; decide +kernel
      have hl : raw16655step0Labels = raw16655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16655 raw16655Labels permutation346 hz
    mixedMoment B raw16655step0 raw16655step0Labels = mixedMoment B raw16655step1 raw16655step1Labels := by
      have ha : raw16655step1 = (fun i j => raw16655step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16655step1 raw16655step0; decide +kernel
      have hl : raw16655step1Labels = raw16655step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16655step0 raw16655step0Labels permutation125 permutation3
    mixedMoment B raw16655step1 raw16655step1Labels = mixedMoment B raw16655step2 raw16655step2Labels := by
      have ha : raw16655step2 = -raw16655step1 := by apply Matrix.ext; change ∀ i j, raw16655step2 i j = -(raw16655step1 i j); unfold raw16655step2 raw16655step1; decide +kernel
      have hl : raw16655step2Labels = raw16655step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3666 node3666Labels := by rfl

def raw16656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw16656Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw16656step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16656step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16656step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16656step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16656 raw16656Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw16656 raw16656Labels = mixedMoment B raw16656step0 raw16656step0Labels := by
      have hz : ∀ j, raw16656 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16656step0 = (fun i j => raw16656 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16656step0 raw16656; decide +kernel
      have hl : raw16656step0Labels = raw16656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16656 raw16656Labels permutation346 hz
    mixedMoment B raw16656step0 raw16656step0Labels = mixedMoment B raw16656step1 raw16656step1Labels := by
      have ha : raw16656step1 = (fun i j => raw16656step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16656step1 raw16656step0; decide +kernel
      have hl : raw16656step1Labels = raw16656step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16656step0 raw16656step0Labels permutation127 permutation3
    mixedMoment B raw16656step1 raw16656step1Labels = mixedMoment B raw16656step2 raw16656step2Labels := by
      have ha : raw16656step2 = -raw16656step1 := by apply Matrix.ext; change ∀ i j, raw16656step2 i j = -(raw16656step1 i j); unfold raw16656step2 raw16656step1; decide +kernel
      have hl : raw16656step2Labels = raw16656step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw16657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16657Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16657step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw16657step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw16657step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16657 raw16657Labels = mixedMoment B node1915 node1915Labels := by
  calc
    mixedMoment B raw16657 raw16657Labels = mixedMoment B raw16657step0 raw16657step0Labels := by
      have hz : ∀ j, raw16657 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16657step0 = (fun i j => raw16657 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16657step0 raw16657; decide +kernel
      have hl : raw16657step0Labels = raw16657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16657 raw16657Labels permutation346 hz
    mixedMoment B raw16657step0 raw16657step0Labels = mixedMoment B raw16657step1 raw16657step1Labels := by
      have ha : raw16657step1 = (fun i j => raw16657step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16657step1 raw16657step0; decide +kernel
      have hl : raw16657step1Labels = raw16657step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16657step0 raw16657step0Labels permutation151 permutation3
    mixedMoment B raw16657step1 raw16657step1Labels = mixedMoment B raw16657step2 raw16657step2Labels := by
      have ha : raw16657step2 = -raw16657step1 := by apply Matrix.ext; change ∀ i j, raw16657step2 i j = -(raw16657step1 i j); unfold raw16657step2 raw16657step1; decide +kernel
      have hl : raw16657step2Labels = raw16657step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1915 node1915Labels := by rfl

def raw16658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16658Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16658step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw16658step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16658step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw16658step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16658 raw16658Labels = mixedMoment B node1917 node1917Labels := by
  calc
    mixedMoment B raw16658 raw16658Labels = mixedMoment B raw16658step0 raw16658step0Labels := by
      have hz : ∀ j, raw16658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16658step0 = (fun i j => raw16658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16658step0 raw16658; decide +kernel
      have hl : raw16658step0Labels = raw16658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16658 raw16658Labels permutation346 hz
    mixedMoment B raw16658step0 raw16658step0Labels = mixedMoment B raw16658step1 raw16658step1Labels := by
      have ha : raw16658step1 = (fun i j => raw16658step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16658step1 raw16658step0; decide +kernel
      have hl : raw16658step1Labels = raw16658step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16658step0 raw16658step0Labels permutation150 permutation3
    mixedMoment B raw16658step1 raw16658step1Labels = mixedMoment B raw16658step2 raw16658step2Labels := by
      have ha : raw16658step2 = -raw16658step1 := by apply Matrix.ext; change ∀ i j, raw16658step2 i j = -(raw16658step1 i j); unfold raw16658step2 raw16658step1; decide +kernel
      have hl : raw16658step2Labels = raw16658step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1917 node1917Labels := by rfl

def raw16659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16659Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16659step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16659step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16659step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16659 raw16659Labels = mixedMoment B node1913 node1913Labels := by
  calc
    mixedMoment B raw16659 raw16659Labels = mixedMoment B raw16659step0 raw16659step0Labels := by
      have ha : raw16659step0 = (fun i j => raw16659 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16659step0 raw16659; decide +kernel
      have hl : raw16659step0Labels = raw16659Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16659 raw16659Labels permutation688 permutation3
    mixedMoment B raw16659step0 raw16659step0Labels = mixedMoment B raw16659step1 raw16659step1Labels := by
      have ha : raw16659step1 = -raw16659step0 := by apply Matrix.ext; change ∀ i j, raw16659step1 i j = -(raw16659step0 i j); unfold raw16659step1 raw16659step0; decide +kernel
      have hl : raw16659step1Labels = raw16659step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1913 node1913Labels := by rfl

def raw16660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16660Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -3, 0]]
def raw16660step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw16660step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16660step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16660 raw16660Labels = mixedMoment B node1949 node1949Labels := by
  calc
    mixedMoment B raw16660 raw16660Labels = mixedMoment B raw16660step0 raw16660step0Labels := by
      have hz : ∀ j, raw16660 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16660step0 = (fun i j => raw16660 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16660step0 raw16660; decide +kernel
      have hl : raw16660step0Labels = raw16660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16660 raw16660Labels permutation346 hz
    mixedMoment B raw16660step0 raw16660step0Labels = mixedMoment B raw16660step1 raw16660step1Labels := by
      have ha : raw16660step1 = (fun i j => raw16660step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16660step1 raw16660step0; decide +kernel
      have hl : raw16660step1Labels = raw16660step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16660step0 raw16660step0Labels permutation149 permutation3
    mixedMoment B raw16660step1 raw16660step1Labels = mixedMoment B raw16660step2 raw16660step2Labels := by
      have ha : raw16660step2 = -raw16660step1 := by apply Matrix.ext; change ∀ i j, raw16660step2 i j = -(raw16660step1 i j); unfold raw16660step2 raw16660step1; decide +kernel
      have hl : raw16660step2Labels = raw16660step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1949 node1949Labels := by rfl

def raw16661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw16661Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0]]
def raw16661step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16661step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw16661step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16661step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16661step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16661step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16661step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16661 raw16661Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw16661 raw16661Labels = mixedMoment B raw16661step0 raw16661step0Labels := by
      have hz : ∀ j, raw16661 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16661step0 = (fun i j => raw16661 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16661step0 raw16661; decide +kernel
      have hl : raw16661step0Labels = raw16661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16661 raw16661Labels permutation520 hz
    mixedMoment B raw16661step0 raw16661step0Labels = mixedMoment B raw16661step1 raw16661step1Labels := by
      have hz : ∀ j, raw16661step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16661step1 = (fun i j => raw16661step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16661step1 raw16661step0; decide +kernel
      have hl : raw16661step1Labels = raw16661step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16661step0 raw16661step0Labels permutation80 hz
    mixedMoment B raw16661step1 raw16661step1Labels = mixedMoment B raw16661step2 raw16661step2Labels := by
      have ha : raw16661step2 = (fun i j => raw16661step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16661step2 raw16661step1; decide +kernel
      have hl : raw16661step2Labels = raw16661step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16661step1 raw16661step1Labels permutation31 permutation3
    mixedMoment B raw16661step2 raw16661step2Labels = mixedMoment B raw16661step3 raw16661step3Labels := by
      have ha : raw16661step3 = -raw16661step2 := by apply Matrix.ext; change ∀ i j, raw16661step3 i j = -(raw16661step2 i j); unfold raw16661step3 raw16661step2; decide +kernel
      have hl : raw16661step3Labels = raw16661step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw16662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw16662step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw16662step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16662 raw16662Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw16662 raw16662Labels = mixedMoment B raw16662step0 raw16662step0Labels := by
      have hz : ∀ j, raw16662 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16662step0 = (fun i j => raw16662 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16662step0 raw16662; decide +kernel
      have hl : raw16662step0Labels = raw16662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16662 raw16662Labels permutation346 hz
    mixedMoment B raw16662step0 raw16662step0Labels = mixedMoment B raw16662step1 raw16662step1Labels := by
      have ha : raw16662step1 = (fun i j => raw16662step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16662step1 raw16662step0; decide +kernel
      have hl : raw16662step1Labels = raw16662step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16662step0 raw16662step0Labels permutation150 permutation2
    mixedMoment B raw16662step1 raw16662step1Labels = mixedMoment B raw16662step2 raw16662step2Labels := by
      have ha : raw16662step2 = -raw16662step1 := by apply Matrix.ext; change ∀ i j, raw16662step2 i j = -(raw16662step1 i j); unfold raw16662step2 raw16662step1; decide +kernel
      have hl : raw16662step2Labels = raw16662step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5409 node5409Labels := by rfl

def raw16663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16663step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16663step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16663step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16663 raw16663Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw16663 raw16663Labels = mixedMoment B raw16663step0 raw16663step0Labels := by
      have ha : raw16663step0 = (fun i j => raw16663 (permutation668 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16663step0 raw16663; decide +kernel
      have hl : raw16663step0Labels = raw16663Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16663 raw16663Labels permutation668 permutation7
    mixedMoment B raw16663step0 raw16663step0Labels = mixedMoment B raw16663step1 raw16663step1Labels := by
      have ha : raw16663step1 = raw16663step0 := by apply Matrix.ext; unfold raw16663step1 raw16663step0; decide +kernel
      have hl : raw16663step0Labels = labelEmbedding10 ∘ raw16663step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16663step0 raw16663step0Labels raw16663step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw16664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16664step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16664step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16664 raw16664Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw16664 raw16664Labels = mixedMoment B raw16664step0 raw16664step0Labels := by
      have hz : ∀ j, raw16664 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16664step0 = (fun i j => raw16664 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16664step0 raw16664; decide +kernel
      have hl : raw16664step0Labels = raw16664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16664 raw16664Labels permutation346 hz
    mixedMoment B raw16664step0 raw16664step0Labels = mixedMoment B raw16664step1 raw16664step1Labels := by
      have ha : raw16664step1 = (fun i j => raw16664step0 (permutation147 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16664step1 raw16664step0; decide +kernel
      have hl : raw16664step1Labels = raw16664step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16664step0 raw16664step0Labels permutation147 permutation7
    mixedMoment B raw16664step1 raw16664step1Labels = mixedMoment B raw16664step2 raw16664step2Labels := by
      have ha : raw16664step2 = raw16664step1 := by apply Matrix.ext; unfold raw16664step2 raw16664step1; decide +kernel
      have hl : raw16664step1Labels = labelEmbedding10 ∘ raw16664step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16664step1 raw16664step1Labels raw16664step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw16665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16665step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16665step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16665 raw16665Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw16665 raw16665Labels = mixedMoment B raw16665step0 raw16665step0Labels := by
      have hz : ∀ j, raw16665 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16665step0 = (fun i j => raw16665 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16665step0 raw16665; decide +kernel
      have hl : raw16665step0Labels = raw16665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16665 raw16665Labels permutation346 hz
    mixedMoment B raw16665step0 raw16665step0Labels = mixedMoment B raw16665step1 raw16665step1Labels := by
      have ha : raw16665step1 = (fun i j => raw16665step0 (permutation147 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16665step1 raw16665step0; decide +kernel
      have hl : raw16665step1Labels = raw16665step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16665step0 raw16665step0Labels permutation147 permutation7
    mixedMoment B raw16665step1 raw16665step1Labels = mixedMoment B raw16665step2 raw16665step2Labels := by
      have ha : raw16665step2 = raw16665step1 := by apply Matrix.ext; unfold raw16665step2 raw16665step1; decide +kernel
      have hl : raw16665step1Labels = labelEmbedding10 ∘ raw16665step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16665step1 raw16665step1Labels raw16665step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw16666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw16666step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16666step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16666step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw16666step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16666step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16666 raw16666Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw16666 raw16666Labels = mixedMoment B raw16666step0 raw16666step0Labels := by
      have hz : ∀ j, raw16666 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16666step0 = (fun i j => raw16666 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16666step0 raw16666; decide +kernel
      have hl : raw16666step0Labels = raw16666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16666 raw16666Labels permutation346 hz
    mixedMoment B raw16666step0 raw16666step0Labels = mixedMoment B raw16666step1 raw16666step1Labels := by
      have ha : raw16666step1 = (fun i j => raw16666step0 (permutation62 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16666step1 raw16666step0; decide +kernel
      have hl : raw16666step1Labels = raw16666step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16666step0 raw16666step0Labels permutation62 permutation6
    mixedMoment B raw16666step1 raw16666step1Labels = mixedMoment B raw16666step2 raw16666step2Labels := by
      have ha : raw16666step2 = -raw16666step1 := by apply Matrix.ext; change ∀ i j, raw16666step2 i j = -(raw16666step1 i j); unfold raw16666step2 raw16666step1; decide +kernel
      have hl : raw16666step2Labels = raw16666step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16666step2 raw16666step2Labels = mixedMoment B raw16666step3 raw16666step3Labels := by
      have ha : raw16666step3 = raw16666step2 := by apply Matrix.ext; unfold raw16666step3 raw16666step2; decide +kernel
      have hl : raw16666step2Labels = labelEmbedding9 ∘ raw16666step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16666step2 raw16666step2Labels raw16666step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw16667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16667step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16667step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16667step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16667 raw16667Labels = mixedMoment B node4891 node4891Labels := by
  calc
    mixedMoment B raw16667 raw16667Labels = mixedMoment B raw16667step0 raw16667step0Labels := by
      have hz : ∀ j, raw16667 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16667step0 = (fun i j => raw16667 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16667step0 raw16667; decide +kernel
      have hl : raw16667step0Labels = raw16667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16667 raw16667Labels permutation346 hz
    mixedMoment B raw16667step0 raw16667step0Labels = mixedMoment B raw16667step1 raw16667step1Labels := by
      have ha : raw16667step1 = (fun i j => raw16667step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16667step1 raw16667step0; decide +kernel
      have hl : raw16667step1Labels = raw16667step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16667step0 raw16667step0Labels permutation38 permutation3
    mixedMoment B raw16667step1 raw16667step1Labels = mixedMoment B raw16667step2 raw16667step2Labels := by
      have ha : raw16667step2 = raw16667step1 := by apply Matrix.ext; unfold raw16667step2 raw16667step1; decide +kernel
      have hl : raw16667step1Labels = labelEmbedding6 ∘ raw16667step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16667step1 raw16667step1Labels raw16667step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4891 node4891Labels := by rfl

def raw16668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16668step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw16668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16668step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16668 raw16668Labels = mixedMoment B node5407 node5407Labels := by
  calc
    mixedMoment B raw16668 raw16668Labels = mixedMoment B raw16668step0 raw16668step0Labels := by
      have ha : raw16668step0 = (fun i j => raw16668 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16668step0 raw16668; decide +kernel
      have hl : raw16668step0Labels = raw16668Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16668 raw16668Labels permutation686 permutation2
    mixedMoment B raw16668step0 raw16668step0Labels = mixedMoment B raw16668step1 raw16668step1Labels := by
      have ha : raw16668step1 = -raw16668step0 := by apply Matrix.ext; change ∀ i j, raw16668step1 i j = -(raw16668step0 i j); unfold raw16668step1 raw16668step0; decide +kernel
      have hl : raw16668step1Labels = raw16668step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5407 node5407Labels := by rfl

def raw16669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw16669step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw16669step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16669 raw16669Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw16669 raw16669Labels = mixedMoment B raw16669step0 raw16669step0Labels := by
      have hz : ∀ j, raw16669 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16669step0 = (fun i j => raw16669 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16669step0 raw16669; decide +kernel
      have hl : raw16669step0Labels = raw16669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16669 raw16669Labels permutation346 hz
    mixedMoment B raw16669step0 raw16669step0Labels = mixedMoment B raw16669step1 raw16669step1Labels := by
      have ha : raw16669step1 = (fun i j => raw16669step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16669step1 raw16669step0; decide +kernel
      have hl : raw16669step1Labels = raw16669step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16669step0 raw16669step0Labels permutation149 permutation2
    mixedMoment B raw16669step1 raw16669step1Labels = mixedMoment B raw16669step2 raw16669step2Labels := by
      have ha : raw16669step2 = -raw16669step1 := by apply Matrix.ext; change ∀ i j, raw16669step2 i j = -(raw16669step1 i j); unfold raw16669step2 raw16669step1; decide +kernel
      have hl : raw16669step2Labels = raw16669step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw16670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw16670step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw16670step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16670 raw16670Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw16670 raw16670Labels = mixedMoment B raw16670step0 raw16670step0Labels := by
      have hz : ∀ j, raw16670 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16670step0 = (fun i j => raw16670 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16670step0 raw16670; decide +kernel
      have hl : raw16670step0Labels = raw16670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16670 raw16670Labels permutation346 hz
    mixedMoment B raw16670step0 raw16670step0Labels = mixedMoment B raw16670step1 raw16670step1Labels := by
      have ha : raw16670step1 = (fun i j => raw16670step0 (permutation67 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16670step1 raw16670step0; decide +kernel
      have hl : raw16670step1Labels = raw16670step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16670step0 raw16670step0Labels permutation67 permutation4
    mixedMoment B raw16670step1 raw16670step1Labels = mixedMoment B raw16670step2 raw16670step2Labels := by
      have ha : raw16670step2 = raw16670step1 := by apply Matrix.ext; unfold raw16670step2 raw16670step1; decide +kernel
      have hl : raw16670step1Labels = labelEmbedding7 ∘ raw16670step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16670step1 raw16670step1Labels raw16670step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw16671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16671step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16671step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16671step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16671 raw16671Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw16671 raw16671Labels = mixedMoment B raw16671step0 raw16671step0Labels := by
      have hz : ∀ j, raw16671 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16671step0 = (fun i j => raw16671 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16671step0 raw16671; decide +kernel
      have hl : raw16671step0Labels = raw16671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16671 raw16671Labels permutation346 hz
    mixedMoment B raw16671step0 raw16671step0Labels = mixedMoment B raw16671step1 raw16671step1Labels := by
      have ha : raw16671step1 = (fun i j => raw16671step0 (permutation65 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16671step1 raw16671step0; decide +kernel
      have hl : raw16671step1Labels = raw16671step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16671step0 raw16671step0Labels permutation65 permutation4
    mixedMoment B raw16671step1 raw16671step1Labels = mixedMoment B raw16671step2 raw16671step2Labels := by
      have ha : raw16671step2 = raw16671step1 := by apply Matrix.ext; unfold raw16671step2 raw16671step1; decide +kernel
      have hl : raw16671step1Labels = labelEmbedding7 ∘ raw16671step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16671step1 raw16671step1Labels raw16671step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw16672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16672step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16672 raw16672Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw16672 raw16672Labels = mixedMoment B raw16672step0 raw16672step0Labels := by
      have ha : raw16672step0 = (fun i j => raw16672 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16672step0 raw16672; decide +kernel
      have hl : raw16672step0Labels = raw16672Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16672 raw16672Labels permutation160 permutation3
    mixedMoment B raw16672step0 raw16672step0Labels = mixedMoment B raw16672step1 raw16672step1Labels := by
      have ha : raw16672step1 = raw16672step0 := by apply Matrix.ext; unfold raw16672step1 raw16672step0; decide +kernel
      have hl : raw16672step0Labels = labelEmbedding6 ∘ raw16672step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16672step0 raw16672step0Labels raw16672step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw16673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw16673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16673 raw16673Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw16673 raw16673Labels = mixedMoment B raw16673step0 raw16673step0Labels := by
      have ha : raw16673step0 = (fun i j => raw16673 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16673step0 raw16673; decide +kernel
      have hl : raw16673step0Labels = raw16673Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16673 raw16673Labels permutation271 permutation2
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw16674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16674step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16674step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16674 raw16674Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw16674 raw16674Labels = mixedMoment B raw16674step0 raw16674step0Labels := by
      have ha : raw16674step0 = (fun i j => raw16674 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16674step0 raw16674; decide +kernel
      have hl : raw16674step0Labels = raw16674Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16674 raw16674Labels permutation682 permutation2
    mixedMoment B raw16674step0 raw16674step0Labels = mixedMoment B raw16674step1 raw16674step1Labels := by
      have ha : raw16674step1 = -raw16674step0 := by apply Matrix.ext; change ∀ i j, raw16674step1 i j = -(raw16674step0 i j); unfold raw16674step1 raw16674step0; decide +kernel
      have hl : raw16674step1Labels = raw16674step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw16675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16675step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16675step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16675 raw16675Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw16675 raw16675Labels = mixedMoment B raw16675step0 raw16675step0Labels := by
      have ha : raw16675step0 = (fun i j => raw16675 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16675step0 raw16675; decide +kernel
      have hl : raw16675step0Labels = raw16675Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16675 raw16675Labels permutation646 permutation2
    mixedMoment B raw16675step0 raw16675step0Labels = mixedMoment B raw16675step1 raw16675step1Labels := by
      have ha : raw16675step1 = -raw16675step0 := by apply Matrix.ext; change ∀ i j, raw16675step1 i j = -(raw16675step0 i j); unfold raw16675step1 raw16675step0; decide +kernel
      have hl : raw16675step1Labels = raw16675step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw16676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16676step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16676step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16676 raw16676Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw16676 raw16676Labels = mixedMoment B raw16676step0 raw16676step0Labels := by
      have ha : raw16676step0 = (fun i j => raw16676 (permutation163 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16676step0 raw16676; decide +kernel
      have hl : raw16676step0Labels = raw16676Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16676 raw16676Labels permutation163 permutation3
    mixedMoment B raw16676step0 raw16676step0Labels = mixedMoment B raw16676step1 raw16676step1Labels := by
      have ha : raw16676step1 = raw16676step0 := by apply Matrix.ext; unfold raw16676step1 raw16676step0; decide +kernel
      have hl : raw16676step0Labels = labelEmbedding6 ∘ raw16676step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16676step0 raw16676step0Labels raw16676step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw16677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16677step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16677step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16677 raw16677Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw16677 raw16677Labels = mixedMoment B raw16677step0 raw16677step0Labels := by
      have hz : ∀ j, raw16677 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16677step0 = (fun i j => raw16677 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16677step0 raw16677; decide +kernel
      have hl : raw16677step0Labels = raw16677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16677 raw16677Labels permutation346 hz
    mixedMoment B raw16677step0 raw16677step0Labels = mixedMoment B raw16677step1 raw16677step1Labels := by
      have ha : raw16677step1 = (fun i j => raw16677step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16677step1 raw16677step0; decide +kernel
      have hl : raw16677step1Labels = raw16677step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16677step0 raw16677step0Labels permutation34 permutation3
    mixedMoment B raw16677step1 raw16677step1Labels = mixedMoment B raw16677step2 raw16677step2Labels := by
      have ha : raw16677step2 = raw16677step1 := by apply Matrix.ext; unfold raw16677step2 raw16677step1; decide +kernel
      have hl : raw16677step1Labels = labelEmbedding6 ∘ raw16677step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16677step1 raw16677step1Labels raw16677step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4867 node4867Labels := by rfl

def raw16678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16678step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16678 raw16678Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw16678 raw16678Labels = mixedMoment B raw16678step0 raw16678step0Labels := by
      have hz : ∀ j, raw16678 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16678step0 = (fun i j => raw16678 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16678step0 raw16678; decide +kernel
      have hl : raw16678step0Labels = raw16678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16678 raw16678Labels permutation346 hz
    mixedMoment B raw16678step0 raw16678step0Labels = mixedMoment B raw16678step1 raw16678step1Labels := by
      have ha : raw16678step1 = (fun i j => raw16678step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16678step1 raw16678step0; decide +kernel
      have hl : raw16678step1Labels = raw16678step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16678step0 raw16678step0Labels permutation56 permutation2
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw16679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16679step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16679step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16679 raw16679Labels = mixedMoment B node5402 node5402Labels := by
  calc
    mixedMoment B raw16679 raw16679Labels = mixedMoment B raw16679step0 raw16679step0Labels := by
      have ha : raw16679step0 = (fun i j => raw16679 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16679step0 raw16679; decide +kernel
      have hl : raw16679step0Labels = raw16679Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16679 raw16679Labels permutation688 permutation2
    mixedMoment B raw16679step0 raw16679step0Labels = mixedMoment B raw16679step1 raw16679step1Labels := by
      have ha : raw16679step1 = -raw16679step0 := by apply Matrix.ext; change ∀ i j, raw16679step1 i j = -(raw16679step0 i j); unfold raw16679step1 raw16679step0; decide +kernel
      have hl : raw16679step1Labels = raw16679step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5402 node5402Labels := by rfl

def raw16680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw16680step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16680step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16680step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16680step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16680 raw16680Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw16680 raw16680Labels = mixedMoment B raw16680step0 raw16680step0Labels := by
      have hz : ∀ j, raw16680 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16680step0 = (fun i j => raw16680 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16680step0 raw16680; decide +kernel
      have hl : raw16680step0Labels = raw16680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16680 raw16680Labels permutation346 hz
    mixedMoment B raw16680step0 raw16680step0Labels = mixedMoment B raw16680step1 raw16680step1Labels := by
      have ha : raw16680step1 = (fun i j => raw16680step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16680step1 raw16680step0; decide +kernel
      have hl : raw16680step1Labels = raw16680step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16680step0 raw16680step0Labels permutation48 permutation5
    mixedMoment B raw16680step1 raw16680step1Labels = mixedMoment B raw16680step2 raw16680step2Labels := by
      have ha : raw16680step2 = -raw16680step1 := by apply Matrix.ext; change ∀ i j, raw16680step2 i j = -(raw16680step1 i j); unfold raw16680step2 raw16680step1; decide +kernel
      have hl : raw16680step2Labels = raw16680step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16680step2 raw16680step2Labels = mixedMoment B raw16680step3 raw16680step3Labels := by
      have ha : raw16680step3 = raw16680step2 := by apply Matrix.ext; unfold raw16680step3 raw16680step2; decide +kernel
      have hl : raw16680step2Labels = labelEmbedding8 ∘ raw16680step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16680step2 raw16680step2Labels raw16680step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5436 node5436Labels := by rfl

def raw16681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16681step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16681step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16681step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16681step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16681 raw16681Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw16681 raw16681Labels = mixedMoment B raw16681step0 raw16681step0Labels := by
      have hz : ∀ j, raw16681 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16681step0 = (fun i j => raw16681 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16681step0 raw16681; decide +kernel
      have hl : raw16681step0Labels = raw16681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16681 raw16681Labels permutation346 hz
    mixedMoment B raw16681step0 raw16681step0Labels = mixedMoment B raw16681step1 raw16681step1Labels := by
      have ha : raw16681step1 = (fun i j => raw16681step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16681step1 raw16681step0; decide +kernel
      have hl : raw16681step1Labels = raw16681step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16681step0 raw16681step0Labels permutation54 permutation5
    mixedMoment B raw16681step1 raw16681step1Labels = mixedMoment B raw16681step2 raw16681step2Labels := by
      have ha : raw16681step2 = -raw16681step1 := by apply Matrix.ext; change ∀ i j, raw16681step2 i j = -(raw16681step1 i j); unfold raw16681step2 raw16681step1; decide +kernel
      have hl : raw16681step2Labels = raw16681step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16681step2 raw16681step2Labels = mixedMoment B raw16681step3 raw16681step3Labels := by
      have ha : raw16681step3 = raw16681step2 := by apply Matrix.ext; unfold raw16681step3 raw16681step2; decide +kernel
      have hl : raw16681step2Labels = labelEmbedding8 ∘ raw16681step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16681step2 raw16681step2Labels raw16681step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw16682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16682step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16682 raw16682Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw16682 raw16682Labels = mixedMoment B raw16682step0 raw16682step0Labels := by
      have hz : ∀ j, raw16682 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16682step0 = (fun i j => raw16682 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16682step0 raw16682; decide +kernel
      have hl : raw16682step0Labels = raw16682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16682 raw16682Labels permutation346 hz
    mixedMoment B raw16682step0 raw16682step0Labels = mixedMoment B raw16682step1 raw16682step1Labels := by
      have ha : raw16682step1 = (fun i j => raw16682step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16682step1 raw16682step0; decide +kernel
      have hl : raw16682step1Labels = raw16682step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16682step0 raw16682step0Labels permutation33 permutation3
    mixedMoment B raw16682step1 raw16682step1Labels = mixedMoment B raw16682step2 raw16682step2Labels := by
      have ha : raw16682step2 = raw16682step1 := by apply Matrix.ext; unfold raw16682step2 raw16682step1; decide +kernel
      have hl : raw16682step1Labels = labelEmbedding6 ∘ raw16682step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16682step1 raw16682step1Labels raw16682step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4856 node4856Labels := by rfl

def raw16683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw16683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16683step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16683step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16683 raw16683Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw16683 raw16683Labels = mixedMoment B raw16683step0 raw16683step0Labels := by
      have hz : ∀ j, raw16683 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16683step0 = (fun i j => raw16683 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16683step0 raw16683; decide +kernel
      have hl : raw16683step0Labels = raw16683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16683 raw16683Labels permutation346 hz
    mixedMoment B raw16683step0 raw16683step0Labels = mixedMoment B raw16683step1 raw16683step1Labels := by
      have ha : raw16683step1 = (fun i j => raw16683step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16683step1 raw16683step0; decide +kernel
      have hl : raw16683step1Labels = raw16683step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16683step0 raw16683step0Labels permutation150 permutation2
    mixedMoment B raw16683step1 raw16683step1Labels = mixedMoment B raw16683step2 raw16683step2Labels := by
      have ha : raw16683step2 = -raw16683step1 := by apply Matrix.ext; change ∀ i j, raw16683step2 i j = -(raw16683step1 i j); unfold raw16683step2 raw16683step1; decide +kernel
      have hl : raw16683step2Labels = raw16683step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw16684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16684step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16684step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16684 raw16684Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw16684 raw16684Labels = mixedMoment B raw16684step0 raw16684step0Labels := by
      have ha : raw16684step0 = (fun i j => raw16684 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16684step0 raw16684; decide +kernel
      have hl : raw16684step0Labels = raw16684Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16684 raw16684Labels permutation688 permutation2
    mixedMoment B raw16684step0 raw16684step0Labels = mixedMoment B raw16684step1 raw16684step1Labels := by
      have ha : raw16684step1 = -raw16684step0 := by apply Matrix.ext; change ∀ i j, raw16684step1 i j = -(raw16684step0 i j); unfold raw16684step1 raw16684step0; decide +kernel
      have hl : raw16684step1Labels = raw16684step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw16685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16685step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16685step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16685 raw16685Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw16685 raw16685Labels = mixedMoment B raw16685step0 raw16685step0Labels := by
      have hz : ∀ j, raw16685 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16685step0 = (fun i j => raw16685 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16685step0 raw16685; decide +kernel
      have hl : raw16685step0Labels = raw16685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16685 raw16685Labels permutation346 hz
    mixedMoment B raw16685step0 raw16685step0Labels = mixedMoment B raw16685step1 raw16685step1Labels := by
      have ha : raw16685step1 = (fun i j => raw16685step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16685step1 raw16685step0; decide +kernel
      have hl : raw16685step1Labels = raw16685step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16685step0 raw16685step0Labels permutation151 permutation2
    mixedMoment B raw16685step1 raw16685step1Labels = mixedMoment B raw16685step2 raw16685step2Labels := by
      have ha : raw16685step2 = -raw16685step1 := by apply Matrix.ext; change ∀ i j, raw16685step2 i j = -(raw16685step1 i j); unfold raw16685step2 raw16685step1; decide +kernel
      have hl : raw16685step2Labels = raw16685step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw16686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw16686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw16686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16686step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16686step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16686step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16686 raw16686Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw16686 raw16686Labels = mixedMoment B raw16686step0 raw16686step0Labels := by
      have hz : ∀ j, raw16686 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16686step0 = (fun i j => raw16686 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16686step0 raw16686; decide +kernel
      have hl : raw16686step0Labels = raw16686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16686 raw16686Labels permutation346 hz
    mixedMoment B raw16686step0 raw16686step0Labels = mixedMoment B raw16686step1 raw16686step1Labels := by
      have ha : raw16686step1 = (fun i j => raw16686step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16686step1 raw16686step0; decide +kernel
      have hl : raw16686step1Labels = raw16686step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16686step0 raw16686step0Labels permutation33 permutation3
    mixedMoment B raw16686step1 raw16686step1Labels = mixedMoment B raw16686step2 raw16686step2Labels := by
      have ha : raw16686step2 = raw16686step1 := by apply Matrix.ext; unfold raw16686step2 raw16686step1; decide +kernel
      have hl : raw16686step1Labels = labelEmbedding6 ∘ raw16686step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16686step1 raw16686step1Labels raw16686step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw16687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16687step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16687step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16687 raw16687Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw16687 raw16687Labels = mixedMoment B raw16687step0 raw16687step0Labels := by
      have hz : ∀ j, raw16687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16687step0 = (fun i j => raw16687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16687step0 raw16687; decide +kernel
      have hl : raw16687step0Labels = raw16687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16687 raw16687Labels permutation346 hz
    mixedMoment B raw16687step0 raw16687step0Labels = mixedMoment B raw16687step1 raw16687step1Labels := by
      have ha : raw16687step1 = (fun i j => raw16687step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16687step1 raw16687step0; decide +kernel
      have hl : raw16687step1Labels = raw16687step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16687step0 raw16687step0Labels permutation32 permutation3
    mixedMoment B raw16687step1 raw16687step1Labels = mixedMoment B raw16687step2 raw16687step2Labels := by
      have ha : raw16687step2 = raw16687step1 := by apply Matrix.ext; unfold raw16687step2 raw16687step1; decide +kernel
      have hl : raw16687step1Labels = labelEmbedding6 ∘ raw16687step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16687step1 raw16687step1Labels raw16687step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4853 node4853Labels := by rfl

def raw16688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw16688step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16688step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16688step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16688 raw16688Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw16688 raw16688Labels = mixedMoment B raw16688step0 raw16688step0Labels := by
      have hz : ∀ j, raw16688 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16688step0 = (fun i j => raw16688 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16688step0 raw16688; decide +kernel
      have hl : raw16688step0Labels = raw16688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16688 raw16688Labels permutation346 hz
    mixedMoment B raw16688step0 raw16688step0Labels = mixedMoment B raw16688step1 raw16688step1Labels := by
      have ha : raw16688step1 = (fun i j => raw16688step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16688step1 raw16688step0; decide +kernel
      have hl : raw16688step1Labels = raw16688step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16688step0 raw16688step0Labels permutation150 permutation2
    mixedMoment B raw16688step1 raw16688step1Labels = mixedMoment B raw16688step2 raw16688step2Labels := by
      have ha : raw16688step2 = -raw16688step1 := by apply Matrix.ext; change ∀ i j, raw16688step2 i j = -(raw16688step1 i j); unfold raw16688step2 raw16688step1; decide +kernel
      have hl : raw16688step2Labels = raw16688step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw16689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16689step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16689step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16689 raw16689Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw16689 raw16689Labels = mixedMoment B raw16689step0 raw16689step0Labels := by
      have ha : raw16689step0 = (fun i j => raw16689 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16689step0 raw16689; decide +kernel
      have hl : raw16689step0Labels = raw16689Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16689 raw16689Labels permutation688 permutation2
    mixedMoment B raw16689step0 raw16689step0Labels = mixedMoment B raw16689step1 raw16689step1Labels := by
      have ha : raw16689step1 = -raw16689step0 := by apply Matrix.ext; change ∀ i j, raw16689step1 i j = -(raw16689step0 i j); unfold raw16689step1 raw16689step0; decide +kernel
      have hl : raw16689step1Labels = raw16689step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5074 node5074Labels := by rfl

def raw16690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16690step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16690step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16690step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16690 raw16690Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw16690 raw16690Labels = mixedMoment B raw16690step0 raw16690step0Labels := by
      have hz : ∀ j, raw16690 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16690step0 = (fun i j => raw16690 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16690step0 raw16690; decide +kernel
      have hl : raw16690step0Labels = raw16690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16690 raw16690Labels permutation346 hz
    mixedMoment B raw16690step0 raw16690step0Labels = mixedMoment B raw16690step1 raw16690step1Labels := by
      have ha : raw16690step1 = (fun i j => raw16690step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16690step1 raw16690step0; decide +kernel
      have hl : raw16690step1Labels = raw16690step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16690step0 raw16690step0Labels permutation151 permutation2
    mixedMoment B raw16690step1 raw16690step1Labels = mixedMoment B raw16690step2 raw16690step2Labels := by
      have ha : raw16690step2 = -raw16690step1 := by apply Matrix.ext; change ∀ i j, raw16690step2 i j = -(raw16690step1 i j); unfold raw16690step2 raw16690step1; decide +kernel
      have hl : raw16690step2Labels = raw16690step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw16691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw16691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw16691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16691step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16691step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16691step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16691 raw16691Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw16691 raw16691Labels = mixedMoment B raw16691step0 raw16691step0Labels := by
      have hz : ∀ j, raw16691 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16691step0 = (fun i j => raw16691 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16691step0 raw16691; decide +kernel
      have hl : raw16691step0Labels = raw16691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16691 raw16691Labels permutation346 hz
    mixedMoment B raw16691step0 raw16691step0Labels = mixedMoment B raw16691step1 raw16691step1Labels := by
      have ha : raw16691step1 = (fun i j => raw16691step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16691step1 raw16691step0; decide +kernel
      have hl : raw16691step1Labels = raw16691step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16691step0 raw16691step0Labels permutation151 permutation2
    mixedMoment B raw16691step1 raw16691step1Labels = mixedMoment B raw16691step2 raw16691step2Labels := by
      have ha : raw16691step2 = -raw16691step1 := by apply Matrix.ext; change ∀ i j, raw16691step2 i j = -(raw16691step1 i j); unfold raw16691step2 raw16691step1; decide +kernel
      have hl : raw16691step2Labels = raw16691step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw16692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16692Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16692step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw16692step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16692step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw16692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16692 raw16692Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw16692 raw16692Labels = mixedMoment B raw16692step0 raw16692step0Labels := by
      have hz : ∀ j, raw16692 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16692step0 = (fun i j => raw16692 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16692step0 raw16692; decide +kernel
      have hl : raw16692step0Labels = raw16692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16692 raw16692Labels permutation346 hz
    mixedMoment B raw16692step0 raw16692step0Labels = mixedMoment B raw16692step1 raw16692step1Labels := by
      have ha : raw16692step1 = (fun i j => raw16692step0 (permutation147 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16692step1 raw16692step0; decide +kernel
      have hl : raw16692step1Labels = raw16692step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16692step0 raw16692step0Labels permutation147 permutation7
    mixedMoment B raw16692step1 raw16692step1Labels = mixedMoment B raw16692step2 raw16692step2Labels := by
      have ha : raw16692step2 = raw16692step1 := by apply Matrix.ext; unfold raw16692step2 raw16692step1; decide +kernel
      have hl : raw16692step1Labels = labelEmbedding1 ∘ raw16692step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16692step1 raw16692step1Labels raw16692step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

def raw16693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16693Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16693step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16693step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16693step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16693 raw16693Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw16693 raw16693Labels = mixedMoment B raw16693step0 raw16693step0Labels := by
      have ha : raw16693step0 = (fun i j => raw16693 (permutation668 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16693step0 raw16693; decide +kernel
      have hl : raw16693step0Labels = raw16693Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16693 raw16693Labels permutation668 permutation7
    mixedMoment B raw16693step0 raw16693step0Labels = mixedMoment B raw16693step1 raw16693step1Labels := by
      have ha : raw16693step1 = raw16693step0 := by apply Matrix.ext; unfold raw16693step1 raw16693step0; decide +kernel
      have hl : raw16693step0Labels = labelEmbedding1 ∘ raw16693step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16693step0 raw16693step0Labels raw16693step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3800 node3800Labels := by rfl

def raw16694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16694Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16694step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16694step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16694step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16694step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16694 raw16694Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw16694 raw16694Labels = mixedMoment B raw16694step0 raw16694step0Labels := by
      have hz : ∀ j, raw16694 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16694step0 = (fun i j => raw16694 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16694step0 raw16694; decide +kernel
      have hl : raw16694step0Labels = raw16694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16694 raw16694Labels permutation346 hz
    mixedMoment B raw16694step0 raw16694step0Labels = mixedMoment B raw16694step1 raw16694step1Labels := by
      have ha : raw16694step1 = (fun i j => raw16694step0 (permutation147 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16694step1 raw16694step0; decide +kernel
      have hl : raw16694step1Labels = raw16694step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16694step0 raw16694step0Labels permutation147 permutation7
    mixedMoment B raw16694step1 raw16694step1Labels = mixedMoment B raw16694step2 raw16694step2Labels := by
      have ha : raw16694step2 = raw16694step1 := by apply Matrix.ext; unfold raw16694step2 raw16694step1; decide +kernel
      have hl : raw16694step1Labels = labelEmbedding1 ∘ raw16694step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16694step1 raw16694step1Labels raw16694step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3808 node3808Labels := by rfl

def raw16695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16695Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16695step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16695step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16695step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16695 raw16695Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw16695 raw16695Labels = mixedMoment B raw16695step0 raw16695step0Labels := by
      have hz : ∀ j, raw16695 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16695step0 = (fun i j => raw16695 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16695step0 raw16695; decide +kernel
      have hl : raw16695step0Labels = raw16695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16695 raw16695Labels permutation346 hz
    mixedMoment B raw16695step0 raw16695step0Labels = mixedMoment B raw16695step1 raw16695step1Labels := by
      have ha : raw16695step1 = (fun i j => raw16695step0 (permutation147 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16695step1 raw16695step0; decide +kernel
      have hl : raw16695step1Labels = raw16695step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16695step0 raw16695step0Labels permutation147 permutation7
    mixedMoment B raw16695step1 raw16695step1Labels = mixedMoment B raw16695step2 raw16695step2Labels := by
      have ha : raw16695step2 = raw16695step1 := by apply Matrix.ext; unfold raw16695step2 raw16695step1; decide +kernel
      have hl : raw16695step1Labels = labelEmbedding1 ∘ raw16695step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16695step1 raw16695step1Labels raw16695step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw16696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16696Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16696step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16696step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16696step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16696step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16696 raw16696Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw16696 raw16696Labels = mixedMoment B raw16696step0 raw16696step0Labels := by
      have hz : ∀ j, raw16696 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16696step0 = (fun i j => raw16696 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16696step0 raw16696; decide +kernel
      have hl : raw16696step0Labels = raw16696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16696 raw16696Labels permutation346 hz
    mixedMoment B raw16696step0 raw16696step0Labels = mixedMoment B raw16696step1 raw16696step1Labels := by
      have ha : raw16696step1 = (fun i j => raw16696step0 (permutation147 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16696step1 raw16696step0; decide +kernel
      have hl : raw16696step1Labels = raw16696step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16696step0 raw16696step0Labels permutation147 permutation7
    mixedMoment B raw16696step1 raw16696step1Labels = mixedMoment B raw16696step2 raw16696step2Labels := by
      have ha : raw16696step2 = raw16696step1 := by apply Matrix.ext; unfold raw16696step2 raw16696step1; decide +kernel
      have hl : raw16696step1Labels = labelEmbedding1 ∘ raw16696step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16696step1 raw16696step1Labels raw16696step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw16697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16697Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16697step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw16697step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16697step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16697step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16697step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16697 raw16697Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw16697 raw16697Labels = mixedMoment B raw16697step0 raw16697step0Labels := by
      have hz : ∀ j, raw16697 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16697step0 = (fun i j => raw16697 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16697step0 raw16697; decide +kernel
      have hl : raw16697step0Labels = raw16697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16697 raw16697Labels permutation346 hz
    mixedMoment B raw16697step0 raw16697step0Labels = mixedMoment B raw16697step1 raw16697step1Labels := by
      have ha : raw16697step1 = (fun i j => raw16697step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16697step1 raw16697step0; decide +kernel
      have hl : raw16697step1Labels = raw16697step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16697step0 raw16697step0Labels permutation49 permutation5
    mixedMoment B raw16697step1 raw16697step1Labels = mixedMoment B raw16697step2 raw16697step2Labels := by
      have ha : raw16697step2 = -raw16697step1 := by apply Matrix.ext; change ∀ i j, raw16697step2 i j = -(raw16697step1 i j); unfold raw16697step2 raw16697step1; decide +kernel
      have hl : raw16697step2Labels = raw16697step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16697step2 raw16697step2Labels = mixedMoment B raw16697step3 raw16697step3Labels := by
      have ha : raw16697step3 = raw16697step2 := by apply Matrix.ext; unfold raw16697step3 raw16697step2; decide +kernel
      have hl : raw16697step2Labels = labelEmbedding1 ∘ raw16697step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16697step2 raw16697step2Labels raw16697step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2253 node2253Labels := by rfl

def raw16698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16698Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw16698step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16698step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16698step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16698step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16698step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16698 raw16698Labels = mixedMoment B node3803 node3803Labels := by
  calc
    mixedMoment B raw16698 raw16698Labels = mixedMoment B raw16698step0 raw16698step0Labels := by
      have ha : raw16698step0 = (fun i j => raw16698 (permutation193 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16698step0 raw16698; decide +kernel
      have hl : raw16698step0Labels = raw16698Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16698 raw16698Labels permutation193 permutation5
    mixedMoment B raw16698step0 raw16698step0Labels = mixedMoment B raw16698step1 raw16698step1Labels := by
      have ha : raw16698step1 = -raw16698step0 := by apply Matrix.ext; change ∀ i j, raw16698step1 i j = -(raw16698step0 i j); unfold raw16698step1 raw16698step0; decide +kernel
      have hl : raw16698step1Labels = raw16698step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16698step1 raw16698step1Labels = mixedMoment B raw16698step2 raw16698step2Labels := by
      have ha : raw16698step2 = raw16698step1 := by apply Matrix.ext; unfold raw16698step2 raw16698step1; decide +kernel
      have hl : raw16698step1Labels = labelEmbedding1 ∘ raw16698step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16698step1 raw16698step1Labels raw16698step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3803 node3803Labels := by rfl

def raw16699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16699Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16699step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw16699step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw16699step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16699 raw16699Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw16699 raw16699Labels = mixedMoment B raw16699step0 raw16699step0Labels := by
      have hz : ∀ j, raw16699 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16699step0 = (fun i j => raw16699 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16699step0 raw16699; decide +kernel
      have hl : raw16699step0Labels = raw16699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16699 raw16699Labels permutation346 hz
    mixedMoment B raw16699step0 raw16699step0Labels = mixedMoment B raw16699step1 raw16699step1Labels := by
      have ha : raw16699step1 = (fun i j => raw16699step0 (permutation147 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16699step1 raw16699step0; decide +kernel
      have hl : raw16699step1Labels = raw16699step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16699step0 raw16699step0Labels permutation147 permutation7
    mixedMoment B raw16699step1 raw16699step1Labels = mixedMoment B raw16699step2 raw16699step2Labels := by
      have ha : raw16699step2 = raw16699step1 := by apply Matrix.ext; unfold raw16699step2 raw16699step1; decide +kernel
      have hl : raw16699step1Labels = labelEmbedding1 ∘ raw16699step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16699step1 raw16699step1Labels raw16699step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw16700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16700Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16700step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw16700step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16700step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16700step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16700step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16700 raw16700Labels = mixedMoment B node3856 node3856Labels := by
  calc
    mixedMoment B raw16700 raw16700Labels = mixedMoment B raw16700step0 raw16700step0Labels := by
      have hz : ∀ j, raw16700 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16700step0 = (fun i j => raw16700 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16700step0 raw16700; decide +kernel
      have hl : raw16700step0Labels = raw16700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16700 raw16700Labels permutation346 hz
    mixedMoment B raw16700step0 raw16700step0Labels = mixedMoment B raw16700step1 raw16700step1Labels := by
      have ha : raw16700step1 = (fun i j => raw16700step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16700step1 raw16700step0; decide +kernel
      have hl : raw16700step1Labels = raw16700step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16700step0 raw16700step0Labels permutation49 permutation5
    mixedMoment B raw16700step1 raw16700step1Labels = mixedMoment B raw16700step2 raw16700step2Labels := by
      have ha : raw16700step2 = -raw16700step1 := by apply Matrix.ext; change ∀ i j, raw16700step2 i j = -(raw16700step1 i j); unfold raw16700step2 raw16700step1; decide +kernel
      have hl : raw16700step2Labels = raw16700step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16700step2 raw16700step2Labels = mixedMoment B raw16700step3 raw16700step3Labels := by
      have ha : raw16700step3 = raw16700step2 := by apply Matrix.ext; unfold raw16700step3 raw16700step2; decide +kernel
      have hl : raw16700step2Labels = labelEmbedding1 ∘ raw16700step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16700step2 raw16700step2Labels raw16700step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3856 node3856Labels := by rfl

def raw16701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16701Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16701step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw16701step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16701step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16701step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16701step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16701step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16701 raw16701Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw16701 raw16701Labels = mixedMoment B raw16701step0 raw16701step0Labels := by
      have hz : ∀ j, raw16701 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16701step0 = (fun i j => raw16701 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16701step0 raw16701; decide +kernel
      have hl : raw16701step0Labels = raw16701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16701 raw16701Labels permutation346 hz
    mixedMoment B raw16701step0 raw16701step0Labels = mixedMoment B raw16701step1 raw16701step1Labels := by
      have ha : raw16701step1 = (fun i j => raw16701step0 (permutation55 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16701step1 raw16701step0; decide +kernel
      have hl : raw16701step1Labels = raw16701step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16701step0 raw16701step0Labels permutation55 permutation5
    mixedMoment B raw16701step1 raw16701step1Labels = mixedMoment B raw16701step2 raw16701step2Labels := by
      have ha : raw16701step2 = -raw16701step1 := by apply Matrix.ext; change ∀ i j, raw16701step2 i j = -(raw16701step1 i j); unfold raw16701step2 raw16701step1; decide +kernel
      have hl : raw16701step2Labels = raw16701step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16701step2 raw16701step2Labels = mixedMoment B raw16701step3 raw16701step3Labels := by
      have ha : raw16701step3 = raw16701step2 := by apply Matrix.ext; unfold raw16701step3 raw16701step2; decide +kernel
      have hl : raw16701step2Labels = labelEmbedding1 ∘ raw16701step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16701step2 raw16701step2Labels raw16701step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3883 node3883Labels := by rfl

def raw16702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16702Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw16702step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16702step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16702step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16702step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16702step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16702 raw16702Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw16702 raw16702Labels = mixedMoment B raw16702step0 raw16702step0Labels := by
      have ha : raw16702step0 = (fun i j => raw16702 (permutation241 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16702step0 raw16702; decide +kernel
      have hl : raw16702step0Labels = raw16702Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16702 raw16702Labels permutation241 permutation5
    mixedMoment B raw16702step0 raw16702step0Labels = mixedMoment B raw16702step1 raw16702step1Labels := by
      have ha : raw16702step1 = -raw16702step0 := by apply Matrix.ext; change ∀ i j, raw16702step1 i j = -(raw16702step0 i j); unfold raw16702step1 raw16702step0; decide +kernel
      have hl : raw16702step1Labels = raw16702step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16702step1 raw16702step1Labels = mixedMoment B raw16702step2 raw16702step2Labels := by
      have ha : raw16702step2 = raw16702step1 := by apply Matrix.ext; unfold raw16702step2 raw16702step1; decide +kernel
      have hl : raw16702step1Labels = labelEmbedding1 ∘ raw16702step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16702step1 raw16702step1Labels raw16702step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

def raw16703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16703Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16703step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16703step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16703step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16703 raw16703Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw16703 raw16703Labels = mixedMoment B raw16703step0 raw16703step0Labels := by
      have ha : raw16703step0 = (fun i j => raw16703 (permutation678 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16703step0 raw16703; decide +kernel
      have hl : raw16703step0Labels = raw16703Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16703 raw16703Labels permutation678 permutation7
    mixedMoment B raw16703step0 raw16703step0Labels = mixedMoment B raw16703step1 raw16703step1Labels := by
      have ha : raw16703step1 = raw16703step0 := by apply Matrix.ext; unfold raw16703step1 raw16703step0; decide +kernel
      have hl : raw16703step0Labels = labelEmbedding1 ∘ raw16703step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16703step0 raw16703step0Labels raw16703step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3795 node3795Labels := by rfl

def raw16704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16704Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16704step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16704step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16704step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16704 raw16704Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw16704 raw16704Labels = mixedMoment B raw16704step0 raw16704step0Labels := by
      have ha : raw16704step0 = (fun i j => raw16704 (permutation678 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16704step0 raw16704; decide +kernel
      have hl : raw16704step0Labels = raw16704Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16704 raw16704Labels permutation678 permutation7
    mixedMoment B raw16704step0 raw16704step0Labels = mixedMoment B raw16704step1 raw16704step1Labels := by
      have ha : raw16704step1 = raw16704step0 := by apply Matrix.ext; unfold raw16704step1 raw16704step0; decide +kernel
      have hl : raw16704step0Labels = labelEmbedding1 ∘ raw16704step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16704step0 raw16704step0Labels raw16704step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3796 node3796Labels := by rfl

def raw16705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16705Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16705step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16705step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16705step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16705 raw16705Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw16705 raw16705Labels = mixedMoment B raw16705step0 raw16705step0Labels := by
      have ha : raw16705step0 = (fun i j => raw16705 (permutation678 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16705step0 raw16705; decide +kernel
      have hl : raw16705step0Labels = raw16705Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16705 raw16705Labels permutation678 permutation7
    mixedMoment B raw16705step0 raw16705step0Labels = mixedMoment B raw16705step1 raw16705step1Labels := by
      have ha : raw16705step1 = raw16705step0 := by apply Matrix.ext; unfold raw16705step1 raw16705step0; decide +kernel
      have hl : raw16705step0Labels = labelEmbedding1 ∘ raw16705step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16705step0 raw16705step0Labels raw16705step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw16706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16706Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw16706step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16706step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16706step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16706step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16706step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16706 raw16706Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw16706 raw16706Labels = mixedMoment B raw16706step0 raw16706step0Labels := by
      have ha : raw16706step0 = (fun i j => raw16706 (permutation261 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16706step0 raw16706; decide +kernel
      have hl : raw16706step0Labels = raw16706Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16706 raw16706Labels permutation261 permutation5
    mixedMoment B raw16706step0 raw16706step0Labels = mixedMoment B raw16706step1 raw16706step1Labels := by
      have ha : raw16706step1 = -raw16706step0 := by apply Matrix.ext; change ∀ i j, raw16706step1 i j = -(raw16706step0 i j); unfold raw16706step1 raw16706step0; decide +kernel
      have hl : raw16706step1Labels = raw16706step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16706step1 raw16706step1Labels = mixedMoment B raw16706step2 raw16706step2Labels := by
      have ha : raw16706step2 = raw16706step1 := by apply Matrix.ext; unfold raw16706step2 raw16706step1; decide +kernel
      have hl : raw16706step1Labels = labelEmbedding1 ∘ raw16706step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16706step1 raw16706step1Labels raw16706step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw16707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16707Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16707step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw16707step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16707step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16707step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16707step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16707 raw16707Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw16707 raw16707Labels = mixedMoment B raw16707step0 raw16707step0Labels := by
      have hz : ∀ j, raw16707 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16707step0 = (fun i j => raw16707 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16707step0 raw16707; decide +kernel
      have hl : raw16707step0Labels = raw16707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16707 raw16707Labels permutation346 hz
    mixedMoment B raw16707step0 raw16707step0Labels = mixedMoment B raw16707step1 raw16707step1Labels := by
      have ha : raw16707step1 = (fun i j => raw16707step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16707step1 raw16707step0; decide +kernel
      have hl : raw16707step1Labels = raw16707step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16707step0 raw16707step0Labels permutation48 permutation5
    mixedMoment B raw16707step1 raw16707step1Labels = mixedMoment B raw16707step2 raw16707step2Labels := by
      have ha : raw16707step2 = -raw16707step1 := by apply Matrix.ext; change ∀ i j, raw16707step2 i j = -(raw16707step1 i j); unfold raw16707step2 raw16707step1; decide +kernel
      have hl : raw16707step2Labels = raw16707step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16707step2 raw16707step2Labels = mixedMoment B raw16707step3 raw16707step3Labels := by
      have ha : raw16707step3 = raw16707step2 := by apply Matrix.ext; unfold raw16707step3 raw16707step2; decide +kernel
      have hl : raw16707step2Labels = labelEmbedding1 ∘ raw16707step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16707step2 raw16707step2Labels raw16707step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2251 node2251Labels := by rfl

def raw16708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16708Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16708step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw16708step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16708step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw16708step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16708 raw16708Labels = mixedMoment B node3811 node3811Labels := by
  calc
    mixedMoment B raw16708 raw16708Labels = mixedMoment B raw16708step0 raw16708step0Labels := by
      have hz : ∀ j, raw16708 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16708step0 = (fun i j => raw16708 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16708step0 raw16708; decide +kernel
      have hl : raw16708step0Labels = raw16708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16708 raw16708Labels permutation346 hz
    mixedMoment B raw16708step0 raw16708step0Labels = mixedMoment B raw16708step1 raw16708step1Labels := by
      have ha : raw16708step1 = (fun i j => raw16708step0 (permutation147 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16708step1 raw16708step0; decide +kernel
      have hl : raw16708step1Labels = raw16708step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16708step0 raw16708step0Labels permutation147 permutation7
    mixedMoment B raw16708step1 raw16708step1Labels = mixedMoment B raw16708step2 raw16708step2Labels := by
      have ha : raw16708step2 = raw16708step1 := by apply Matrix.ext; unfold raw16708step2 raw16708step1; decide +kernel
      have hl : raw16708step1Labels = labelEmbedding1 ∘ raw16708step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16708step1 raw16708step1Labels raw16708step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3811 node3811Labels := by rfl

def raw16709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16709Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw16709step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16709step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16709step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16709 raw16709Labels = mixedMoment B node3802 node3802Labels := by
  calc
    mixedMoment B raw16709 raw16709Labels = mixedMoment B raw16709step0 raw16709step0Labels := by
      have ha : raw16709step0 = (fun i j => raw16709 (permutation192 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16709step0 raw16709; decide +kernel
      have hl : raw16709step0Labels = raw16709Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16709 raw16709Labels permutation192 permutation5
    mixedMoment B raw16709step0 raw16709step0Labels = mixedMoment B raw16709step1 raw16709step1Labels := by
      have ha : raw16709step1 = -raw16709step0 := by apply Matrix.ext; change ∀ i j, raw16709step1 i j = -(raw16709step0 i j); unfold raw16709step1 raw16709step0; decide +kernel
      have hl : raw16709step1Labels = raw16709step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16709step1 raw16709step1Labels = mixedMoment B raw16709step2 raw16709step2Labels := by
      have ha : raw16709step2 = raw16709step1 := by apply Matrix.ext; unfold raw16709step2 raw16709step1; decide +kernel
      have hl : raw16709step1Labels = labelEmbedding1 ∘ raw16709step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16709step1 raw16709step1Labels raw16709step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3802 node3802Labels := by rfl

def raw16710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw16710step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw16710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16710step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16710step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16710step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16710 raw16710Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw16710 raw16710Labels = mixedMoment B raw16710step0 raw16710step0Labels := by
      have hz : ∀ j, raw16710 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16710step0 = (fun i j => raw16710 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16710step0 raw16710; decide +kernel
      have hl : raw16710step0Labels = raw16710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16710 raw16710Labels permutation346 hz
    mixedMoment B raw16710step0 raw16710step0Labels = mixedMoment B raw16710step1 raw16710step1Labels := by
      have ha : raw16710step1 = (fun i j => raw16710step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16710step1 raw16710step0; decide +kernel
      have hl : raw16710step1Labels = raw16710step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16710step0 raw16710step0Labels permutation48 permutation5
    mixedMoment B raw16710step1 raw16710step1Labels = mixedMoment B raw16710step2 raw16710step2Labels := by
      have ha : raw16710step2 = -raw16710step1 := by apply Matrix.ext; change ∀ i j, raw16710step2 i j = -(raw16710step1 i j); unfold raw16710step2 raw16710step1; decide +kernel
      have hl : raw16710step2Labels = raw16710step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16710step2 raw16710step2Labels = mixedMoment B raw16710step3 raw16710step3Labels := by
      have ha : raw16710step3 = raw16710step2 := by apply Matrix.ext; unfold raw16710step3 raw16710step2; decide +kernel
      have hl : raw16710step2Labels = labelEmbedding1 ∘ raw16710step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16710step2 raw16710step2Labels raw16710step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3854 node3854Labels := by rfl

def raw16711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16711Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16711step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16711step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16711step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16711step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16711step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16711 raw16711Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw16711 raw16711Labels = mixedMoment B raw16711step0 raw16711step0Labels := by
      have hz : ∀ j, raw16711 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16711step0 = (fun i j => raw16711 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16711step0 raw16711; decide +kernel
      have hl : raw16711step0Labels = raw16711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16711 raw16711Labels permutation346 hz
    mixedMoment B raw16711step0 raw16711step0Labels = mixedMoment B raw16711step1 raw16711step1Labels := by
      have ha : raw16711step1 = (fun i j => raw16711step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16711step1 raw16711step0; decide +kernel
      have hl : raw16711step1Labels = raw16711step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16711step0 raw16711step0Labels permutation54 permutation5
    mixedMoment B raw16711step1 raw16711step1Labels = mixedMoment B raw16711step2 raw16711step2Labels := by
      have ha : raw16711step2 = -raw16711step1 := by apply Matrix.ext; change ∀ i j, raw16711step2 i j = -(raw16711step1 i j); unfold raw16711step2 raw16711step1; decide +kernel
      have hl : raw16711step2Labels = raw16711step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16711step2 raw16711step2Labels = mixedMoment B raw16711step3 raw16711step3Labels := by
      have ha : raw16711step3 = raw16711step2 := by apply Matrix.ext; unfold raw16711step3 raw16711step2; decide +kernel
      have hl : raw16711step2Labels = labelEmbedding1 ∘ raw16711step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16711step2 raw16711step2Labels raw16711step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw16712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16712Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16712step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16712step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16712step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16712step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16712step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16712 raw16712Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw16712 raw16712Labels = mixedMoment B raw16712step0 raw16712step0Labels := by
      have hz : ∀ j, raw16712 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16712step0 = (fun i j => raw16712 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16712step0 raw16712; decide +kernel
      have hl : raw16712step0Labels = raw16712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16712 raw16712Labels permutation346 hz
    mixedMoment B raw16712step0 raw16712step0Labels = mixedMoment B raw16712step1 raw16712step1Labels := by
      have ha : raw16712step1 = (fun i j => raw16712step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16712step1 raw16712step0; decide +kernel
      have hl : raw16712step1Labels = raw16712step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16712step0 raw16712step0Labels permutation50 permutation5
    mixedMoment B raw16712step1 raw16712step1Labels = mixedMoment B raw16712step2 raw16712step2Labels := by
      have ha : raw16712step2 = -raw16712step1 := by apply Matrix.ext; change ∀ i j, raw16712step2 i j = -(raw16712step1 i j); unfold raw16712step2 raw16712step1; decide +kernel
      have hl : raw16712step2Labels = raw16712step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16712step2 raw16712step2Labels = mixedMoment B raw16712step3 raw16712step3Labels := by
      have ha : raw16712step3 = raw16712step2 := by apply Matrix.ext; unfold raw16712step3 raw16712step2; decide +kernel
      have hl : raw16712step2Labels = labelEmbedding1 ∘ raw16712step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16712step2 raw16712step2Labels raw16712step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2274 node2274Labels := by rfl

def raw16713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16713step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16713step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16713step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16713step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16713 raw16713Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw16713 raw16713Labels = mixedMoment B raw16713step0 raw16713step0Labels := by
      have hz : ∀ j, raw16713 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16713step0 = (fun i j => raw16713 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16713step0 raw16713; decide +kernel
      have hl : raw16713step0Labels = raw16713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16713 raw16713Labels permutation346 hz
    mixedMoment B raw16713step0 raw16713step0Labels = mixedMoment B raw16713step1 raw16713step1Labels := by
      have ha : raw16713step1 = (fun i j => raw16713step0 (permutation147 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16713step1 raw16713step0; decide +kernel
      have hl : raw16713step1Labels = raw16713step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16713step0 raw16713step0Labels permutation147 permutation7
    mixedMoment B raw16713step1 raw16713step1Labels = mixedMoment B raw16713step2 raw16713step2Labels := by
      have ha : raw16713step2 = raw16713step1 := by apply Matrix.ext; unfold raw16713step2 raw16713step1; decide +kernel
      have hl : raw16713step1Labels = labelEmbedding1 ∘ raw16713step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16713step1 raw16713step1Labels raw16713step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3770 node3770Labels := by rfl

def raw16714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16714step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16714step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16714step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16714 raw16714Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw16714 raw16714Labels = mixedMoment B raw16714step0 raw16714step0Labels := by
      have ha : raw16714step0 = (fun i j => raw16714 (permutation678 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16714step0 raw16714; decide +kernel
      have hl : raw16714step0Labels = raw16714Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16714 raw16714Labels permutation678 permutation7
    mixedMoment B raw16714step0 raw16714step0Labels = mixedMoment B raw16714step1 raw16714step1Labels := by
      have ha : raw16714step1 = raw16714step0 := by apply Matrix.ext; unfold raw16714step1 raw16714step0; decide +kernel
      have hl : raw16714step0Labels = labelEmbedding1 ∘ raw16714step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16714step0 raw16714step0Labels raw16714step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

def raw16715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16715step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16715 raw16715Labels = mixedMoment B node3771 node3771Labels := by
  calc
    mixedMoment B raw16715 raw16715Labels = mixedMoment B raw16715step0 raw16715step0Labels := by
      have hz : ∀ j, raw16715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16715step0 = (fun i j => raw16715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16715step0 raw16715; decide +kernel
      have hl : raw16715step0Labels = raw16715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16715 raw16715Labels permutation346 hz
    mixedMoment B raw16715step0 raw16715step0Labels = mixedMoment B raw16715step1 raw16715step1Labels := by
      have ha : raw16715step1 = (fun i j => raw16715step0 (permutation147 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16715step1 raw16715step0; decide +kernel
      have hl : raw16715step1Labels = raw16715step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16715step0 raw16715step0Labels permutation147 permutation7
    mixedMoment B raw16715step1 raw16715step1Labels = mixedMoment B raw16715step2 raw16715step2Labels := by
      have ha : raw16715step2 = raw16715step1 := by apply Matrix.ext; unfold raw16715step2 raw16715step1; decide +kernel
      have hl : raw16715step1Labels = labelEmbedding1 ∘ raw16715step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16715step1 raw16715step1Labels raw16715step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3771 node3771Labels := by rfl

def raw16716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw16716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw16716step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16716step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16716step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16716step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16716 raw16716Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw16716 raw16716Labels = mixedMoment B raw16716step0 raw16716step0Labels := by
      have hz : ∀ j, raw16716 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16716step0 = (fun i j => raw16716 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16716step0 raw16716; decide +kernel
      have hl : raw16716step0Labels = raw16716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16716 raw16716Labels permutation346 hz
    mixedMoment B raw16716step0 raw16716step0Labels = mixedMoment B raw16716step1 raw16716step1Labels := by
      have ha : raw16716step1 = (fun i j => raw16716step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16716step1 raw16716step0; decide +kernel
      have hl : raw16716step1Labels = raw16716step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16716step0 raw16716step0Labels permutation50 permutation5
    mixedMoment B raw16716step1 raw16716step1Labels = mixedMoment B raw16716step2 raw16716step2Labels := by
      have ha : raw16716step2 = -raw16716step1 := by apply Matrix.ext; change ∀ i j, raw16716step2 i j = -(raw16716step1 i j); unfold raw16716step2 raw16716step1; decide +kernel
      have hl : raw16716step2Labels = raw16716step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16716step2 raw16716step2Labels = mixedMoment B raw16716step3 raw16716step3Labels := by
      have ha : raw16716step3 = raw16716step2 := by apply Matrix.ext; unfold raw16716step3 raw16716step2; decide +kernel
      have hl : raw16716step2Labels = labelEmbedding1 ∘ raw16716step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16716step2 raw16716step2Labels raw16716step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw16717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16717step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3]]
def raw16717step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16717step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw16717step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16717step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw16717step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16717 raw16717Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw16717 raw16717Labels = mixedMoment B raw16717step0 raw16717step0Labels := by
      have hz : ∀ j, raw16717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16717step0 = (fun i j => raw16717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16717step0 raw16717; decide +kernel
      have hl : raw16717step0Labels = raw16717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16717 raw16717Labels permutation346 hz
    mixedMoment B raw16717step0 raw16717step0Labels = mixedMoment B raw16717step1 raw16717step1Labels := by
      have ha : raw16717step1 = (fun i j => raw16717step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16717step1 raw16717step0; decide +kernel
      have hl : raw16717step1Labels = raw16717step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16717step0 raw16717step0Labels permutation44 permutation5
    mixedMoment B raw16717step1 raw16717step1Labels = mixedMoment B raw16717step2 raw16717step2Labels := by
      have ha : raw16717step2 = -raw16717step1 := by apply Matrix.ext; change ∀ i j, raw16717step2 i j = -(raw16717step1 i j); unfold raw16717step2 raw16717step1; decide +kernel
      have hl : raw16717step2Labels = raw16717step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16717step2 raw16717step2Labels = mixedMoment B raw16717step3 raw16717step3Labels := by
      have ha : raw16717step3 = raw16717step2 := by apply Matrix.ext; unfold raw16717step3 raw16717step2; decide +kernel
      have hl : raw16717step2Labels = labelEmbedding1 ∘ raw16717step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16717step2 raw16717step2Labels raw16717step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

def raw16718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16718step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw16718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16718 raw16718Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw16718 raw16718Labels = mixedMoment B raw16718step0 raw16718step0Labels := by
      have hz : ∀ j, raw16718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16718step0 = (fun i j => raw16718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16718step0 raw16718; decide +kernel
      have hl : raw16718step0Labels = raw16718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16718 raw16718Labels permutation346 hz
    mixedMoment B raw16718step0 raw16718step0Labels = mixedMoment B raw16718step1 raw16718step1Labels := by
      have ha : raw16718step1 = (fun i j => raw16718step0 (permutation147 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16718step1 raw16718step0; decide +kernel
      have hl : raw16718step1Labels = raw16718step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16718step0 raw16718step0Labels permutation147 permutation7
    mixedMoment B raw16718step1 raw16718step1Labels = mixedMoment B raw16718step2 raw16718step2Labels := by
      have ha : raw16718step2 = raw16718step1 := by apply Matrix.ext; unfold raw16718step2 raw16718step1; decide +kernel
      have hl : raw16718step1Labels = labelEmbedding1 ∘ raw16718step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16718step1 raw16718step1Labels raw16718step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3478 node3478Labels := by rfl

def raw16719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16719step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16719step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16719step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16719 raw16719Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw16719 raw16719Labels = mixedMoment B raw16719step0 raw16719step0Labels := by
      have ha : raw16719step0 = (fun i j => raw16719 (permutation678 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16719step0 raw16719; decide +kernel
      have hl : raw16719step0Labels = raw16719Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16719 raw16719Labels permutation678 permutation7
    mixedMoment B raw16719step0 raw16719step0Labels = mixedMoment B raw16719step1 raw16719step1Labels := by
      have ha : raw16719step1 = raw16719step0 := by apply Matrix.ext; unfold raw16719step1 raw16719step0; decide +kernel
      have hl : raw16719step0Labels = labelEmbedding1 ∘ raw16719step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16719step0 raw16719step0Labels raw16719step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

def raw16720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw16720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16720step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16720 raw16720Labels = mixedMoment B node3479 node3479Labels := by
  calc
    mixedMoment B raw16720 raw16720Labels = mixedMoment B raw16720step0 raw16720step0Labels := by
      have hz : ∀ j, raw16720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16720step0 = (fun i j => raw16720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16720step0 raw16720; decide +kernel
      have hl : raw16720step0Labels = raw16720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16720 raw16720Labels permutation346 hz
    mixedMoment B raw16720step0 raw16720step0Labels = mixedMoment B raw16720step1 raw16720step1Labels := by
      have ha : raw16720step1 = (fun i j => raw16720step0 (permutation147 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16720step1 raw16720step0; decide +kernel
      have hl : raw16720step1Labels = raw16720step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16720step0 raw16720step0Labels permutation147 permutation7
    mixedMoment B raw16720step1 raw16720step1Labels = mixedMoment B raw16720step2 raw16720step2Labels := by
      have ha : raw16720step2 = raw16720step1 := by apply Matrix.ext; unfold raw16720step2 raw16720step1; decide +kernel
      have hl : raw16720step1Labels = labelEmbedding1 ∘ raw16720step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16720step1 raw16720step1Labels raw16720step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3479 node3479Labels := by rfl

def raw16721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw16721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw16721step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16721step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16721step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16721 raw16721Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw16721 raw16721Labels = mixedMoment B raw16721step0 raw16721step0Labels := by
      have hz : ∀ j, raw16721 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16721step0 = (fun i j => raw16721 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16721step0 raw16721; decide +kernel
      have hl : raw16721step0Labels = raw16721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16721 raw16721Labels permutation346 hz
    mixedMoment B raw16721step0 raw16721step0Labels = mixedMoment B raw16721step1 raw16721step1Labels := by
      have ha : raw16721step1 = (fun i j => raw16721step0 (permutation147 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16721step1 raw16721step0; decide +kernel
      have hl : raw16721step1Labels = raw16721step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16721step0 raw16721step0Labels permutation147 permutation7
    mixedMoment B raw16721step1 raw16721step1Labels = mixedMoment B raw16721step2 raw16721step2Labels := by
      have ha : raw16721step2 = raw16721step1 := by apply Matrix.ext; unfold raw16721step2 raw16721step1; decide +kernel
      have hl : raw16721step1Labels = labelEmbedding1 ∘ raw16721step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16721step1 raw16721step1Labels raw16721step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw16722 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16722step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16722 raw16722Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw16722 raw16722Labels = mixedMoment B raw16722step0 raw16722step0Labels := by
      have hz : ∀ j, raw16722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16722step0 = (fun i j => raw16722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16722step0 raw16722; decide +kernel
      have hl : raw16722step0Labels = raw16722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16722 raw16722Labels permutation346 hz
    mixedMoment B raw16722step0 raw16722step0Labels = mixedMoment B raw16722step1 raw16722step1Labels := by
      have ha : raw16722step1 = (fun i j => raw16722step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16722step1 raw16722step0; decide +kernel
      have hl : raw16722step1Labels = raw16722step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16722step0 raw16722step0Labels permutation150 permutation2
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw16723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw16723step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw16723step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16723step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw16723step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16723 raw16723Labels = mixedMoment B node5103 node5103Labels := by
  calc
    mixedMoment B raw16723 raw16723Labels = mixedMoment B raw16723step0 raw16723step0Labels := by
      have hz : ∀ j, raw16723 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16723step0 = (fun i j => raw16723 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16723step0 raw16723; decide +kernel
      have hl : raw16723step0Labels = raw16723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16723 raw16723Labels permutation346 hz
    mixedMoment B raw16723step0 raw16723step0Labels = mixedMoment B raw16723step1 raw16723step1Labels := by
      have ha : raw16723step1 = (fun i j => raw16723step0 (permutation64 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16723step1 raw16723step0; decide +kernel
      have hl : raw16723step1Labels = raw16723step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16723step0 raw16723step0Labels permutation64 permutation3
    mixedMoment B raw16723step1 raw16723step1Labels = mixedMoment B raw16723step2 raw16723step2Labels := by
      have ha : raw16723step2 = -raw16723step1 := by apply Matrix.ext; change ∀ i j, raw16723step2 i j = -(raw16723step1 i j); unfold raw16723step2 raw16723step1; decide +kernel
      have hl : raw16723step2Labels = raw16723step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16723step2 raw16723step2Labels = mixedMoment B raw16723step3 raw16723step3Labels := by
      have ha : raw16723step3 = raw16723step2 := by apply Matrix.ext; unfold raw16723step3 raw16723step2; decide +kernel
      have hl : raw16723step2Labels = labelEmbedding6 ∘ raw16723step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16723step2 raw16723step2Labels raw16723step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5103 node5103Labels := by rfl

def raw16724 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw16724step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16724 raw16724Labels = mixedMoment B node5087 node5087Labels := by
  calc
    mixedMoment B raw16724 raw16724Labels = mixedMoment B raw16724step0 raw16724step0Labels := by
      have hz : ∀ j, raw16724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16724step0 = (fun i j => raw16724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16724step0 raw16724; decide +kernel
      have hl : raw16724step0Labels = raw16724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16724 raw16724Labels permutation346 hz
    mixedMoment B raw16724step0 raw16724step0Labels = mixedMoment B raw16724step1 raw16724step1Labels := by
      have ha : raw16724step1 = (fun i j => raw16724step0 (permutation147 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16724step1 raw16724step0; decide +kernel
      have hl : raw16724step1Labels = raw16724step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16724step0 raw16724step0Labels permutation147 permutation2
    _ = mixedMoment B node5087 node5087Labels := by rfl

def raw16725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16725step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 2, 0]]
def raw16725step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw16725step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16725step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw16725step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16725 raw16725Labels = mixedMoment B node5287 node5287Labels := by
  calc
    mixedMoment B raw16725 raw16725Labels = mixedMoment B raw16725step0 raw16725step0Labels := by
      have hz : ∀ j, raw16725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16725step0 = (fun i j => raw16725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16725step0 raw16725; decide +kernel
      have hl : raw16725step0Labels = raw16725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16725 raw16725Labels permutation346 hz
    mixedMoment B raw16725step0 raw16725step0Labels = mixedMoment B raw16725step1 raw16725step1Labels := by
      have ha : raw16725step1 = (fun i j => raw16725step0 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16725step1 raw16725step0; decide +kernel
      have hl : raw16725step1Labels = raw16725step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16725step0 raw16725step0Labels permutation48 permutation4
    mixedMoment B raw16725step1 raw16725step1Labels = mixedMoment B raw16725step2 raw16725step2Labels := by
      have ha : raw16725step2 = -raw16725step1 := by apply Matrix.ext; change ∀ i j, raw16725step2 i j = -(raw16725step1 i j); unfold raw16725step2 raw16725step1; decide +kernel
      have hl : raw16725step2Labels = raw16725step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16725step2 raw16725step2Labels = mixedMoment B raw16725step3 raw16725step3Labels := by
      have ha : raw16725step3 = raw16725step2 := by apply Matrix.ext; unfold raw16725step3 raw16725step2; decide +kernel
      have hl : raw16725step2Labels = labelEmbedding7 ∘ raw16725step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16725step2 raw16725step2Labels raw16725step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5287 node5287Labels := by rfl

def raw16726 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16726step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw16726step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16726 raw16726Labels = mixedMoment B node5090 node5090Labels := by
  calc
    mixedMoment B raw16726 raw16726Labels = mixedMoment B raw16726step0 raw16726step0Labels := by
      have hz : ∀ j, raw16726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16726step0 = (fun i j => raw16726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16726step0 raw16726; decide +kernel
      have hl : raw16726step0Labels = raw16726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16726 raw16726Labels permutation346 hz
    mixedMoment B raw16726step0 raw16726step0Labels = mixedMoment B raw16726step1 raw16726step1Labels := by
      have ha : raw16726step1 = (fun i j => raw16726step0 (permutation147 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16726step1 raw16726step0; decide +kernel
      have hl : raw16726step1Labels = raw16726step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16726step0 raw16726step0Labels permutation147 permutation2
    _ = mixedMoment B node5090 node5090Labels := by rfl

def raw16727 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16727step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16727step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16727step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16727step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16727step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16727step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16727step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16727step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16727 raw16727Labels = mixedMoment B node3817 node3817Labels := by
  calc
    mixedMoment B raw16727 raw16727Labels = mixedMoment B raw16727step0 raw16727step0Labels := by
      have hz : ∀ j, raw16727 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16727step0 = (fun i j => raw16727 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16727step0 raw16727; decide +kernel
      have hl : raw16727step0Labels = raw16727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16727 raw16727Labels permutation434 hz
    mixedMoment B raw16727step0 raw16727step0Labels = mixedMoment B raw16727step1 raw16727step1Labels := by
      have hz : ∀ j, raw16727step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16727step1 = (fun i j => raw16727step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16727step1 raw16727step0; decide +kernel
      have hl : raw16727step1Labels = raw16727step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16727step0 raw16727step0Labels permutation80 hz
    mixedMoment B raw16727step1 raw16727step1Labels = mixedMoment B raw16727step2 raw16727step2Labels := by
      have ha : raw16727step2 = (fun i j => raw16727step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16727step2 raw16727step1; decide +kernel
      have hl : raw16727step2Labels = raw16727step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16727step1 raw16727step1Labels permutation31 permutation7
    mixedMoment B raw16727step2 raw16727step2Labels = mixedMoment B raw16727step3 raw16727step3Labels := by
      have ha : raw16727step3 = -raw16727step2 := by apply Matrix.ext; change ∀ i j, raw16727step3 i j = -(raw16727step2 i j); unfold raw16727step3 raw16727step2; decide +kernel
      have hl : raw16727step3Labels = raw16727step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16727step3 raw16727step3Labels = mixedMoment B raw16727step4 raw16727step4Labels := by
      have ha : raw16727step4 = raw16727step3 := by apply Matrix.ext; unfold raw16727step4 raw16727step3; decide +kernel
      have hl : raw16727step3Labels = labelEmbedding1 ∘ raw16727step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16727step3 raw16727step3Labels raw16727step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3817 node3817Labels := by rfl

def raw16728 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16728step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16728step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16728step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16728step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16728step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16728step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16728 raw16728Labels = mixedMoment B node3471 node3471Labels := by
  calc
    mixedMoment B raw16728 raw16728Labels = mixedMoment B raw16728step0 raw16728step0Labels := by
      have hz : ∀ j, raw16728 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16728step0 = (fun i j => raw16728 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16728step0 raw16728; decide +kernel
      have hl : raw16728step0Labels = raw16728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16728 raw16728Labels permutation346 hz
    mixedMoment B raw16728step0 raw16728step0Labels = mixedMoment B raw16728step1 raw16728step1Labels := by
      have ha : raw16728step1 = (fun i j => raw16728step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16728step1 raw16728step0; decide +kernel
      have hl : raw16728step1Labels = raw16728step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16728step0 raw16728step0Labels permutation151 permutation7
    mixedMoment B raw16728step1 raw16728step1Labels = mixedMoment B raw16728step2 raw16728step2Labels := by
      have ha : raw16728step2 = -raw16728step1 := by apply Matrix.ext; change ∀ i j, raw16728step2 i j = -(raw16728step1 i j); unfold raw16728step2 raw16728step1; decide +kernel
      have hl : raw16728step2Labels = raw16728step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16728step2 raw16728step2Labels = mixedMoment B raw16728step3 raw16728step3Labels := by
      have ha : raw16728step3 = raw16728step2 := by apply Matrix.ext; unfold raw16728step3 raw16728step2; decide +kernel
      have hl : raw16728step2Labels = labelEmbedding1 ∘ raw16728step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16728step2 raw16728step2Labels raw16728step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3471 node3471Labels := by rfl

def raw16729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16729step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw16729step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw16729step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16729step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw16729step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16729 raw16729Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw16729 raw16729Labels = mixedMoment B raw16729step0 raw16729step0Labels := by
      have hz : ∀ j, raw16729 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16729step0 = (fun i j => raw16729 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16729step0 raw16729; decide +kernel
      have hl : raw16729step0Labels = raw16729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16729 raw16729Labels permutation346 hz
    mixedMoment B raw16729step0 raw16729step0Labels = mixedMoment B raw16729step1 raw16729step1Labels := by
      have ha : raw16729step1 = (fun i j => raw16729step0 (permutation55 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16729step1 raw16729step0; decide +kernel
      have hl : raw16729step1Labels = raw16729step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16729step0 raw16729step0Labels permutation55 permutation5
    mixedMoment B raw16729step1 raw16729step1Labels = mixedMoment B raw16729step2 raw16729step2Labels := by
      have ha : raw16729step2 = -raw16729step1 := by apply Matrix.ext; change ∀ i j, raw16729step2 i j = -(raw16729step1 i j); unfold raw16729step2 raw16729step1; decide +kernel
      have hl : raw16729step2Labels = raw16729step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16729step2 raw16729step2Labels = mixedMoment B raw16729step3 raw16729step3Labels := by
      have ha : raw16729step3 = raw16729step2 := by apply Matrix.ext; unfold raw16729step3 raw16729step2; decide +kernel
      have hl : raw16729step2Labels = labelEmbedding1 ∘ raw16729step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16729step2 raw16729step2Labels raw16729step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3024 node3024Labels := by rfl

def raw16730 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16730step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16730step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16730step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw16730step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16730step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw16730step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16730 raw16730Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw16730 raw16730Labels = mixedMoment B raw16730step0 raw16730step0Labels := by
      have hz : ∀ j, raw16730 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16730step0 = (fun i j => raw16730 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16730step0 raw16730; decide +kernel
      have hl : raw16730step0Labels = raw16730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16730 raw16730Labels permutation434 hz
    mixedMoment B raw16730step0 raw16730step0Labels = mixedMoment B raw16730step1 raw16730step1Labels := by
      have hz : ∀ j, raw16730step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16730step1 = (fun i j => raw16730step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16730step1 raw16730step0; decide +kernel
      have hl : raw16730step1Labels = raw16730step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16730step0 raw16730step0Labels permutation80 hz
    mixedMoment B raw16730step1 raw16730step1Labels = mixedMoment B raw16730step2 raw16730step2Labels := by
      have ha : raw16730step2 = (fun i j => raw16730step1 (permutation17 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16730step2 raw16730step1; decide +kernel
      have hl : raw16730step2Labels = raw16730step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16730step1 raw16730step1Labels permutation17 permutation5
    mixedMoment B raw16730step2 raw16730step2Labels = mixedMoment B raw16730step3 raw16730step3Labels := by
      have ha : raw16730step3 = raw16730step2 := by apply Matrix.ext; unfold raw16730step3 raw16730step2; decide +kernel
      have hl : raw16730step2Labels = labelEmbedding1 ∘ raw16730step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16730step2 raw16730step2Labels raw16730step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3626 node3626Labels := by rfl

def raw16731 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16731step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw16731step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16731step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw16731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16731 raw16731Labels = mixedMoment B node3472 node3472Labels := by
  calc
    mixedMoment B raw16731 raw16731Labels = mixedMoment B raw16731step0 raw16731step0Labels := by
      have hz : ∀ j, raw16731 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16731step0 = (fun i j => raw16731 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16731step0 raw16731; decide +kernel
      have hl : raw16731step0Labels = raw16731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16731 raw16731Labels permutation346 hz
    mixedMoment B raw16731step0 raw16731step0Labels = mixedMoment B raw16731step1 raw16731step1Labels := by
      have ha : raw16731step1 = (fun i j => raw16731step0 (permutation65 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16731step1 raw16731step0; decide +kernel
      have hl : raw16731step1Labels = raw16731step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16731step0 raw16731step0Labels permutation65 permutation5
    mixedMoment B raw16731step1 raw16731step1Labels = mixedMoment B raw16731step2 raw16731step2Labels := by
      have ha : raw16731step2 = raw16731step1 := by apply Matrix.ext; unfold raw16731step2 raw16731step1; decide +kernel
      have hl : raw16731step1Labels = labelEmbedding1 ∘ raw16731step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16731step1 raw16731step1Labels raw16731step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3472 node3472Labels := by rfl

def raw16732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw16732step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16732step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16732step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16732step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16732step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16732 raw16732Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw16732 raw16732Labels = mixedMoment B raw16732step0 raw16732step0Labels := by
      have hz : ∀ j, raw16732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16732step0 = (fun i j => raw16732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16732step0 raw16732; decide +kernel
      have hl : raw16732step0Labels = raw16732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16732 raw16732Labels permutation346 hz
    mixedMoment B raw16732step0 raw16732step0Labels = mixedMoment B raw16732step1 raw16732step1Labels := by
      have ha : raw16732step1 = (fun i j => raw16732step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16732step1 raw16732step0; decide +kernel
      have hl : raw16732step1Labels = raw16732step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16732step0 raw16732step0Labels permutation54 permutation5
    mixedMoment B raw16732step1 raw16732step1Labels = mixedMoment B raw16732step2 raw16732step2Labels := by
      have ha : raw16732step2 = -raw16732step1 := by apply Matrix.ext; change ∀ i j, raw16732step2 i j = -(raw16732step1 i j); unfold raw16732step2 raw16732step1; decide +kernel
      have hl : raw16732step2Labels = raw16732step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16732step2 raw16732step2Labels = mixedMoment B raw16732step3 raw16732step3Labels := by
      have ha : raw16732step3 = raw16732step2 := by apply Matrix.ext; unfold raw16732step3 raw16732step2; decide +kernel
      have hl : raw16732step2Labels = labelEmbedding1 ∘ raw16732step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16732step2 raw16732step2Labels raw16732step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3025 node3025Labels := by rfl

def raw16733 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw16733step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw16733step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16733step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16733step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16733step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16733step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16733 raw16733Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw16733 raw16733Labels = mixedMoment B raw16733step0 raw16733step0Labels := by
      have hz : ∀ j, raw16733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16733step0 = (fun i j => raw16733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16733step0 raw16733; decide +kernel
      have hl : raw16733step0Labels = raw16733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16733 raw16733Labels permutation346 hz
    mixedMoment B raw16733step0 raw16733step0Labels = mixedMoment B raw16733step1 raw16733step1Labels := by
      have ha : raw16733step1 = (fun i j => raw16733step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16733step1 raw16733step0; decide +kernel
      have hl : raw16733step1Labels = raw16733step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16733step0 raw16733step0Labels permutation151 permutation7
    mixedMoment B raw16733step1 raw16733step1Labels = mixedMoment B raw16733step2 raw16733step2Labels := by
      have ha : raw16733step2 = -raw16733step1 := by apply Matrix.ext; change ∀ i j, raw16733step2 i j = -(raw16733step1 i j); unfold raw16733step2 raw16733step1; decide +kernel
      have hl : raw16733step2Labels = raw16733step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16733step2 raw16733step2Labels = mixedMoment B raw16733step3 raw16733step3Labels := by
      have ha : raw16733step3 = raw16733step2 := by apply Matrix.ext; unfold raw16733step3 raw16733step2; decide +kernel
      have hl : raw16733step2Labels = labelEmbedding1 ∘ raw16733step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16733step2 raw16733step2Labels raw16733step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3480 node3480Labels := by rfl

def raw16734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw16734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw16734step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16734step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16734step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16734step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16734 raw16734Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw16734 raw16734Labels = mixedMoment B raw16734step0 raw16734step0Labels := by
      have hz : ∀ j, raw16734 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16734step0 = (fun i j => raw16734 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16734step0 raw16734; decide +kernel
      have hl : raw16734step0Labels = raw16734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16734 raw16734Labels permutation346 hz
    mixedMoment B raw16734step0 raw16734step0Labels = mixedMoment B raw16734step1 raw16734step1Labels := by
      have ha : raw16734step1 = (fun i j => raw16734step0 (permutation55 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16734step1 raw16734step0; decide +kernel
      have hl : raw16734step1Labels = raw16734step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16734step0 raw16734step0Labels permutation55 permutation5
    mixedMoment B raw16734step1 raw16734step1Labels = mixedMoment B raw16734step2 raw16734step2Labels := by
      have ha : raw16734step2 = -raw16734step1 := by apply Matrix.ext; change ∀ i j, raw16734step2 i j = -(raw16734step1 i j); unfold raw16734step2 raw16734step1; decide +kernel
      have hl : raw16734step2Labels = raw16734step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16734step2 raw16734step2Labels = mixedMoment B raw16734step3 raw16734step3Labels := by
      have ha : raw16734step3 = raw16734step2 := by apply Matrix.ext; unfold raw16734step3 raw16734step2; decide +kernel
      have hl : raw16734step2Labels = labelEmbedding1 ∘ raw16734step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16734step2 raw16734step2Labels raw16734step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw16735 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw16735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw16735step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16735step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16735step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16735step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16735 raw16735Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw16735 raw16735Labels = mixedMoment B raw16735step0 raw16735step0Labels := by
      have hz : ∀ j, raw16735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16735step0 = (fun i j => raw16735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16735step0 raw16735; decide +kernel
      have hl : raw16735step0Labels = raw16735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16735 raw16735Labels permutation346 hz
    mixedMoment B raw16735step0 raw16735step0Labels = mixedMoment B raw16735step1 raw16735step1Labels := by
      have ha : raw16735step1 = (fun i j => raw16735step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16735step1 raw16735step0; decide +kernel
      have hl : raw16735step1Labels = raw16735step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16735step0 raw16735step0Labels permutation151 permutation7
    mixedMoment B raw16735step1 raw16735step1Labels = mixedMoment B raw16735step2 raw16735step2Labels := by
      have ha : raw16735step2 = -raw16735step1 := by apply Matrix.ext; change ∀ i j, raw16735step2 i j = -(raw16735step1 i j); unfold raw16735step2 raw16735step1; decide +kernel
      have hl : raw16735step2Labels = raw16735step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16735step2 raw16735step2Labels = mixedMoment B raw16735step3 raw16735step3Labels := by
      have ha : raw16735step3 = raw16735step2 := by apply Matrix.ext; unfold raw16735step3 raw16735step2; decide +kernel
      have hl : raw16735step2Labels = labelEmbedding1 ∘ raw16735step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16735step2 raw16735step2Labels raw16735step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw16736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16736Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16736step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16736 raw16736Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw16736 raw16736Labels = mixedMoment B raw16736step0 raw16736step0Labels := by
      have ha : raw16736step0 = (fun i j => raw16736 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16736step0 raw16736; decide +kernel
      have hl : raw16736step0Labels = raw16736Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16736 raw16736Labels permutation265 permutation2
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw16737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16737Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16737step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16737step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16737step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16737step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16737step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16737 raw16737Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw16737 raw16737Labels = mixedMoment B raw16737step0 raw16737step0Labels := by
      have ha : raw16737step0 = (fun i j => raw16737 (permutation685 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16737step0 raw16737; decide +kernel
      have hl : raw16737step0Labels = raw16737Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16737 raw16737Labels permutation685 permutation3
    mixedMoment B raw16737step0 raw16737step0Labels = mixedMoment B raw16737step1 raw16737step1Labels := by
      have ha : raw16737step1 = -raw16737step0 := by apply Matrix.ext; change ∀ i j, raw16737step1 i j = -(raw16737step0 i j); unfold raw16737step1 raw16737step0; decide +kernel
      have hl : raw16737step1Labels = raw16737step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16737step1 raw16737step1Labels = mixedMoment B raw16737step2 raw16737step2Labels := by
      have ha : raw16737step2 = raw16737step1 := by apply Matrix.ext; unfold raw16737step2 raw16737step1; decide +kernel
      have hl : raw16737step1Labels = labelEmbedding6 ∘ raw16737step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16737step1 raw16737step1Labels raw16737step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5480 node5480Labels := by rfl

def raw16738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16738Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16738step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16738step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16738step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16738step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16738step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16738 raw16738Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw16738 raw16738Labels = mixedMoment B raw16738step0 raw16738step0Labels := by
      have ha : raw16738step0 = (fun i j => raw16738 (permutation679 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16738step0 raw16738; decide +kernel
      have hl : raw16738step0Labels = raw16738Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16738 raw16738Labels permutation679 permutation3
    mixedMoment B raw16738step0 raw16738step0Labels = mixedMoment B raw16738step1 raw16738step1Labels := by
      have ha : raw16738step1 = -raw16738step0 := by apply Matrix.ext; change ∀ i j, raw16738step1 i j = -(raw16738step0 i j); unfold raw16738step1 raw16738step0; decide +kernel
      have hl : raw16738step1Labels = raw16738step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16738step1 raw16738step1Labels = mixedMoment B raw16738step2 raw16738step2Labels := by
      have ha : raw16738step2 = raw16738step1 := by apply Matrix.ext; unfold raw16738step2 raw16738step1; decide +kernel
      have hl : raw16738step1Labels = labelEmbedding6 ∘ raw16738step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16738step1 raw16738step1Labels raw16738step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5480 node5480Labels := by rfl

def raw16739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16739Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16739step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16739step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16739step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16739step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16739step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16739 raw16739Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw16739 raw16739Labels = mixedMoment B raw16739step0 raw16739step0Labels := by
      have hz : ∀ j, raw16739 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16739step0 = (fun i j => raw16739 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16739step0 raw16739; decide +kernel
      have hl : raw16739step0Labels = raw16739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16739 raw16739Labels permutation520 hz
    mixedMoment B raw16739step0 raw16739step0Labels = mixedMoment B raw16739step1 raw16739step1Labels := by
      have ha : raw16739step1 = (fun i j => raw16739step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16739step1 raw16739step0; decide +kernel
      have hl : raw16739step1Labels = raw16739step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16739step0 raw16739step0Labels permutation56 permutation7
    mixedMoment B raw16739step1 raw16739step1Labels = mixedMoment B raw16739step2 raw16739step2Labels := by
      have ha : raw16739step2 = -raw16739step1 := by apply Matrix.ext; change ∀ i j, raw16739step2 i j = -(raw16739step1 i j); unfold raw16739step2 raw16739step1; decide +kernel
      have hl : raw16739step2Labels = raw16739step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16739step2 raw16739step2Labels = mixedMoment B raw16739step3 raw16739step3Labels := by
      have ha : raw16739step3 = raw16739step2 := by apply Matrix.ext; unfold raw16739step3 raw16739step2; decide +kernel
      have hl : raw16739step2Labels = labelEmbedding10 ∘ raw16739step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16739step2 raw16739step2Labels raw16739step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw16740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw16740step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16740step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16740step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16740step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16740step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16740 raw16740Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw16740 raw16740Labels = mixedMoment B raw16740step0 raw16740step0Labels := by
      have ha : raw16740step0 = (fun i j => raw16740 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16740step0 raw16740; decide +kernel
      have hl : raw16740step0Labels = raw16740Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16740 raw16740Labels permutation277 permutation7
    mixedMoment B raw16740step0 raw16740step0Labels = mixedMoment B raw16740step1 raw16740step1Labels := by
      have ha : raw16740step1 = -raw16740step0 := by apply Matrix.ext; change ∀ i j, raw16740step1 i j = -(raw16740step0 i j); unfold raw16740step1 raw16740step0; decide +kernel
      have hl : raw16740step1Labels = raw16740step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16740step1 raw16740step1Labels = mixedMoment B raw16740step2 raw16740step2Labels := by
      have ha : raw16740step2 = raw16740step1 := by apply Matrix.ext; unfold raw16740step2 raw16740step1; decide +kernel
      have hl : raw16740step1Labels = labelEmbedding10 ∘ raw16740step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16740step1 raw16740step1Labels raw16740step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw16741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16741Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16741step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16741step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16741step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16741 raw16741Labels = mixedMoment B node5244 node5244Labels := by
  calc
    mixedMoment B raw16741 raw16741Labels = mixedMoment B raw16741step0 raw16741step0Labels := by
      have ha : raw16741step0 = (fun i j => raw16741 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16741step0 raw16741; decide +kernel
      have hl : raw16741step0Labels = raw16741Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16741 raw16741Labels permutation182 permutation3
    mixedMoment B raw16741step0 raw16741step0Labels = mixedMoment B raw16741step1 raw16741step1Labels := by
      have ha : raw16741step1 = raw16741step0 := by apply Matrix.ext; unfold raw16741step1 raw16741step0; decide +kernel
      have hl : raw16741step0Labels = labelEmbedding6 ∘ raw16741step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16741step0 raw16741step0Labels raw16741step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5244 node5244Labels := by rfl

def raw16742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16742Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16742step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16742step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16742step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16742 raw16742Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw16742 raw16742Labels = mixedMoment B raw16742step0 raw16742step0Labels := by
      have ha : raw16742step0 = (fun i j => raw16742 (permutation330 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16742step0 raw16742; decide +kernel
      have hl : raw16742step0Labels = raw16742Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16742 raw16742Labels permutation330 permutation4
    mixedMoment B raw16742step0 raw16742step0Labels = mixedMoment B raw16742step1 raw16742step1Labels := by
      have ha : raw16742step1 = raw16742step0 := by apply Matrix.ext; unfold raw16742step1 raw16742step0; decide +kernel
      have hl : raw16742step0Labels = labelEmbedding7 ∘ raw16742step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16742step0 raw16742step0Labels raw16742step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

def raw16743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16743step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16743step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16743step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16743 raw16743Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw16743 raw16743Labels = mixedMoment B raw16743step0 raw16743step0Labels := by
      have ha : raw16743step0 = (fun i j => raw16743 (permutation329 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16743step0 raw16743; decide +kernel
      have hl : raw16743step0Labels = raw16743Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16743 raw16743Labels permutation329 permutation4
    mixedMoment B raw16743step0 raw16743step0Labels = mixedMoment B raw16743step1 raw16743step1Labels := by
      have ha : raw16743step1 = raw16743step0 := by apply Matrix.ext; unfold raw16743step1 raw16743step0; decide +kernel
      have hl : raw16743step0Labels = labelEmbedding7 ∘ raw16743step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16743step0 raw16743step0Labels raw16743step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

def raw16744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16744step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16744step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16744step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16744 raw16744Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw16744 raw16744Labels = mixedMoment B raw16744step0 raw16744step0Labels := by
      have hz : ∀ j, raw16744 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16744step0 = (fun i j => raw16744 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16744step0 raw16744; decide +kernel
      have hl : raw16744step0Labels = raw16744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16744 raw16744Labels permutation520 hz
    mixedMoment B raw16744step0 raw16744step0Labels = mixedMoment B raw16744step1 raw16744step1Labels := by
      have ha : raw16744step1 = (fun i j => raw16744step0 (permutation74 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16744step1 raw16744step0; decide +kernel
      have hl : raw16744step1Labels = raw16744step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16744step0 raw16744step0Labels permutation74 permutation4
    mixedMoment B raw16744step1 raw16744step1Labels = mixedMoment B raw16744step2 raw16744step2Labels := by
      have ha : raw16744step2 = raw16744step1 := by apply Matrix.ext; unfold raw16744step2 raw16744step1; decide +kernel
      have hl : raw16744step1Labels = labelEmbedding7 ∘ raw16744step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16744step1 raw16744step1Labels raw16744step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw16745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16745Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16745step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16745step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16745step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16745 raw16745Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw16745 raw16745Labels = mixedMoment B raw16745step0 raw16745step0Labels := by
      have ha : raw16745step0 = (fun i j => raw16745 (permutation329 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16745step0 raw16745; decide +kernel
      have hl : raw16745step0Labels = raw16745Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16745 raw16745Labels permutation329 permutation4
    mixedMoment B raw16745step0 raw16745step0Labels = mixedMoment B raw16745step1 raw16745step1Labels := by
      have ha : raw16745step1 = raw16745step0 := by apply Matrix.ext; unfold raw16745step1 raw16745step0; decide +kernel
      have hl : raw16745step0Labels = labelEmbedding7 ∘ raw16745step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16745step0 raw16745step0Labels raw16745step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw16746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16746step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16746step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16746step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16746 raw16746Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw16746 raw16746Labels = mixedMoment B raw16746step0 raw16746step0Labels := by
      have ha : raw16746step0 = (fun i j => raw16746 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16746step0 raw16746; decide +kernel
      have hl : raw16746step0Labels = raw16746Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16746 raw16746Labels permutation158 permutation3
    mixedMoment B raw16746step0 raw16746step0Labels = mixedMoment B raw16746step1 raw16746step1Labels := by
      have ha : raw16746step1 = raw16746step0 := by apply Matrix.ext; unfold raw16746step1 raw16746step0; decide +kernel
      have hl : raw16746step0Labels = labelEmbedding6 ∘ raw16746step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16746step0 raw16746step0Labels raw16746step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5185 node5185Labels := by rfl

def raw16747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16747step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16747 raw16747Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw16747 raw16747Labels = mixedMoment B raw16747step0 raw16747step0Labels := by
      have ha : raw16747step0 = (fun i j => raw16747 (permutation273 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16747step0 raw16747; decide +kernel
      have hl : raw16747step0Labels = raw16747Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16747 raw16747Labels permutation273 permutation2
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw16748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16748Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16748step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16748 raw16748Labels = mixedMoment B node5470 node5470Labels := by
  calc
    mixedMoment B raw16748 raw16748Labels = mixedMoment B raw16748step0 raw16748step0Labels := by
      have ha : raw16748step0 = (fun i j => raw16748 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16748step0 raw16748; decide +kernel
      have hl : raw16748step0Labels = raw16748Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16748 raw16748Labels permutation160 permutation2
    _ = mixedMoment B node5470 node5470Labels := by rfl

def raw16749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw16749step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16749step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16749step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16749 raw16749Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw16749 raw16749Labels = mixedMoment B raw16749step0 raw16749step0Labels := by
      have hz : ∀ j, raw16749 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16749step0 = (fun i j => raw16749 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16749step0 raw16749; decide +kernel
      have hl : raw16749step0Labels = raw16749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16749 raw16749Labels permutation520 hz
    mixedMoment B raw16749step0 raw16749step0Labels = mixedMoment B raw16749step1 raw16749step1Labels := by
      have ha : raw16749step1 = (fun i j => raw16749step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16749step1 raw16749step0; decide +kernel
      have hl : raw16749step1Labels = raw16749step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16749step0 raw16749step0Labels permutation34 permutation2
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw16750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16750step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16750 raw16750Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw16750 raw16750Labels = mixedMoment B raw16750step0 raw16750step0Labels := by
      have ha : raw16750step0 = (fun i j => raw16750 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16750step0 raw16750; decide +kernel
      have hl : raw16750step0Labels = raw16750Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16750 raw16750Labels permutation160 permutation2
    _ = mixedMoment B node5472 node5472Labels := by rfl

def raw16751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16751step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16751step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16751step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16751 raw16751Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw16751 raw16751Labels = mixedMoment B raw16751step0 raw16751step0Labels := by
      have ha : raw16751step0 = (fun i j => raw16751 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16751step0 raw16751; decide +kernel
      have hl : raw16751step0Labels = raw16751Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16751 raw16751Labels permutation152 permutation3
    mixedMoment B raw16751step0 raw16751step0Labels = mixedMoment B raw16751step1 raw16751step1Labels := by
      have ha : raw16751step1 = raw16751step0 := by apply Matrix.ext; unfold raw16751step1 raw16751step0; decide +kernel
      have hl : raw16751step0Labels = labelEmbedding6 ∘ raw16751step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16751step0 raw16751step0Labels raw16751step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5185 node5185Labels := by rfl

def raw16752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16752step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16752 raw16752Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw16752 raw16752Labels = mixedMoment B raw16752step0 raw16752step0Labels := by
      have ha : raw16752step0 = (fun i j => raw16752 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16752step0 raw16752; decide +kernel
      have hl : raw16752step0Labels = raw16752Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16752 raw16752Labels permutation267 permutation2
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw16753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16753 raw16753Labels = mixedMoment B node5470 node5470Labels := by
  calc
    mixedMoment B raw16753 raw16753Labels = mixedMoment B raw16753step0 raw16753step0Labels := by
      have ha : raw16753step0 = (fun i j => raw16753 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16753step0 raw16753; decide +kernel
      have hl : raw16753step0Labels = raw16753Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16753 raw16753Labels permutation154 permutation2
    _ = mixedMoment B node5470 node5470Labels := by rfl

def raw16754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16754 raw16754Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw16754 raw16754Labels = mixedMoment B raw16754step0 raw16754step0Labels := by
      have hz : ∀ j, raw16754 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16754step0 = (fun i j => raw16754 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16754step0 raw16754; decide +kernel
      have hl : raw16754step0Labels = raw16754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16754 raw16754Labels permutation520 hz
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw16755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16755step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16755 raw16755Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw16755 raw16755Labels = mixedMoment B raw16755step0 raw16755step0Labels := by
      have ha : raw16755step0 = (fun i j => raw16755 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16755step0 raw16755; decide +kernel
      have hl : raw16755step0Labels = raw16755Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16755 raw16755Labels permutation154 permutation2
    _ = mixedMoment B node5472 node5472Labels := by rfl

def raw16756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16756step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16756step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16756step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw16756step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16756 raw16756Labels = mixedMoment B node5181 node5181Labels := by
  calc
    mixedMoment B raw16756 raw16756Labels = mixedMoment B raw16756step0 raw16756step0Labels := by
      have ha : raw16756step0 = (fun i j => raw16756 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16756step0 raw16756; decide +kernel
      have hl : raw16756step0Labels = raw16756Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16756 raw16756Labels permutation153 permutation3
    mixedMoment B raw16756step0 raw16756step0Labels = mixedMoment B raw16756step1 raw16756step1Labels := by
      have ha : raw16756step1 = raw16756step0 := by apply Matrix.ext; unfold raw16756step1 raw16756step0; decide +kernel
      have hl : raw16756step0Labels = labelEmbedding6 ∘ raw16756step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16756step0 raw16756step0Labels raw16756step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5181 node5181Labels := by rfl

def raw16757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16757step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16757 raw16757Labels = mixedMoment B node5348 node5348Labels := by
  calc
    mixedMoment B raw16757 raw16757Labels = mixedMoment B raw16757step0 raw16757step0Labels := by
      have ha : raw16757step0 = (fun i j => raw16757 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16757step0 raw16757; decide +kernel
      have hl : raw16757step0Labels = raw16757Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16757 raw16757Labels permutation265 permutation2
    _ = mixedMoment B node5348 node5348Labels := by rfl

def raw16758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16758step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16758step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16758step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16758step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16758 raw16758Labels = mixedMoment B node5350 node5350Labels := by
  calc
    mixedMoment B raw16758 raw16758Labels = mixedMoment B raw16758step0 raw16758step0Labels := by
      have ha : raw16758step0 = (fun i j => raw16758 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16758step0 raw16758; decide +kernel
      have hl : raw16758step0Labels = raw16758Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16758 raw16758Labels permutation587 permutation3
    mixedMoment B raw16758step0 raw16758step0Labels = mixedMoment B raw16758step1 raw16758step1Labels := by
      have ha : raw16758step1 = -raw16758step0 := by apply Matrix.ext; change ∀ i j, raw16758step1 i j = -(raw16758step0 i j); unfold raw16758step1 raw16758step0; decide +kernel
      have hl : raw16758step1Labels = raw16758step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16758step1 raw16758step1Labels = mixedMoment B raw16758step2 raw16758step2Labels := by
      have ha : raw16758step2 = raw16758step1 := by apply Matrix.ext; unfold raw16758step2 raw16758step1; decide +kernel
      have hl : raw16758step1Labels = labelEmbedding6 ∘ raw16758step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16758step1 raw16758step1Labels raw16758step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5350 node5350Labels := by rfl

def raw16759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16759step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16759step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16759step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16759step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16759step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16759 raw16759Labels = mixedMoment B node5350 node5350Labels := by
  calc
    mixedMoment B raw16759 raw16759Labels = mixedMoment B raw16759step0 raw16759step0Labels := by
      have ha : raw16759step0 = (fun i j => raw16759 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16759step0 raw16759; decide +kernel
      have hl : raw16759step0Labels = raw16759Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16759 raw16759Labels permutation582 permutation3
    mixedMoment B raw16759step0 raw16759step0Labels = mixedMoment B raw16759step1 raw16759step1Labels := by
      have ha : raw16759step1 = -raw16759step0 := by apply Matrix.ext; change ∀ i j, raw16759step1 i j = -(raw16759step0 i j); unfold raw16759step1 raw16759step0; decide +kernel
      have hl : raw16759step1Labels = raw16759step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16759step1 raw16759step1Labels = mixedMoment B raw16759step2 raw16759step2Labels := by
      have ha : raw16759step2 = raw16759step1 := by apply Matrix.ext; unfold raw16759step2 raw16759step1; decide +kernel
      have hl : raw16759step1Labels = labelEmbedding6 ∘ raw16759step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16759step1 raw16759step1Labels raw16759step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5350 node5350Labels := by rfl

def raw16760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw16760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16760step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16760step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16760step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16760step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16760step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16760 raw16760Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw16760 raw16760Labels = mixedMoment B raw16760step0 raw16760step0Labels := by
      have ha : raw16760step0 = (fun i j => raw16760 (permutation584 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16760step0 raw16760; decide +kernel
      have hl : raw16760step0Labels = raw16760Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16760 raw16760Labels permutation584 permutation3
    mixedMoment B raw16760step0 raw16760step0Labels = mixedMoment B raw16760step1 raw16760step1Labels := by
      have ha : raw16760step1 = -raw16760step0 := by apply Matrix.ext; change ∀ i j, raw16760step1 i j = -(raw16760step0 i j); unfold raw16760step1 raw16760step0; decide +kernel
      have hl : raw16760step1Labels = raw16760step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16760step1 raw16760step1Labels = mixedMoment B raw16760step2 raw16760step2Labels := by
      have ha : raw16760step2 = raw16760step1 := by apply Matrix.ext; unfold raw16760step2 raw16760step1; decide +kernel
      have hl : raw16760step1Labels = labelEmbedding6 ∘ raw16760step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16760step1 raw16760step1Labels raw16760step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw16761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw16761step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16761step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw16761step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16761step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw16761step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16761 raw16761Labels = mixedMoment B node5064 node5064Labels := by
  calc
    mixedMoment B raw16761 raw16761Labels = mixedMoment B raw16761step0 raw16761step0Labels := by
      have ha : raw16761step0 = (fun i j => raw16761 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16761step0 raw16761; decide +kernel
      have hl : raw16761step0Labels = raw16761Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16761 raw16761Labels permutation682 permutation3
    mixedMoment B raw16761step0 raw16761step0Labels = mixedMoment B raw16761step1 raw16761step1Labels := by
      have ha : raw16761step1 = -raw16761step0 := by apply Matrix.ext; change ∀ i j, raw16761step1 i j = -(raw16761step0 i j); unfold raw16761step1 raw16761step0; decide +kernel
      have hl : raw16761step1Labels = raw16761step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16761step1 raw16761step1Labels = mixedMoment B raw16761step2 raw16761step2Labels := by
      have ha : raw16761step2 = raw16761step1 := by apply Matrix.ext; unfold raw16761step2 raw16761step1; decide +kernel
      have hl : raw16761step1Labels = labelEmbedding6 ∘ raw16761step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16761step1 raw16761step1Labels raw16761step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5064 node5064Labels := by rfl

def raw16762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16762step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw16762step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16762step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16762step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16762step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16762step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16762 raw16762Labels = mixedMoment B node5067 node5067Labels := by
  calc
    mixedMoment B raw16762 raw16762Labels = mixedMoment B raw16762step0 raw16762step0Labels := by
      have ha : raw16762step0 = (fun i j => raw16762 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16762step0 raw16762; decide +kernel
      have hl : raw16762step0Labels = raw16762Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16762 raw16762Labels permutation682 permutation3
    mixedMoment B raw16762step0 raw16762step0Labels = mixedMoment B raw16762step1 raw16762step1Labels := by
      have ha : raw16762step1 = -raw16762step0 := by apply Matrix.ext; change ∀ i j, raw16762step1 i j = -(raw16762step0 i j); unfold raw16762step1 raw16762step0; decide +kernel
      have hl : raw16762step1Labels = raw16762step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16762step1 raw16762step1Labels = mixedMoment B raw16762step2 raw16762step2Labels := by
      have ha : raw16762step2 = raw16762step1 := by apply Matrix.ext; unfold raw16762step2 raw16762step1; decide +kernel
      have hl : raw16762step1Labels = labelEmbedding6 ∘ raw16762step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16762step1 raw16762step1Labels raw16762step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5067 node5067Labels := by rfl

def raw16763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16763step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16763step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16763step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16763step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16763 raw16763Labels = mixedMoment B node5071 node5071Labels := by
  calc
    mixedMoment B raw16763 raw16763Labels = mixedMoment B raw16763step0 raw16763step0Labels := by
      have ha : raw16763step0 = (fun i j => raw16763 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16763step0 raw16763; decide +kernel
      have hl : raw16763step0Labels = raw16763Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16763 raw16763Labels permutation686 permutation3
    mixedMoment B raw16763step0 raw16763step0Labels = mixedMoment B raw16763step1 raw16763step1Labels := by
      have ha : raw16763step1 = -raw16763step0 := by apply Matrix.ext; change ∀ i j, raw16763step1 i j = -(raw16763step0 i j); unfold raw16763step1 raw16763step0; decide +kernel
      have hl : raw16763step1Labels = raw16763step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16763step1 raw16763step1Labels = mixedMoment B raw16763step2 raw16763step2Labels := by
      have ha : raw16763step2 = raw16763step1 := by apply Matrix.ext; unfold raw16763step2 raw16763step1; decide +kernel
      have hl : raw16763step1Labels = labelEmbedding6 ∘ raw16763step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16763step1 raw16763step1Labels raw16763step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5071 node5071Labels := by rfl

def raw16764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16764step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16764step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16764step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16764step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16764step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16764step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16764 raw16764Labels = mixedMoment B node5071 node5071Labels := by
  calc
    mixedMoment B raw16764 raw16764Labels = mixedMoment B raw16764step0 raw16764step0Labels := by
      have ha : raw16764step0 = (fun i j => raw16764 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16764step0 raw16764; decide +kernel
      have hl : raw16764step0Labels = raw16764Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16764 raw16764Labels permutation680 permutation3
    mixedMoment B raw16764step0 raw16764step0Labels = mixedMoment B raw16764step1 raw16764step1Labels := by
      have ha : raw16764step1 = -raw16764step0 := by apply Matrix.ext; change ∀ i j, raw16764step1 i j = -(raw16764step0 i j); unfold raw16764step1 raw16764step0; decide +kernel
      have hl : raw16764step1Labels = raw16764step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16764step1 raw16764step1Labels = mixedMoment B raw16764step2 raw16764step2Labels := by
      have ha : raw16764step2 = raw16764step1 := by apply Matrix.ext; unfold raw16764step2 raw16764step1; decide +kernel
      have hl : raw16764step1Labels = labelEmbedding6 ∘ raw16764step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16764step1 raw16764step1Labels raw16764step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5071 node5071Labels := by rfl

def raw16765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw16765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw16765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16765step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16765step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16765step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16765step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16765step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16765 raw16765Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw16765 raw16765Labels = mixedMoment B raw16765step0 raw16765step0Labels := by
      have hz : ∀ j, raw16765 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16765step0 = (fun i j => raw16765 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16765step0 raw16765; decide +kernel
      have hl : raw16765step0Labels = raw16765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16765 raw16765Labels permutation520 hz
    mixedMoment B raw16765step0 raw16765step0Labels = mixedMoment B raw16765step1 raw16765step1Labels := by
      have ha : raw16765step1 = (fun i j => raw16765step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16765step1 raw16765step0; decide +kernel
      have hl : raw16765step1Labels = raw16765step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16765step0 raw16765step0Labels permutation145 permutation3
    mixedMoment B raw16765step1 raw16765step1Labels = mixedMoment B raw16765step2 raw16765step2Labels := by
      have ha : raw16765step2 = -raw16765step1 := by apply Matrix.ext; change ∀ i j, raw16765step2 i j = -(raw16765step1 i j); unfold raw16765step2 raw16765step1; decide +kernel
      have hl : raw16765step2Labels = raw16765step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16765step2 raw16765step2Labels = mixedMoment B raw16765step3 raw16765step3Labels := by
      have ha : raw16765step3 = raw16765step2 := by apply Matrix.ext; unfold raw16765step3 raw16765step2; decide +kernel
      have hl : raw16765step2Labels = labelEmbedding6 ∘ raw16765step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16765step2 raw16765step2Labels raw16765step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw16766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16766Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw16766step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16766step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw16766step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16766 raw16766Labels = mixedMoment B node3977 node3977Labels := by
  calc
    mixedMoment B raw16766 raw16766Labels = mixedMoment B raw16766step0 raw16766step0Labels := by
      have ha : raw16766step0 = (fun i j => raw16766 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16766step0 raw16766; decide +kernel
      have hl : raw16766step0Labels = raw16766Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16766 raw16766Labels permutation681 permutation3
    mixedMoment B raw16766step0 raw16766step0Labels = mixedMoment B raw16766step1 raw16766step1Labels := by
      have ha : raw16766step1 = -raw16766step0 := by apply Matrix.ext; change ∀ i j, raw16766step1 i j = -(raw16766step0 i j); unfold raw16766step1 raw16766step0; decide +kernel
      have hl : raw16766step1Labels = raw16766step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3977 node3977Labels := by rfl

def raw16767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16767Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16767step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16767step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16767step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16767 raw16767Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw16767 raw16767Labels = mixedMoment B raw16767step0 raw16767step0Labels := by
      have ha : raw16767step0 = (fun i j => raw16767 (permutation685 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16767step0 raw16767; decide +kernel
      have hl : raw16767step0Labels = raw16767Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16767 raw16767Labels permutation685 permutation3
    mixedMoment B raw16767step0 raw16767step0Labels = mixedMoment B raw16767step1 raw16767step1Labels := by
      have ha : raw16767step1 = -raw16767step0 := by apply Matrix.ext; change ∀ i j, raw16767step1 i j = -(raw16767step0 i j); unfold raw16767step1 raw16767step0; decide +kernel
      have hl : raw16767step1Labels = raw16767step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3978 node3978Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
