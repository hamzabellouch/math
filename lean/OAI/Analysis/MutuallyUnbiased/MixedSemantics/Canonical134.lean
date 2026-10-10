import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw17152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw17152Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17152step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw17152step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw17152step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17152 raw17152Labels = mixedMoment B node3911 node3911Labels := by
  calc
    mixedMoment B raw17152 raw17152Labels = mixedMoment B raw17152step0 raw17152step0Labels := by
      have hz : ∀ j, raw17152 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17152step0 = (fun i j => raw17152 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17152step0 raw17152; decide +kernel
      have hl : raw17152step0Labels = raw17152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17152 raw17152Labels permutation520 hz
    mixedMoment B raw17152step0 raw17152step0Labels = mixedMoment B raw17152step1 raw17152step1Labels := by
      have ha : raw17152step1 = (fun i j => raw17152step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17152step1 raw17152step0; decide +kernel
      have hl : raw17152step1Labels = raw17152step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17152step0 raw17152step0Labels permutation144 permutation3
    mixedMoment B raw17152step1 raw17152step1Labels = mixedMoment B raw17152step2 raw17152step2Labels := by
      have ha : raw17152step2 = -raw17152step1 := by apply Matrix.ext; change ∀ i j, raw17152step2 i j = -(raw17152step1 i j); unfold raw17152step2 raw17152step1; decide +kernel
      have hl : raw17152step2Labels = raw17152step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3911 node3911Labels := by rfl

def raw17153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw17153Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17153step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw17153step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17153step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw17153step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17153 raw17153Labels = mixedMoment B node4051 node4051Labels := by
  calc
    mixedMoment B raw17153 raw17153Labels = mixedMoment B raw17153step0 raw17153step0Labels := by
      have ha : raw17153step0 = (fun i j => raw17153 (permutation583 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17153step0 raw17153; decide +kernel
      have hl : raw17153step0Labels = raw17153Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17153 raw17153Labels permutation583 permutation3
    mixedMoment B raw17153step0 raw17153step0Labels = mixedMoment B raw17153step1 raw17153step1Labels := by
      have ha : raw17153step1 = -raw17153step0 := by apply Matrix.ext; change ∀ i j, raw17153step1 i j = -(raw17153step0 i j); unfold raw17153step1 raw17153step0; decide +kernel
      have hl : raw17153step1Labels = raw17153step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4051 node4051Labels := by rfl

def raw17154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17154Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw17154step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17154 raw17154Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw17154 raw17154Labels = mixedMoment B raw17154step0 raw17154step0Labels := by
      have ha : raw17154step0 = (fun i j => raw17154 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17154step0 raw17154; decide +kernel
      have hl : raw17154step0Labels = raw17154Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17154 raw17154Labels permutation182 permutation3
    _ = mixedMoment B node2694 node2694Labels := by rfl

def raw17155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17155Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17155step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17155step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17155step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17155 raw17155Labels = mixedMoment B node3794 node3794Labels := by
  calc
    mixedMoment B raw17155 raw17155Labels = mixedMoment B raw17155step0 raw17155step0Labels := by
      have ha : raw17155step0 = (fun i j => raw17155 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17155step0 raw17155; decide +kernel
      have hl : raw17155step0Labels = raw17155Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17155 raw17155Labels permutation676 permutation3
    mixedMoment B raw17155step0 raw17155step0Labels = mixedMoment B raw17155step1 raw17155step1Labels := by
      have ha : raw17155step1 = -raw17155step0 := by apply Matrix.ext; change ∀ i j, raw17155step1 i j = -(raw17155step0 i j); unfold raw17155step1 raw17155step0; decide +kernel
      have hl : raw17155step1Labels = raw17155step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3794 node3794Labels := by rfl

def raw17156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17156Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17156step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17156step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17156step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17156step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17156 raw17156Labels = mixedMoment B node3794 node3794Labels := by
  calc
    mixedMoment B raw17156 raw17156Labels = mixedMoment B raw17156step0 raw17156step0Labels := by
      have ha : raw17156step0 = (fun i j => raw17156 (permutation674 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17156step0 raw17156; decide +kernel
      have hl : raw17156step0Labels = raw17156Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17156 raw17156Labels permutation674 permutation3
    mixedMoment B raw17156step0 raw17156step0Labels = mixedMoment B raw17156step1 raw17156step1Labels := by
      have ha : raw17156step1 = -raw17156step0 := by apply Matrix.ext; change ∀ i j, raw17156step1 i j = -(raw17156step0 i j); unfold raw17156step1 raw17156step0; decide +kernel
      have hl : raw17156step1Labels = raw17156step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3794 node3794Labels := by rfl

def raw17157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw17157Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17157step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17157step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw17157step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17157step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw17157step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17157 raw17157Labels = mixedMoment B node3902 node3902Labels := by
  calc
    mixedMoment B raw17157 raw17157Labels = mixedMoment B raw17157step0 raw17157step0Labels := by
      have hz : ∀ j, raw17157 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17157step0 = (fun i j => raw17157 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17157step0 raw17157; decide +kernel
      have hl : raw17157step0Labels = raw17157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17157 raw17157Labels permutation520 hz
    mixedMoment B raw17157step0 raw17157step0Labels = mixedMoment B raw17157step1 raw17157step1Labels := by
      have ha : raw17157step1 = (fun i j => raw17157step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17157step1 raw17157step0; decide +kernel
      have hl : raw17157step1Labels = raw17157step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17157step0 raw17157step0Labels permutation137 permutation3
    mixedMoment B raw17157step1 raw17157step1Labels = mixedMoment B raw17157step2 raw17157step2Labels := by
      have ha : raw17157step2 = -raw17157step1 := by apply Matrix.ext; change ∀ i j, raw17157step2 i j = -(raw17157step1 i j); unfold raw17157step2 raw17157step1; decide +kernel
      have hl : raw17157step2Labels = raw17157step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3902 node3902Labels := by rfl

def raw17158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw17158Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17158step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw17158step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17158 raw17158Labels = mixedMoment B node4009 node4009Labels := by
  calc
    mixedMoment B raw17158 raw17158Labels = mixedMoment B raw17158step0 raw17158step0Labels := by
      have ha : raw17158step0 = (fun i j => raw17158 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17158step0 raw17158; decide +kernel
      have hl : raw17158step0Labels = raw17158Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17158 raw17158Labels permutation182 permutation3
    _ = mixedMoment B node4009 node4009Labels := by rfl

def raw17159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17159Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17159step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17159 raw17159Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw17159 raw17159Labels = mixedMoment B raw17159step0 raw17159step0Labels := by
      have ha : raw17159step0 = (fun i j => raw17159 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17159step0 raw17159; decide +kernel
      have hl : raw17159step0Labels = raw17159Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17159 raw17159Labels permutation158 permutation3
    _ = mixedMoment B node2553 node2553Labels := by rfl

def raw17160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17160Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17160step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17160step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17160step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17160 raw17160Labels = mixedMoment B node3779 node3779Labels := by
  calc
    mixedMoment B raw17160 raw17160Labels = mixedMoment B raw17160step0 raw17160step0Labels := by
      have ha : raw17160step0 = (fun i j => raw17160 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17160step0 raw17160; decide +kernel
      have hl : raw17160step0Labels = raw17160Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17160 raw17160Labels permutation681 permutation3
    mixedMoment B raw17160step0 raw17160step0Labels = mixedMoment B raw17160step1 raw17160step1Labels := by
      have ha : raw17160step1 = -raw17160step0 := by apply Matrix.ext; change ∀ i j, raw17160step1 i j = -(raw17160step0 i j); unfold raw17160step1 raw17160step0; decide +kernel
      have hl : raw17160step1Labels = raw17160step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3779 node3779Labels := by rfl

def raw17161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17161Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17161step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17161step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17161step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17161 raw17161Labels = mixedMoment B node3781 node3781Labels := by
  calc
    mixedMoment B raw17161 raw17161Labels = mixedMoment B raw17161step0 raw17161step0Labels := by
      have ha : raw17161step0 = (fun i j => raw17161 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17161step0 raw17161; decide +kernel
      have hl : raw17161step0Labels = raw17161Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17161 raw17161Labels permutation680 permutation3
    mixedMoment B raw17161step0 raw17161step0Labels = mixedMoment B raw17161step1 raw17161step1Labels := by
      have ha : raw17161step1 = -raw17161step0 := by apply Matrix.ext; change ∀ i j, raw17161step1 i j = -(raw17161step0 i j); unfold raw17161step1 raw17161step0; decide +kernel
      have hl : raw17161step1Labels = raw17161step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3781 node3781Labels := by rfl

def raw17162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw17162Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17162step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17162step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17162step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17162 raw17162Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw17162 raw17162Labels = mixedMoment B raw17162step0 raw17162step0Labels := by
      have hz : ∀ j, raw17162 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17162step0 = (fun i j => raw17162 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17162step0 raw17162; decide +kernel
      have hl : raw17162step0Labels = raw17162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17162 raw17162Labels permutation520 hz
    mixedMoment B raw17162step0 raw17162step0Labels = mixedMoment B raw17162step1 raw17162step1Labels := by
      have ha : raw17162step1 = (fun i j => raw17162step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17162step1 raw17162step0; decide +kernel
      have hl : raw17162step1Labels = raw17162step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17162step0 raw17162step0Labels permutation145 permutation3
    mixedMoment B raw17162step1 raw17162step1Labels = mixedMoment B raw17162step2 raw17162step2Labels := by
      have ha : raw17162step2 = -raw17162step1 := by apply Matrix.ext; change ∀ i j, raw17162step2 i j = -(raw17162step1 i j); unfold raw17162step2 raw17162step1; decide +kernel
      have hl : raw17162step2Labels = raw17162step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw17163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw17163Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17163step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17163 raw17163Labels = mixedMoment B node3992 node3992Labels := by
  calc
    mixedMoment B raw17163 raw17163Labels = mixedMoment B raw17163step0 raw17163step0Labels := by
      have ha : raw17163step0 = (fun i j => raw17163 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17163step0 raw17163; decide +kernel
      have hl : raw17163step0Labels = raw17163Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17163 raw17163Labels permutation158 permutation3
    _ = mixedMoment B node3992 node3992Labels := by rfl

def raw17164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17164Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17164step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17164 raw17164Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw17164 raw17164Labels = mixedMoment B raw17164step0 raw17164step0Labels := by
      have ha : raw17164step0 = (fun i j => raw17164 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17164step0 raw17164; decide +kernel
      have hl : raw17164step0Labels = raw17164Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17164 raw17164Labels permutation152 permutation3
    _ = mixedMoment B node2553 node2553Labels := by rfl

def raw17165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17165step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17165step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17165step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17165 raw17165Labels = mixedMoment B node3779 node3779Labels := by
  calc
    mixedMoment B raw17165 raw17165Labels = mixedMoment B raw17165step0 raw17165step0Labels := by
      have ha : raw17165step0 = (fun i j => raw17165 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17165step0 raw17165; decide +kernel
      have hl : raw17165step0Labels = raw17165Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17165 raw17165Labels permutation687 permutation3
    mixedMoment B raw17165step0 raw17165step0Labels = mixedMoment B raw17165step1 raw17165step1Labels := by
      have ha : raw17165step1 = -raw17165step0 := by apply Matrix.ext; change ∀ i j, raw17165step1 i j = -(raw17165step0 i j); unfold raw17165step1 raw17165step0; decide +kernel
      have hl : raw17165step1Labels = raw17165step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3779 node3779Labels := by rfl

def raw17166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17166step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17166step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17166step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17166 raw17166Labels = mixedMoment B node3781 node3781Labels := by
  calc
    mixedMoment B raw17166 raw17166Labels = mixedMoment B raw17166step0 raw17166step0Labels := by
      have ha : raw17166step0 = (fun i j => raw17166 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17166step0 raw17166; decide +kernel
      have hl : raw17166step0Labels = raw17166Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17166 raw17166Labels permutation686 permutation3
    mixedMoment B raw17166step0 raw17166step0Labels = mixedMoment B raw17166step1 raw17166step1Labels := by
      have ha : raw17166step1 = -raw17166step0 := by apply Matrix.ext; change ∀ i j, raw17166step1 i j = -(raw17166step0 i j); unfold raw17166step1 raw17166step0; decide +kernel
      have hl : raw17166step1Labels = raw17166step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3781 node3781Labels := by rfl

def raw17167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw17167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17167step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17167step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17167step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17167 raw17167Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw17167 raw17167Labels = mixedMoment B raw17167step0 raw17167step0Labels := by
      have hz : ∀ j, raw17167 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17167step0 = (fun i j => raw17167 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17167step0 raw17167; decide +kernel
      have hl : raw17167step0Labels = raw17167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17167 raw17167Labels permutation520 hz
    mixedMoment B raw17167step0 raw17167step0Labels = mixedMoment B raw17167step1 raw17167step1Labels := by
      have ha : raw17167step1 = (fun i j => raw17167step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17167step1 raw17167step0; decide +kernel
      have hl : raw17167step1Labels = raw17167step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17167step0 raw17167step0Labels permutation151 permutation3
    mixedMoment B raw17167step1 raw17167step1Labels = mixedMoment B raw17167step2 raw17167step2Labels := by
      have ha : raw17167step2 = -raw17167step1 := by apply Matrix.ext; change ∀ i j, raw17167step2 i j = -(raw17167step1 i j); unfold raw17167step2 raw17167step1; decide +kernel
      have hl : raw17167step2Labels = raw17167step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw17168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw17168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17168step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17168step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17168 raw17168Labels = mixedMoment B node3992 node3992Labels := by
  calc
    mixedMoment B raw17168 raw17168Labels = mixedMoment B raw17168step0 raw17168step0Labels := by
      have ha : raw17168step0 = (fun i j => raw17168 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17168step0 raw17168; decide +kernel
      have hl : raw17168step0Labels = raw17168Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17168 raw17168Labels permutation152 permutation3
    _ = mixedMoment B node3992 node3992Labels := by rfl

def raw17169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw17169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17169step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw17169step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17169 raw17169Labels = mixedMoment B node2541 node2541Labels := by
  calc
    mixedMoment B raw17169 raw17169Labels = mixedMoment B raw17169step0 raw17169step0Labels := by
      have ha : raw17169step0 = (fun i j => raw17169 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17169step0 raw17169; decide +kernel
      have hl : raw17169step0Labels = raw17169Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17169 raw17169Labels permutation152 permutation3
    _ = mixedMoment B node2541 node2541Labels := by rfl

def raw17170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw17170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17170step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17170step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17170step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17170 raw17170Labels = mixedMoment B node3647 node3647Labels := by
  calc
    mixedMoment B raw17170 raw17170Labels = mixedMoment B raw17170step0 raw17170step0Labels := by
      have ha : raw17170step0 = (fun i j => raw17170 (permutation583 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17170step0 raw17170; decide +kernel
      have hl : raw17170step0Labels = raw17170Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17170 raw17170Labels permutation583 permutation3
    mixedMoment B raw17170step0 raw17170step0Labels = mixedMoment B raw17170step1 raw17170step1Labels := by
      have ha : raw17170step1 = -raw17170step0 := by apply Matrix.ext; change ∀ i j, raw17170step1 i j = -(raw17170step0 i j); unfold raw17170step1 raw17170step0; decide +kernel
      have hl : raw17170step1Labels = raw17170step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3647 node3647Labels := by rfl

def raw17171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw17171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17171step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17171step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17171step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17171 raw17171Labels = mixedMoment B node3651 node3651Labels := by
  calc
    mixedMoment B raw17171 raw17171Labels = mixedMoment B raw17171step0 raw17171step0Labels := by
      have ha : raw17171step0 = (fun i j => raw17171 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17171step0 raw17171; decide +kernel
      have hl : raw17171step0Labels = raw17171Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17171 raw17171Labels permutation587 permutation3
    mixedMoment B raw17171step0 raw17171step0Labels = mixedMoment B raw17171step1 raw17171step1Labels := by
      have ha : raw17171step1 = -raw17171step0 := by apply Matrix.ext; change ∀ i j, raw17171step1 i j = -(raw17171step0 i j); unfold raw17171step1 raw17171step0; decide +kernel
      have hl : raw17171step1Labels = raw17171step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3651 node3651Labels := by rfl

def raw17172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -2, 0]]
def raw17172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17172step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17172step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17172step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17172 raw17172Labels = mixedMoment B node3651 node3651Labels := by
  calc
    mixedMoment B raw17172 raw17172Labels = mixedMoment B raw17172step0 raw17172step0Labels := by
      have ha : raw17172step0 = (fun i j => raw17172 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17172step0 raw17172; decide +kernel
      have hl : raw17172step0Labels = raw17172Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17172 raw17172Labels permutation582 permutation3
    mixedMoment B raw17172step0 raw17172step0Labels = mixedMoment B raw17172step1 raw17172step1Labels := by
      have ha : raw17172step1 = -raw17172step0 := by apply Matrix.ext; change ∀ i j, raw17172step1 i j = -(raw17172step0 i j); unfold raw17172step1 raw17172step0; decide +kernel
      have hl : raw17172step1Labels = raw17172step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3651 node3651Labels := by rfl

def raw17173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw17173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17173step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17173step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17173step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17173 raw17173Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw17173 raw17173Labels = mixedMoment B raw17173step0 raw17173step0Labels := by
      have ha : raw17173step0 = (fun i j => raw17173 (permutation584 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17173step0 raw17173; decide +kernel
      have hl : raw17173step0Labels = raw17173Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17173 raw17173Labels permutation584 permutation3
    mixedMoment B raw17173step0 raw17173step0Labels = mixedMoment B raw17173step1 raw17173step1Labels := by
      have ha : raw17173step1 = -raw17173step0 := by apply Matrix.ext; change ∀ i j, raw17173step1 i j = -(raw17173step0 i j); unfold raw17173step1 raw17173step0; decide +kernel
      have hl : raw17173step1Labels = raw17173step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3800 node3800Labels := by rfl

def raw17174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw17174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17174step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw17174step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17174step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw17174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17174 raw17174Labels = mixedMoment B node1897 node1897Labels := by
  calc
    mixedMoment B raw17174 raw17174Labels = mixedMoment B raw17174step0 raw17174step0Labels := by
      have ha : raw17174step0 = (fun i j => raw17174 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17174step0 raw17174; decide +kernel
      have hl : raw17174step0Labels = raw17174Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17174 raw17174Labels permutation682 permutation3
    mixedMoment B raw17174step0 raw17174step0Labels = mixedMoment B raw17174step1 raw17174step1Labels := by
      have ha : raw17174step1 = -raw17174step0 := by apply Matrix.ext; change ∀ i j, raw17174step1 i j = -(raw17174step0 i j); unfold raw17174step1 raw17174step0; decide +kernel
      have hl : raw17174step1Labels = raw17174step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1897 node1897Labels := by rfl

def raw17175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw17175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17175step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17175step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17175 raw17175Labels = mixedMoment B node1901 node1901Labels := by
  calc
    mixedMoment B raw17175 raw17175Labels = mixedMoment B raw17175step0 raw17175step0Labels := by
      have ha : raw17175step0 = (fun i j => raw17175 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17175step0 raw17175; decide +kernel
      have hl : raw17175step0Labels = raw17175Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17175 raw17175Labels permutation681 permutation3
    mixedMoment B raw17175step0 raw17175step0Labels = mixedMoment B raw17175step1 raw17175step1Labels := by
      have ha : raw17175step1 = -raw17175step0 := by apply Matrix.ext; change ∀ i j, raw17175step1 i j = -(raw17175step0 i j); unfold raw17175step1 raw17175step0; decide +kernel
      have hl : raw17175step1Labels = raw17175step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1901 node1901Labels := by rfl

def raw17176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw17176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17176step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17176step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17176 raw17176Labels = mixedMoment B node1909 node1909Labels := by
  calc
    mixedMoment B raw17176 raw17176Labels = mixedMoment B raw17176step0 raw17176step0Labels := by
      have ha : raw17176step0 = (fun i j => raw17176 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17176step0 raw17176; decide +kernel
      have hl : raw17176step0Labels = raw17176Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17176 raw17176Labels permutation686 permutation3
    mixedMoment B raw17176step0 raw17176step0Labels = mixedMoment B raw17176step1 raw17176step1Labels := by
      have ha : raw17176step1 = -raw17176step0 := by apply Matrix.ext; change ∀ i j, raw17176step1 i j = -(raw17176step0 i j); unfold raw17176step1 raw17176step0; decide +kernel
      have hl : raw17176step1Labels = raw17176step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1909 node1909Labels := by rfl

def raw17177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -3, 0]]
def raw17177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17177step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17177step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17177step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17177 raw17177Labels = mixedMoment B node1909 node1909Labels := by
  calc
    mixedMoment B raw17177 raw17177Labels = mixedMoment B raw17177step0 raw17177step0Labels := by
      have ha : raw17177step0 = (fun i j => raw17177 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17177step0 raw17177; decide +kernel
      have hl : raw17177step0Labels = raw17177Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17177 raw17177Labels permutation680 permutation3
    mixedMoment B raw17177step0 raw17177step0Labels = mixedMoment B raw17177step1 raw17177step1Labels := by
      have ha : raw17177step1 = -raw17177step0 := by apply Matrix.ext; change ∀ i j, raw17177step1 i j = -(raw17177step0 i j); unfold raw17177step1 raw17177step0; decide +kernel
      have hl : raw17177step1Labels = raw17177step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1909 node1909Labels := by rfl

def raw17178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw17178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw17178step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17178step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17178 raw17178Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw17178 raw17178Labels = mixedMoment B raw17178step0 raw17178step0Labels := by
      have hz : ∀ j, raw17178 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17178step0 = (fun i j => raw17178 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17178step0 raw17178; decide +kernel
      have hl : raw17178step0Labels = raw17178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17178 raw17178Labels permutation520 hz
    mixedMoment B raw17178step0 raw17178step0Labels = mixedMoment B raw17178step1 raw17178step1Labels := by
      have ha : raw17178step1 = (fun i j => raw17178step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17178step1 raw17178step0; decide +kernel
      have hl : raw17178step1Labels = raw17178step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17178step0 raw17178step0Labels permutation145 permutation3
    mixedMoment B raw17178step1 raw17178step1Labels = mixedMoment B raw17178step2 raw17178step2Labels := by
      have ha : raw17178step2 = -raw17178step1 := by apply Matrix.ext; change ∀ i j, raw17178step2 i j = -(raw17178step1 i j); unfold raw17178step2 raw17178step1; decide +kernel
      have hl : raw17178step2Labels = raw17178step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2244 node2244Labels := by rfl

def raw17179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17179Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17179step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17179step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17179step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17179 raw17179Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw17179 raw17179Labels = mixedMoment B raw17179step0 raw17179step0Labels := by
      have ha : raw17179step0 = (fun i j => raw17179 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17179step0 raw17179; decide +kernel
      have hl : raw17179step0Labels = raw17179Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17179 raw17179Labels permutation681 permutation2
    mixedMoment B raw17179step0 raw17179step0Labels = mixedMoment B raw17179step1 raw17179step1Labels := by
      have ha : raw17179step1 = -raw17179step0 := by apply Matrix.ext; change ∀ i j, raw17179step1 i j = -(raw17179step0 i j); unfold raw17179step1 raw17179step0; decide +kernel
      have hl : raw17179step1Labels = raw17179step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw17180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17180Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17180step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17180step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17180step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17180 raw17180Labels = mixedMoment B node5408 node5408Labels := by
  calc
    mixedMoment B raw17180 raw17180Labels = mixedMoment B raw17180step0 raw17180step0Labels := by
      have ha : raw17180step0 = (fun i j => raw17180 (permutation685 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17180step0 raw17180; decide +kernel
      have hl : raw17180step0Labels = raw17180Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17180 raw17180Labels permutation685 permutation2
    mixedMoment B raw17180step0 raw17180step0Labels = mixedMoment B raw17180step1 raw17180step1Labels := by
      have ha : raw17180step1 = -raw17180step0 := by apply Matrix.ext; change ∀ i j, raw17180step1 i j = -(raw17180step0 i j); unfold raw17180step1 raw17180step0; decide +kernel
      have hl : raw17180step1Labels = raw17180step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5408 node5408Labels := by rfl

def raw17181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17181Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17181step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17181step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17181 raw17181Labels = mixedMoment B node5408 node5408Labels := by
  calc
    mixedMoment B raw17181 raw17181Labels = mixedMoment B raw17181step0 raw17181step0Labels := by
      have ha : raw17181step0 = (fun i j => raw17181 (permutation679 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17181step0 raw17181; decide +kernel
      have hl : raw17181step0Labels = raw17181Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17181 raw17181Labels permutation679 permutation2
    mixedMoment B raw17181step0 raw17181step0Labels = mixedMoment B raw17181step1 raw17181step1Labels := by
      have ha : raw17181step1 = -raw17181step0 := by apply Matrix.ext; change ∀ i j, raw17181step1 i j = -(raw17181step0 i j); unfold raw17181step1 raw17181step0; decide +kernel
      have hl : raw17181step1Labels = raw17181step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5408 node5408Labels := by rfl

def raw17182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17182step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17182step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17182step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17182 raw17182Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw17182 raw17182Labels = mixedMoment B raw17182step0 raw17182step0Labels := by
      have ha : raw17182step0 = (fun i j => raw17182 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17182step0 raw17182; decide +kernel
      have hl : raw17182step0Labels = raw17182Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17182 raw17182Labels permutation674 permutation7
    mixedMoment B raw17182step0 raw17182step0Labels = mixedMoment B raw17182step1 raw17182step1Labels := by
      have ha : raw17182step1 = raw17182step0 := by apply Matrix.ext; unfold raw17182step1 raw17182step0; decide +kernel
      have hl : raw17182step0Labels = labelEmbedding10 ∘ raw17182step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17182step0 raw17182step0Labels raw17182step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw17183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17183Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17183step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17183step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17183step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17183 raw17183Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw17183 raw17183Labels = mixedMoment B raw17183step0 raw17183step0Labels := by
      have ha : raw17183step0 = (fun i j => raw17183 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17183step0 raw17183; decide +kernel
      have hl : raw17183step0Labels = raw17183Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17183 raw17183Labels permutation674 permutation7
    mixedMoment B raw17183step0 raw17183step0Labels = mixedMoment B raw17183step1 raw17183step1Labels := by
      have ha : raw17183step1 = raw17183step0 := by apply Matrix.ext; unfold raw17183step1 raw17183step0; decide +kernel
      have hl : raw17183step0Labels = labelEmbedding10 ∘ raw17183step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17183step0 raw17183step0Labels raw17183step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw17184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17184step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17184step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17184step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17184step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17184 raw17184Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw17184 raw17184Labels = mixedMoment B raw17184step0 raw17184step0Labels := by
      have hz : ∀ j, raw17184 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw17184step0 = (fun i j => raw17184 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw17184step0 raw17184; decide +kernel
      have hl : raw17184step0Labels = raw17184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17184 raw17184Labels permutation265 hz
    mixedMoment B raw17184step0 raw17184step0Labels = mixedMoment B raw17184step1 raw17184step1Labels := by
      have ha : raw17184step1 = (fun i j => raw17184step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17184step1 raw17184step0; decide +kernel
      have hl : raw17184step1Labels = raw17184step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17184step0 raw17184step0Labels permutation32 permutation3
    mixedMoment B raw17184step1 raw17184step1Labels = mixedMoment B raw17184step2 raw17184step2Labels := by
      have ha : raw17184step2 = raw17184step1 := by apply Matrix.ext; unfold raw17184step2 raw17184step1; decide +kernel
      have hl : raw17184step1Labels = labelEmbedding6 ∘ raw17184step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17184step1 raw17184step1Labels raw17184step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw17185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17185step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17185step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17185step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17185step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17185 raw17185Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw17185 raw17185Labels = mixedMoment B raw17185step0 raw17185step0Labels := by
      have ha : raw17185step0 = (fun i j => raw17185 (permutation273 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17185step0 raw17185; decide +kernel
      have hl : raw17185step0Labels = raw17185Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17185 raw17185Labels permutation273 permutation3
    mixedMoment B raw17185step0 raw17185step0Labels = mixedMoment B raw17185step1 raw17185step1Labels := by
      have ha : raw17185step1 = raw17185step0 := by apply Matrix.ext; unfold raw17185step1 raw17185step0; decide +kernel
      have hl : raw17185step0Labels = labelEmbedding6 ∘ raw17185step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17185step0 raw17185step0Labels raw17185step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw17186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17186step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17186step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17186step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17186 raw17186Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw17186 raw17186Labels = mixedMoment B raw17186step0 raw17186step0Labels := by
      have ha : raw17186step0 = (fun i j => raw17186 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17186step0 raw17186; decide +kernel
      have hl : raw17186step0Labels = raw17186Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17186 raw17186Labels permutation680 permutation2
    mixedMoment B raw17186step0 raw17186step0Labels = mixedMoment B raw17186step1 raw17186step1Labels := by
      have ha : raw17186step1 = -raw17186step0 := by apply Matrix.ext; change ∀ i j, raw17186step1 i j = -(raw17186step0 i j); unfold raw17186step1 raw17186step0; decide +kernel
      have hl : raw17186step1Labels = raw17186step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw17187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17187step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17187step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17187 raw17187Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw17187 raw17187Labels = mixedMoment B raw17187step0 raw17187step0Labels := by
      have ha : raw17187step0 = (fun i j => raw17187 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17187step0 raw17187; decide +kernel
      have hl : raw17187step0Labels = raw17187Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17187 raw17187Labels permutation674 permutation7
    mixedMoment B raw17187step0 raw17187step0Labels = mixedMoment B raw17187step1 raw17187step1Labels := by
      have ha : raw17187step1 = raw17187step0 := by apply Matrix.ext; unfold raw17187step1 raw17187step0; decide +kernel
      have hl : raw17187step0Labels = labelEmbedding10 ∘ raw17187step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17187step0 raw17187step0Labels raw17187step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw17188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17188step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17188step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17188step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17188 raw17188Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw17188 raw17188Labels = mixedMoment B raw17188step0 raw17188step0Labels := by
      have ha : raw17188step0 = (fun i j => raw17188 (permutation163 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17188step0 raw17188; decide +kernel
      have hl : raw17188step0Labels = raw17188Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17188 raw17188Labels permutation163 permutation3
    mixedMoment B raw17188step0 raw17188step0Labels = mixedMoment B raw17188step1 raw17188step1Labels := by
      have ha : raw17188step1 = raw17188step0 := by apply Matrix.ext; unfold raw17188step1 raw17188step0; decide +kernel
      have hl : raw17188step0Labels = labelEmbedding6 ∘ raw17188step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17188step0 raw17188step0Labels raw17188step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5480 node5480Labels := by rfl

def raw17189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17189step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17189step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17189step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17189 raw17189Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw17189 raw17189Labels = mixedMoment B raw17189step0 raw17189step0Labels := by
      have ha : raw17189step0 = (fun i j => raw17189 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17189step0 raw17189; decide +kernel
      have hl : raw17189step0Labels = raw17189Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17189 raw17189Labels permutation267 permutation3
    mixedMoment B raw17189step0 raw17189step0Labels = mixedMoment B raw17189step1 raw17189step1Labels := by
      have ha : raw17189step1 = raw17189step0 := by apply Matrix.ext; unfold raw17189step1 raw17189step0; decide +kernel
      have hl : raw17189step0Labels = labelEmbedding6 ∘ raw17189step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17189step0 raw17189step0Labels raw17189step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw17190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17190step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17190step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17190step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17190step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17190 raw17190Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw17190 raw17190Labels = mixedMoment B raw17190step0 raw17190step0Labels := by
      have ha : raw17190step0 = (fun i j => raw17190 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17190step0 raw17190; decide +kernel
      have hl : raw17190step0Labels = raw17190Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17190 raw17190Labels permutation686 permutation2
    mixedMoment B raw17190step0 raw17190step0Labels = mixedMoment B raw17190step1 raw17190step1Labels := by
      have ha : raw17190step1 = -raw17190step0 := by apply Matrix.ext; change ∀ i j, raw17190step1 i j = -(raw17190step0 i j); unfold raw17190step1 raw17190step0; decide +kernel
      have hl : raw17190step1Labels = raw17190step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw17191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17191step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17191step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17191step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17191step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17191 raw17191Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw17191 raw17191Labels = mixedMoment B raw17191step0 raw17191step0Labels := by
      have ha : raw17191step0 = (fun i j => raw17191 (permutation676 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17191step0 raw17191; decide +kernel
      have hl : raw17191step0Labels = raw17191Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17191 raw17191Labels permutation676 permutation7
    mixedMoment B raw17191step0 raw17191step0Labels = mixedMoment B raw17191step1 raw17191step1Labels := by
      have ha : raw17191step1 = raw17191step0 := by apply Matrix.ext; unfold raw17191step1 raw17191step0; decide +kernel
      have hl : raw17191step0Labels = labelEmbedding10 ∘ raw17191step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17191step0 raw17191step0Labels raw17191step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw17192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17192step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17192step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17192 raw17192Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw17192 raw17192Labels = mixedMoment B raw17192step0 raw17192step0Labels := by
      have ha : raw17192step0 = (fun i j => raw17192 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17192step0 raw17192; decide +kernel
      have hl : raw17192step0Labels = raw17192Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17192 raw17192Labels permutation157 permutation3
    mixedMoment B raw17192step0 raw17192step0Labels = mixedMoment B raw17192step1 raw17192step1Labels := by
      have ha : raw17192step1 = raw17192step0 := by apply Matrix.ext; unfold raw17192step1 raw17192step0; decide +kernel
      have hl : raw17192step0Labels = labelEmbedding6 ∘ raw17192step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17192step0 raw17192step0Labels raw17192step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5480 node5480Labels := by rfl

def raw17193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw17193step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17193step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17193step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17193 raw17193Labels = mixedMoment B node5348 node5348Labels := by
  calc
    mixedMoment B raw17193 raw17193Labels = mixedMoment B raw17193step0 raw17193step0Labels := by
      have ha : raw17193step0 = (fun i j => raw17193 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17193step0 raw17193; decide +kernel
      have hl : raw17193step0Labels = raw17193Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17193 raw17193Labels permutation682 permutation2
    mixedMoment B raw17193step0 raw17193step0Labels = mixedMoment B raw17193step1 raw17193step1Labels := by
      have ha : raw17193step1 = -raw17193step0 := by apply Matrix.ext; change ∀ i j, raw17193step1 i j = -(raw17193step0 i j); unfold raw17193step1 raw17193step0; decide +kernel
      have hl : raw17193step1Labels = raw17193step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5348 node5348Labels := by rfl

def raw17194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17194step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17194step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17194step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17194 raw17194Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw17194 raw17194Labels = mixedMoment B raw17194step0 raw17194step0Labels := by
      have ha : raw17194step0 = (fun i j => raw17194 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17194step0 raw17194; decide +kernel
      have hl : raw17194step0Labels = raw17194Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17194 raw17194Labels permutation686 permutation2
    mixedMoment B raw17194step0 raw17194step0Labels = mixedMoment B raw17194step1 raw17194step1Labels := by
      have ha : raw17194step1 = -raw17194step0 := by apply Matrix.ext; change ∀ i j, raw17194step1 i j = -(raw17194step0 i j); unfold raw17194step1 raw17194step0; decide +kernel
      have hl : raw17194step1Labels = raw17194step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw17195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17195step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17195step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17195step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17195step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17195 raw17195Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw17195 raw17195Labels = mixedMoment B raw17195step0 raw17195step0Labels := by
      have ha : raw17195step0 = (fun i j => raw17195 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17195step0 raw17195; decide +kernel
      have hl : raw17195step0Labels = raw17195Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17195 raw17195Labels permutation680 permutation2
    mixedMoment B raw17195step0 raw17195step0Labels = mixedMoment B raw17195step1 raw17195step1Labels := by
      have ha : raw17195step1 = -raw17195step0 := by apply Matrix.ext; change ∀ i j, raw17195step1 i j = -(raw17195step0 i j); unfold raw17195step1 raw17195step0; decide +kernel
      have hl : raw17195step1Labels = raw17195step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw17196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw17196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17196step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17196step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17196 raw17196Labels = mixedMoment B node5471 node5471Labels := by
  calc
    mixedMoment B raw17196 raw17196Labels = mixedMoment B raw17196step0 raw17196step0Labels := by
      have ha : raw17196step0 = (fun i j => raw17196 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17196step0 raw17196; decide +kernel
      have hl : raw17196step0Labels = raw17196Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17196 raw17196Labels permutation584 permutation2
    mixedMoment B raw17196step0 raw17196step0Labels = mixedMoment B raw17196step1 raw17196step1Labels := by
      have ha : raw17196step1 = -raw17196step0 := by apply Matrix.ext; change ∀ i j, raw17196step1 i j = -(raw17196step0 i j); unfold raw17196step1 raw17196step0; decide +kernel
      have hl : raw17196step1Labels = raw17196step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5471 node5471Labels := by rfl

def raw17197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw17197step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17197step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17197step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17197 raw17197Labels = mixedMoment B node5067 node5067Labels := by
  calc
    mixedMoment B raw17197 raw17197Labels = mixedMoment B raw17197step0 raw17197step0Labels := by
      have ha : raw17197step0 = (fun i j => raw17197 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17197step0 raw17197; decide +kernel
      have hl : raw17197step0Labels = raw17197Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17197 raw17197Labels permutation682 permutation2
    mixedMoment B raw17197step0 raw17197step0Labels = mixedMoment B raw17197step1 raw17197step1Labels := by
      have ha : raw17197step1 = -raw17197step0 := by apply Matrix.ext; change ∀ i j, raw17197step1 i j = -(raw17197step0 i j); unfold raw17197step1 raw17197step0; decide +kernel
      have hl : raw17197step1Labels = raw17197step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5067 node5067Labels := by rfl

def raw17198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17198step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17198step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17198step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17198 raw17198Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw17198 raw17198Labels = mixedMoment B raw17198step0 raw17198step0Labels := by
      have ha : raw17198step0 = (fun i j => raw17198 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17198step0 raw17198; decide +kernel
      have hl : raw17198step0Labels = raw17198Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17198 raw17198Labels permutation686 permutation2
    mixedMoment B raw17198step0 raw17198step0Labels = mixedMoment B raw17198step1 raw17198step1Labels := by
      have ha : raw17198step1 = -raw17198step0 := by apply Matrix.ext; change ∀ i j, raw17198step1 i j = -(raw17198step0 i j); unfold raw17198step1 raw17198step0; decide +kernel
      have hl : raw17198step1Labels = raw17198step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw17199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17199step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17199step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17199step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17199 raw17199Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw17199 raw17199Labels = mixedMoment B raw17199step0 raw17199step0Labels := by
      have ha : raw17199step0 = (fun i j => raw17199 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17199step0 raw17199; decide +kernel
      have hl : raw17199step0Labels = raw17199Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17199 raw17199Labels permutation680 permutation2
    mixedMoment B raw17199step0 raw17199step0Labels = mixedMoment B raw17199step1 raw17199step1Labels := by
      have ha : raw17199step1 = -raw17199step0 := by apply Matrix.ext; change ∀ i j, raw17199step1 i j = -(raw17199step0 i j); unfold raw17199step1 raw17199step0; decide +kernel
      have hl : raw17199step1Labels = raw17199step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw17200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw17200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17200step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17200step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17200 raw17200Labels = mixedMoment B node5250 node5250Labels := by
  calc
    mixedMoment B raw17200 raw17200Labels = mixedMoment B raw17200step0 raw17200step0Labels := by
      have ha : raw17200step0 = (fun i j => raw17200 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17200step0 raw17200; decide +kernel
      have hl : raw17200step0Labels = raw17200Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17200 raw17200Labels permutation682 permutation2
    mixedMoment B raw17200step0 raw17200step0Labels = mixedMoment B raw17200step1 raw17200step1Labels := by
      have ha : raw17200step1 = -raw17200step0 := by apply Matrix.ext; change ∀ i j, raw17200step1 i j = -(raw17200step0 i j); unfold raw17200step1 raw17200step0; decide +kernel
      have hl : raw17200step1Labels = raw17200step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5250 node5250Labels := by rfl

def raw17201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17201Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17201step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17201step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17201step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17201 raw17201Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw17201 raw17201Labels = mixedMoment B raw17201step0 raw17201step0Labels := by
      have ha : raw17201step0 = (fun i j => raw17201 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17201step0 raw17201; decide +kernel
      have hl : raw17201step0Labels = raw17201Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17201 raw17201Labels permutation674 permutation7
    mixedMoment B raw17201step0 raw17201step0Labels = mixedMoment B raw17201step1 raw17201step1Labels := by
      have ha : raw17201step1 = raw17201step0 := by apply Matrix.ext; unfold raw17201step1 raw17201step0; decide +kernel
      have hl : raw17201step0Labels = labelEmbedding1 ∘ raw17201step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17201step0 raw17201step0Labels raw17201step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3812 node3812Labels := by rfl

def raw17202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17202Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17202step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17202step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17202step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17202 raw17202Labels = mixedMoment B node3806 node3806Labels := by
  calc
    mixedMoment B raw17202 raw17202Labels = mixedMoment B raw17202step0 raw17202step0Labels := by
      have ha : raw17202step0 = (fun i j => raw17202 (permutation675 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17202step0 raw17202; decide +kernel
      have hl : raw17202step0Labels = raw17202Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17202 raw17202Labels permutation675 permutation7
    mixedMoment B raw17202step0 raw17202step0Labels = mixedMoment B raw17202step1 raw17202step1Labels := by
      have ha : raw17202step1 = raw17202step0 := by apply Matrix.ext; unfold raw17202step1 raw17202step0; decide +kernel
      have hl : raw17202step0Labels = labelEmbedding1 ∘ raw17202step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17202step0 raw17202step0Labels raw17202step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3806 node3806Labels := by rfl

def raw17203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17203Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17203step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17203step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17203step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17203 raw17203Labels = mixedMoment B node3806 node3806Labels := by
  calc
    mixedMoment B raw17203 raw17203Labels = mixedMoment B raw17203step0 raw17203step0Labels := by
      have ha : raw17203step0 = (fun i j => raw17203 (permutation673 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17203step0 raw17203; decide +kernel
      have hl : raw17203step0Labels = raw17203Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17203 raw17203Labels permutation673 permutation7
    mixedMoment B raw17203step0 raw17203step0Labels = mixedMoment B raw17203step1 raw17203step1Labels := by
      have ha : raw17203step1 = raw17203step0 := by apply Matrix.ext; unfold raw17203step1 raw17203step0; decide +kernel
      have hl : raw17203step0Labels = labelEmbedding1 ∘ raw17203step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17203step0 raw17203step0Labels raw17203step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3806 node3806Labels := by rfl

def raw17204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17204step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17204step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17204step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17204 raw17204Labels = mixedMoment B node3851 node3851Labels := by
  calc
    mixedMoment B raw17204 raw17204Labels = mixedMoment B raw17204step0 raw17204step0Labels := by
      have ha : raw17204step0 = (fun i j => raw17204 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17204step0 raw17204; decide +kernel
      have hl : raw17204step0Labels = raw17204Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17204 raw17204Labels permutation674 permutation7
    mixedMoment B raw17204step0 raw17204step0Labels = mixedMoment B raw17204step1 raw17204step1Labels := by
      have ha : raw17204step1 = raw17204step0 := by apply Matrix.ext; unfold raw17204step1 raw17204step0; decide +kernel
      have hl : raw17204step0Labels = labelEmbedding1 ∘ raw17204step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17204step0 raw17204step0Labels raw17204step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3851 node3851Labels := by rfl

def raw17205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17205Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17205step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17205step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17205step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17205 raw17205Labels = mixedMoment B node3980 node3980Labels := by
  calc
    mixedMoment B raw17205 raw17205Labels = mixedMoment B raw17205step0 raw17205step0Labels := by
      have ha : raw17205step0 = (fun i j => raw17205 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17205step0 raw17205; decide +kernel
      have hl : raw17205step0Labels = raw17205Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17205 raw17205Labels permutation674 permutation7
    mixedMoment B raw17205step0 raw17205step0Labels = mixedMoment B raw17205step1 raw17205step1Labels := by
      have ha : raw17205step1 = raw17205step0 := by apply Matrix.ext; unfold raw17205step1 raw17205step0; decide +kernel
      have hl : raw17205step0Labels = labelEmbedding1 ∘ raw17205step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17205step0 raw17205step0Labels raw17205step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3980 node3980Labels := by rfl

def raw17206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17206Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17206step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw17206step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17206step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw17206step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17206step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw17206step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17206 raw17206Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw17206 raw17206Labels = mixedMoment B raw17206step0 raw17206step0Labels := by
      have hz : ∀ j, raw17206 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw17206step0 = (fun i j => raw17206 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw17206step0 raw17206; decide +kernel
      have hl : raw17206step0Labels = raw17206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17206 raw17206Labels permutation265 hz
    mixedMoment B raw17206step0 raw17206step0Labels = mixedMoment B raw17206step1 raw17206step1Labels := by
      have ha : raw17206step1 = (fun i j => raw17206step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17206step1 raw17206step0; decide +kernel
      have hl : raw17206step1Labels = raw17206step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17206step0 raw17206step0Labels permutation48 permutation5
    mixedMoment B raw17206step1 raw17206step1Labels = mixedMoment B raw17206step2 raw17206step2Labels := by
      have ha : raw17206step2 = -raw17206step1 := by apply Matrix.ext; change ∀ i j, raw17206step2 i j = -(raw17206step1 i j); unfold raw17206step2 raw17206step1; decide +kernel
      have hl : raw17206step2Labels = raw17206step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17206step2 raw17206step2Labels = mixedMoment B raw17206step3 raw17206step3Labels := by
      have ha : raw17206step3 = raw17206step2 := by apply Matrix.ext; unfold raw17206step3 raw17206step2; decide +kernel
      have hl : raw17206step2Labels = labelEmbedding1 ∘ raw17206step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17206step2 raw17206step2Labels raw17206step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

def raw17207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17207Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17207step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17207step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17207step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17207step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17207step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17207 raw17207Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw17207 raw17207Labels = mixedMoment B raw17207step0 raw17207step0Labels := by
      have ha : raw17207step0 = (fun i j => raw17207 (permutation282 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17207step0 raw17207; decide +kernel
      have hl : raw17207step0Labels = raw17207Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17207 raw17207Labels permutation282 permutation5
    mixedMoment B raw17207step0 raw17207step0Labels = mixedMoment B raw17207step1 raw17207step1Labels := by
      have ha : raw17207step1 = -raw17207step0 := by apply Matrix.ext; change ∀ i j, raw17207step1 i j = -(raw17207step0 i j); unfold raw17207step1 raw17207step0; decide +kernel
      have hl : raw17207step1Labels = raw17207step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17207step1 raw17207step1Labels = mixedMoment B raw17207step2 raw17207step2Labels := by
      have ha : raw17207step2 = raw17207step1 := by apply Matrix.ext; unfold raw17207step2 raw17207step1; decide +kernel
      have hl : raw17207step1Labels = labelEmbedding1 ∘ raw17207step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17207step1 raw17207step1Labels raw17207step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

def raw17208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17208Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17208step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17208step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17208step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17208 raw17208Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw17208 raw17208Labels = mixedMoment B raw17208step0 raw17208step0Labels := by
      have ha : raw17208step0 = (fun i j => raw17208 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17208step0 raw17208; decide +kernel
      have hl : raw17208step0Labels = raw17208Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17208 raw17208Labels permutation674 permutation7
    mixedMoment B raw17208step0 raw17208step0Labels = mixedMoment B raw17208step1 raw17208step1Labels := by
      have ha : raw17208step1 = raw17208step0 := by apply Matrix.ext; unfold raw17208step1 raw17208step0; decide +kernel
      have hl : raw17208step0Labels = labelEmbedding1 ∘ raw17208step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17208step0 raw17208step0Labels raw17208step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

def raw17209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17209Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17209step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17209step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17209step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17209 raw17209Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw17209 raw17209Labels = mixedMoment B raw17209step0 raw17209step0Labels := by
      have ha : raw17209step0 = (fun i j => raw17209 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17209step0 raw17209; decide +kernel
      have hl : raw17209step0Labels = raw17209Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17209 raw17209Labels permutation674 permutation7
    mixedMoment B raw17209step0 raw17209step0Labels = mixedMoment B raw17209step1 raw17209step1Labels := by
      have ha : raw17209step1 = raw17209step0 := by apply Matrix.ext; unfold raw17209step1 raw17209step0; decide +kernel
      have hl : raw17209step0Labels = labelEmbedding1 ∘ raw17209step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17209step0 raw17209step0Labels raw17209step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw17210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17210Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17210step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17210step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17210step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17210 raw17210Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw17210 raw17210Labels = mixedMoment B raw17210step0 raw17210step0Labels := by
      have ha : raw17210step0 = (fun i j => raw17210 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17210step0 raw17210; decide +kernel
      have hl : raw17210step0Labels = raw17210Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17210 raw17210Labels permutation674 permutation7
    mixedMoment B raw17210step0 raw17210step0Labels = mixedMoment B raw17210step1 raw17210step1Labels := by
      have ha : raw17210step1 = raw17210step0 := by apply Matrix.ext; unfold raw17210step1 raw17210step0; decide +kernel
      have hl : raw17210step0Labels = labelEmbedding1 ∘ raw17210step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17210step0 raw17210step0Labels raw17210step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw17211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17211Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17211step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17211step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17211step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17211step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17211step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17211 raw17211Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw17211 raw17211Labels = mixedMoment B raw17211step0 raw17211step0Labels := by
      have ha : raw17211step0 = (fun i j => raw17211 (permutation281 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17211step0 raw17211; decide +kernel
      have hl : raw17211step0Labels = raw17211Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17211 raw17211Labels permutation281 permutation5
    mixedMoment B raw17211step0 raw17211step0Labels = mixedMoment B raw17211step1 raw17211step1Labels := by
      have ha : raw17211step1 = -raw17211step0 := by apply Matrix.ext; change ∀ i j, raw17211step1 i j = -(raw17211step0 i j); unfold raw17211step1 raw17211step0; decide +kernel
      have hl : raw17211step1Labels = raw17211step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17211step1 raw17211step1Labels = mixedMoment B raw17211step2 raw17211step2Labels := by
      have ha : raw17211step2 = raw17211step1 := by apply Matrix.ext; unfold raw17211step2 raw17211step1; decide +kernel
      have hl : raw17211step1Labels = labelEmbedding1 ∘ raw17211step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17211step1 raw17211step1Labels raw17211step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

def raw17212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17212Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17212step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17212 raw17212Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw17212 raw17212Labels = mixedMoment B raw17212step0 raw17212step0Labels := by
      have ha : raw17212step0 = (fun i j => raw17212 (permutation676 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17212step0 raw17212; decide +kernel
      have hl : raw17212step0Labels = raw17212Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17212 raw17212Labels permutation676 permutation7
    mixedMoment B raw17212step0 raw17212step0Labels = mixedMoment B raw17212step1 raw17212step1Labels := by
      have ha : raw17212step1 = raw17212step0 := by apply Matrix.ext; unfold raw17212step1 raw17212step0; decide +kernel
      have hl : raw17212step0Labels = labelEmbedding1 ∘ raw17212step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17212step0 raw17212step0Labels raw17212step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

def raw17213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17213Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17213step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17213step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17213step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17213 raw17213Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw17213 raw17213Labels = mixedMoment B raw17213step0 raw17213step0Labels := by
      have ha : raw17213step0 = (fun i j => raw17213 (permutation676 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17213step0 raw17213; decide +kernel
      have hl : raw17213step0Labels = raw17213Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17213 raw17213Labels permutation676 permutation7
    mixedMoment B raw17213step0 raw17213step0Labels = mixedMoment B raw17213step1 raw17213step1Labels := by
      have ha : raw17213step1 = raw17213step0 := by apply Matrix.ext; unfold raw17213step1 raw17213step0; decide +kernel
      have hl : raw17213step0Labels = labelEmbedding1 ∘ raw17213step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17213step0 raw17213step0Labels raw17213step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw17214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17214Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17214step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17214step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17214step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17214 raw17214Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw17214 raw17214Labels = mixedMoment B raw17214step0 raw17214step0Labels := by
      have ha : raw17214step0 = (fun i j => raw17214 (permutation676 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17214step0 raw17214; decide +kernel
      have hl : raw17214step0Labels = raw17214Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17214 raw17214Labels permutation676 permutation7
    mixedMoment B raw17214step0 raw17214step0Labels = mixedMoment B raw17214step1 raw17214step1Labels := by
      have ha : raw17214step1 = raw17214step0 := by apply Matrix.ext; unfold raw17214step1 raw17214step0; decide +kernel
      have hl : raw17214step0Labels = labelEmbedding1 ∘ raw17214step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17214step0 raw17214step0Labels raw17214step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw17215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17215Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw17215step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17215step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17215step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17215step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17215step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17215 raw17215Labels = mixedMoment B node3768 node3768Labels := by
  calc
    mixedMoment B raw17215 raw17215Labels = mixedMoment B raw17215step0 raw17215step0Labels := by
      have ha : raw17215step0 = (fun i j => raw17215 (permutation283 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17215step0 raw17215; decide +kernel
      have hl : raw17215step0Labels = raw17215Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17215 raw17215Labels permutation283 permutation5
    mixedMoment B raw17215step0 raw17215step0Labels = mixedMoment B raw17215step1 raw17215step1Labels := by
      have ha : raw17215step1 = -raw17215step0 := by apply Matrix.ext; change ∀ i j, raw17215step1 i j = -(raw17215step0 i j); unfold raw17215step1 raw17215step0; decide +kernel
      have hl : raw17215step1Labels = raw17215step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17215step1 raw17215step1Labels = mixedMoment B raw17215step2 raw17215step2Labels := by
      have ha : raw17215step2 = raw17215step1 := by apply Matrix.ext; unfold raw17215step2 raw17215step1; decide +kernel
      have hl : raw17215step1Labels = labelEmbedding1 ∘ raw17215step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17215step1 raw17215step1Labels raw17215step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3768 node3768Labels := by rfl

def raw17216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17216Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17216step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17216step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17216step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17216 raw17216Labels = mixedMoment B node3764 node3764Labels := by
  calc
    mixedMoment B raw17216 raw17216Labels = mixedMoment B raw17216step0 raw17216step0Labels := by
      have ha : raw17216step0 = (fun i j => raw17216 (permutation676 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17216step0 raw17216; decide +kernel
      have hl : raw17216step0Labels = raw17216Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17216 raw17216Labels permutation676 permutation7
    mixedMoment B raw17216step0 raw17216step0Labels = mixedMoment B raw17216step1 raw17216step1Labels := by
      have ha : raw17216step1 = raw17216step0 := by apply Matrix.ext; unfold raw17216step1 raw17216step0; decide +kernel
      have hl : raw17216step0Labels = labelEmbedding1 ∘ raw17216step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17216step0 raw17216step0Labels raw17216step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3764 node3764Labels := by rfl

def raw17217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17217Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17217step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17217step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17217step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17217step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17217 raw17217Labels = mixedMoment B node3764 node3764Labels := by
  calc
    mixedMoment B raw17217 raw17217Labels = mixedMoment B raw17217step0 raw17217step0Labels := by
      have ha : raw17217step0 = (fun i j => raw17217 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17217step0 raw17217; decide +kernel
      have hl : raw17217step0Labels = raw17217Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17217 raw17217Labels permutation674 permutation7
    mixedMoment B raw17217step0 raw17217step0Labels = mixedMoment B raw17217step1 raw17217step1Labels := by
      have ha : raw17217step1 = raw17217step0 := by apply Matrix.ext; unfold raw17217step1 raw17217step0; decide +kernel
      have hl : raw17217step0Labels = labelEmbedding1 ∘ raw17217step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17217step0 raw17217step0Labels raw17217step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3764 node3764Labels := by rfl

def raw17218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw17218Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17218step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17218step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17218step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17218 raw17218Labels = mixedMoment B node3956 node3956Labels := by
  calc
    mixedMoment B raw17218 raw17218Labels = mixedMoment B raw17218step0 raw17218step0Labels := by
      have ha : raw17218step0 = (fun i j => raw17218 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17218step0 raw17218; decide +kernel
      have hl : raw17218step0Labels = raw17218Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17218 raw17218Labels permutation674 permutation7
    mixedMoment B raw17218step0 raw17218step0Labels = mixedMoment B raw17218step1 raw17218step1Labels := by
      have ha : raw17218step1 = raw17218step0 := by apply Matrix.ext; unfold raw17218step1 raw17218step0; decide +kernel
      have hl : raw17218step0Labels = labelEmbedding1 ∘ raw17218step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17218step0 raw17218step0Labels raw17218step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3956 node3956Labels := by rfl

def raw17219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17219Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17219step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17219step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17219step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17219 raw17219Labels = mixedMoment B node3476 node3476Labels := by
  calc
    mixedMoment B raw17219 raw17219Labels = mixedMoment B raw17219step0 raw17219step0Labels := by
      have ha : raw17219step0 = (fun i j => raw17219 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17219step0 raw17219; decide +kernel
      have hl : raw17219step0Labels = raw17219Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17219 raw17219Labels permutation674 permutation7
    mixedMoment B raw17219step0 raw17219step0Labels = mixedMoment B raw17219step1 raw17219step1Labels := by
      have ha : raw17219step1 = raw17219step0 := by apply Matrix.ext; unfold raw17219step1 raw17219step0; decide +kernel
      have hl : raw17219step0Labels = labelEmbedding1 ∘ raw17219step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17219step0 raw17219step0Labels raw17219step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3476 node3476Labels := by rfl

def raw17220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17220Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17220step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17220step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17220step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17220 raw17220Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw17220 raw17220Labels = mixedMoment B raw17220step0 raw17220step0Labels := by
      have ha : raw17220step0 = (fun i j => raw17220 (permutation676 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17220step0 raw17220; decide +kernel
      have hl : raw17220step0Labels = raw17220Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17220 raw17220Labels permutation676 permutation7
    mixedMoment B raw17220step0 raw17220step0Labels = mixedMoment B raw17220step1 raw17220step1Labels := by
      have ha : raw17220step1 = raw17220step0 := by apply Matrix.ext; unfold raw17220step1 raw17220step0; decide +kernel
      have hl : raw17220step0Labels = labelEmbedding1 ∘ raw17220step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17220step0 raw17220step0Labels raw17220step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

def raw17221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17221Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17221step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17221step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17221step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17221 raw17221Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw17221 raw17221Labels = mixedMoment B raw17221step0 raw17221step0Labels := by
      have ha : raw17221step0 = (fun i j => raw17221 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17221step0 raw17221; decide +kernel
      have hl : raw17221step0Labels = raw17221Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17221 raw17221Labels permutation674 permutation7
    mixedMoment B raw17221step0 raw17221step0Labels = mixedMoment B raw17221step1 raw17221step1Labels := by
      have ha : raw17221step1 = raw17221step0 := by apply Matrix.ext; unfold raw17221step1 raw17221step0; decide +kernel
      have hl : raw17221step0Labels = labelEmbedding1 ∘ raw17221step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17221step0 raw17221step0Labels raw17221step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

def raw17222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw17222Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17222step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17222step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17222step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17222 raw17222Labels = mixedMoment B node3531 node3531Labels := by
  calc
    mixedMoment B raw17222 raw17222Labels = mixedMoment B raw17222step0 raw17222step0Labels := by
      have ha : raw17222step0 = (fun i j => raw17222 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17222step0 raw17222; decide +kernel
      have hl : raw17222step0Labels = raw17222Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17222 raw17222Labels permutation674 permutation7
    mixedMoment B raw17222step0 raw17222step0Labels = mixedMoment B raw17222step1 raw17222step1Labels := by
      have ha : raw17222step1 = raw17222step0 := by apply Matrix.ext; unfold raw17222step1 raw17222step0; decide +kernel
      have hl : raw17222step0Labels = labelEmbedding1 ∘ raw17222step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17222step0 raw17222step0Labels raw17222step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3531 node3531Labels := by rfl

def raw17223 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17223step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17223 raw17223Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw17223 raw17223Labels = mixedMoment B raw17223step0 raw17223step0Labels := by
      have hz : ∀ j, raw17223 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17223step0 = (fun i j => raw17223 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17223step0 raw17223; decide +kernel
      have hl : raw17223step0Labels = raw17223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17223 raw17223Labels permutation434 hz
    mixedMoment B raw17223step0 raw17223step0Labels = mixedMoment B raw17223step1 raw17223step1Labels := by
      have ha : raw17223step1 = (fun i j => raw17223step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17223step1 raw17223step0; decide +kernel
      have hl : raw17223step1Labels = raw17223step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17223step0 raw17223step0Labels permutation149 permutation2
    _ = mixedMoment B node5409 node5409Labels := by rfl

def raw17224 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw17224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17224 raw17224Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw17224 raw17224Labels = mixedMoment B raw17224step0 raw17224step0Labels := by
      have ha : raw17224step0 = (fun i j => raw17224 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17224step0 raw17224; decide +kernel
      have hl : raw17224step0Labels = raw17224Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17224 raw17224Labels permutation674 permutation2
    _ = mixedMoment B node5351 node5351Labels := by rfl

def raw17225 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw17225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17225 raw17225Labels = mixedMoment B node5072 node5072Labels := by
  calc
    mixedMoment B raw17225 raw17225Labels = mixedMoment B raw17225step0 raw17225step0Labels := by
      have ha : raw17225step0 = (fun i j => raw17225 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17225step0 raw17225; decide +kernel
      have hl : raw17225step0Labels = raw17225Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17225 raw17225Labels permutation674 permutation2
    _ = mixedMoment B node5072 node5072Labels := by rfl

def raw17226 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17226 raw17226Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw17226 raw17226Labels = mixedMoment B raw17226step0 raw17226step0Labels := by
      have hz : ∀ j, raw17226 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17226step0 = (fun i j => raw17226 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17226step0 raw17226; decide +kernel
      have hl : raw17226step0Labels = raw17226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17226 raw17226Labels permutation434 hz
    mixedMoment B raw17226step0 raw17226step0Labels = mixedMoment B raw17226step1 raw17226step1Labels := by
      have ha : raw17226step1 = (fun i j => raw17226step0 (permutation148 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17226step1 raw17226step0; decide +kernel
      have hl : raw17226step1Labels = raw17226step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17226step0 raw17226step0Labels permutation148 permutation2
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw17227 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw17227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17227 raw17227Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw17227 raw17227Labels = mixedMoment B raw17227step0 raw17227step0Labels := by
      have ha : raw17227step0 = (fun i j => raw17227 (permutation675 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17227step0 raw17227; decide +kernel
      have hl : raw17227step0Labels = raw17227Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17227 raw17227Labels permutation675 permutation2
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw17228 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw17228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17228 raw17228Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw17228 raw17228Labels = mixedMoment B raw17228step0 raw17228step0Labels := by
      have ha : raw17228step0 = (fun i j => raw17228 (permutation675 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17228step0 raw17228; decide +kernel
      have hl : raw17228step0Labels = raw17228Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17228 raw17228Labels permutation675 permutation2
    _ = mixedMoment B node5074 node5074Labels := by rfl

def raw17229 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw17229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17229step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17229 raw17229Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw17229 raw17229Labels = mixedMoment B raw17229step0 raw17229step0Labels := by
      have ha : raw17229step0 = (fun i j => raw17229 (permutation673 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17229step0 raw17229; decide +kernel
      have hl : raw17229step0Labels = raw17229Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17229 raw17229Labels permutation673 permutation2
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw17230 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw17230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17230 raw17230Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw17230 raw17230Labels = mixedMoment B raw17230step0 raw17230step0Labels := by
      have ha : raw17230step0 = (fun i j => raw17230 (permutation673 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17230step0 raw17230; decide +kernel
      have hl : raw17230step0Labels = raw17230Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17230 raw17230Labels permutation673 permutation2
    _ = mixedMoment B node5074 node5074Labels := by rfl

def raw17231 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17231step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17231step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17231step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17231step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17231step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17231 raw17231Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw17231 raw17231Labels = mixedMoment B raw17231step0 raw17231step0Labels := by
      have hz : ∀ j, raw17231 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17231step0 = (fun i j => raw17231 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17231step0 raw17231; decide +kernel
      have hl : raw17231step0Labels = raw17231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17231 raw17231Labels permutation434 hz
    mixedMoment B raw17231step0 raw17231step0Labels = mixedMoment B raw17231step1 raw17231step1Labels := by
      have ha : raw17231step1 = (fun i j => raw17231step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17231step1 raw17231step0; decide +kernel
      have hl : raw17231step1Labels = raw17231step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17231step0 raw17231step0Labels permutation151 permutation7
    mixedMoment B raw17231step1 raw17231step1Labels = mixedMoment B raw17231step2 raw17231step2Labels := by
      have ha : raw17231step2 = -raw17231step1 := by apply Matrix.ext; change ∀ i j, raw17231step2 i j = -(raw17231step1 i j); unfold raw17231step2 raw17231step1; decide +kernel
      have hl : raw17231step2Labels = raw17231step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17231step2 raw17231step2Labels = mixedMoment B raw17231step3 raw17231step3Labels := by
      have ha : raw17231step3 = raw17231step2 := by apply Matrix.ext; unfold raw17231step3 raw17231step2; decide +kernel
      have hl : raw17231step2Labels = labelEmbedding10 ∘ raw17231step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17231step2 raw17231step2Labels raw17231step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw17232 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw17232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17232 raw17232Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw17232 raw17232Labels = mixedMoment B raw17232step0 raw17232step0Labels := by
      have ha : raw17232step0 = (fun i j => raw17232 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17232step0 raw17232; decide +kernel
      have hl : raw17232step0Labels = raw17232Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17232 raw17232Labels permutation674 permutation2
    _ = mixedMoment B node5256 node5256Labels := by rfl

def raw17233 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17233Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17233step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17233step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17233step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17233step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17233step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17233step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17233 raw17233Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw17233 raw17233Labels = mixedMoment B raw17233step0 raw17233step0Labels := by
      have hz : ∀ j, raw17233 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17233step0 = (fun i j => raw17233 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17233step0 raw17233; decide +kernel
      have hl : raw17233step0Labels = raw17233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17233 raw17233Labels permutation346 hz
    mixedMoment B raw17233step0 raw17233step0Labels = mixedMoment B raw17233step1 raw17233step1Labels := by
      have ha : raw17233step1 = (fun i j => raw17233step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17233step1 raw17233step0; decide +kernel
      have hl : raw17233step1Labels = raw17233step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17233step0 raw17233step0Labels permutation151 permutation7
    mixedMoment B raw17233step1 raw17233step1Labels = mixedMoment B raw17233step2 raw17233step2Labels := by
      have ha : raw17233step2 = -raw17233step1 := by apply Matrix.ext; change ∀ i j, raw17233step2 i j = -(raw17233step1 i j); unfold raw17233step2 raw17233step1; decide +kernel
      have hl : raw17233step2Labels = raw17233step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17233step2 raw17233step2Labels = mixedMoment B raw17233step3 raw17233step3Labels := by
      have ha : raw17233step3 = raw17233step2 := by apply Matrix.ext; unfold raw17233step3 raw17233step2; decide +kernel
      have hl : raw17233step2Labels = labelEmbedding1 ∘ raw17233step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17233step2 raw17233step2Labels raw17233step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

def raw17234 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17234Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17234step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17234step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17234step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17234step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17234step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17234step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17234 raw17234Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw17234 raw17234Labels = mixedMoment B raw17234step0 raw17234step0Labels := by
      have hz : ∀ j, raw17234 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17234step0 = (fun i j => raw17234 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17234step0 raw17234; decide +kernel
      have hl : raw17234step0Labels = raw17234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17234 raw17234Labels permutation434 hz
    mixedMoment B raw17234step0 raw17234step0Labels = mixedMoment B raw17234step1 raw17234step1Labels := by
      have ha : raw17234step1 = (fun i j => raw17234step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17234step1 raw17234step0; decide +kernel
      have hl : raw17234step1Labels = raw17234step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17234step0 raw17234step0Labels permutation151 permutation7
    mixedMoment B raw17234step1 raw17234step1Labels = mixedMoment B raw17234step2 raw17234step2Labels := by
      have ha : raw17234step2 = -raw17234step1 := by apply Matrix.ext; change ∀ i j, raw17234step2 i j = -(raw17234step1 i j); unfold raw17234step2 raw17234step1; decide +kernel
      have hl : raw17234step2Labels = raw17234step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17234step2 raw17234step2Labels = mixedMoment B raw17234step3 raw17234step3Labels := by
      have ha : raw17234step3 = raw17234step2 := by apply Matrix.ext; unfold raw17234step3 raw17234step2; decide +kernel
      have hl : raw17234step2Labels = labelEmbedding1 ∘ raw17234step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17234step2 raw17234step2Labels raw17234step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

def raw17235 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw17235Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17235step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17235step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17235step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17235step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17235step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17235step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17235 raw17235Labels = mixedMoment B node3757 node3757Labels := by
  calc
    mixedMoment B raw17235 raw17235Labels = mixedMoment B raw17235step0 raw17235step0Labels := by
      have ha : raw17235step0 = (fun i j => raw17235 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17235step0 raw17235; decide +kernel
      have hl : raw17235step0Labels = raw17235Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17235 raw17235Labels permutation682 permutation7
    mixedMoment B raw17235step0 raw17235step0Labels = mixedMoment B raw17235step1 raw17235step1Labels := by
      have ha : raw17235step1 = -raw17235step0 := by apply Matrix.ext; change ∀ i j, raw17235step1 i j = -(raw17235step0 i j); unfold raw17235step1 raw17235step0; decide +kernel
      have hl : raw17235step1Labels = raw17235step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17235step1 raw17235step1Labels = mixedMoment B raw17235step2 raw17235step2Labels := by
      have ha : raw17235step2 = raw17235step1 := by apply Matrix.ext; unfold raw17235step2 raw17235step1; decide +kernel
      have hl : raw17235step1Labels = labelEmbedding1 ∘ raw17235step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17235step1 raw17235step1Labels raw17235step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3757 node3757Labels := by rfl

def raw17236 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw17236Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17236step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17236step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17236step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17236step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17236step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17236 raw17236Labels = mixedMoment B node3459 node3459Labels := by
  calc
    mixedMoment B raw17236 raw17236Labels = mixedMoment B raw17236step0 raw17236step0Labels := by
      have ha : raw17236step0 = (fun i j => raw17236 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17236step0 raw17236; decide +kernel
      have hl : raw17236step0Labels = raw17236Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17236 raw17236Labels permutation682 permutation7
    mixedMoment B raw17236step0 raw17236step0Labels = mixedMoment B raw17236step1 raw17236step1Labels := by
      have ha : raw17236step1 = -raw17236step0 := by apply Matrix.ext; change ∀ i j, raw17236step1 i j = -(raw17236step0 i j); unfold raw17236step1 raw17236step0; decide +kernel
      have hl : raw17236step1Labels = raw17236step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17236step1 raw17236step1Labels = mixedMoment B raw17236step2 raw17236step2Labels := by
      have ha : raw17236step2 = raw17236step1 := by apply Matrix.ext; unfold raw17236step2 raw17236step1; decide +kernel
      have hl : raw17236step1Labels = labelEmbedding1 ∘ raw17236step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17236step1 raw17236step1Labels raw17236step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3459 node3459Labels := by rfl

def raw17237 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17237Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17237step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17237step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17237step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17237step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17237step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17237step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17237 raw17237Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw17237 raw17237Labels = mixedMoment B raw17237step0 raw17237step0Labels := by
      have hz : ∀ j, raw17237 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17237step0 = (fun i j => raw17237 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17237step0 raw17237; decide +kernel
      have hl : raw17237step0Labels = raw17237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17237 raw17237Labels permutation434 hz
    mixedMoment B raw17237step0 raw17237step0Labels = mixedMoment B raw17237step1 raw17237step1Labels := by
      have ha : raw17237step1 = (fun i j => raw17237step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17237step1 raw17237step0; decide +kernel
      have hl : raw17237step1Labels = raw17237step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17237step0 raw17237step0Labels permutation151 permutation7
    mixedMoment B raw17237step1 raw17237step1Labels = mixedMoment B raw17237step2 raw17237step2Labels := by
      have ha : raw17237step2 = -raw17237step1 := by apply Matrix.ext; change ∀ i j, raw17237step2 i j = -(raw17237step1 i j); unfold raw17237step2 raw17237step1; decide +kernel
      have hl : raw17237step2Labels = raw17237step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17237step2 raw17237step2Labels = mixedMoment B raw17237step3 raw17237step3Labels := by
      have ha : raw17237step3 = raw17237step2 := by apply Matrix.ext; unfold raw17237step3 raw17237step2; decide +kernel
      have hl : raw17237step2Labels = labelEmbedding1 ∘ raw17237step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17237step2 raw17237step2Labels raw17237step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw17238 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw17238Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17238step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17238step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17238step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17238step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17238step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17238 raw17238Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw17238 raw17238Labels = mixedMoment B raw17238step0 raw17238step0Labels := by
      have ha : raw17238step0 = (fun i j => raw17238 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17238step0 raw17238; decide +kernel
      have hl : raw17238step0Labels = raw17238Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17238 raw17238Labels permutation688 permutation7
    mixedMoment B raw17238step0 raw17238step0Labels = mixedMoment B raw17238step1 raw17238step1Labels := by
      have ha : raw17238step1 = -raw17238step0 := by apply Matrix.ext; change ∀ i j, raw17238step1 i j = -(raw17238step0 i j); unfold raw17238step1 raw17238step0; decide +kernel
      have hl : raw17238step1Labels = raw17238step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17238step1 raw17238step1Labels = mixedMoment B raw17238step2 raw17238step2Labels := by
      have ha : raw17238step2 = raw17238step1 := by apply Matrix.ext; unfold raw17238step2 raw17238step1; decide +kernel
      have hl : raw17238step1Labels = labelEmbedding1 ∘ raw17238step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17238step1 raw17238step1Labels raw17238step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

def raw17239 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw17239Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17239step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17239step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17239step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17239step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17239step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17239 raw17239Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw17239 raw17239Labels = mixedMoment B raw17239step0 raw17239step0Labels := by
      have ha : raw17239step0 = (fun i j => raw17239 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17239step0 raw17239; decide +kernel
      have hl : raw17239step0Labels = raw17239Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17239 raw17239Labels permutation688 permutation7
    mixedMoment B raw17239step0 raw17239step0Labels = mixedMoment B raw17239step1 raw17239step1Labels := by
      have ha : raw17239step1 = -raw17239step0 := by apply Matrix.ext; change ∀ i j, raw17239step1 i j = -(raw17239step0 i j); unfold raw17239step1 raw17239step0; decide +kernel
      have hl : raw17239step1Labels = raw17239step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17239step1 raw17239step1Labels = mixedMoment B raw17239step2 raw17239step2Labels := by
      have ha : raw17239step2 = raw17239step1 := by apply Matrix.ext; unfold raw17239step2 raw17239step1; decide +kernel
      have hl : raw17239step1Labels = labelEmbedding1 ∘ raw17239step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17239step1 raw17239step1Labels raw17239step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

def raw17240 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17240Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw17240step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17240step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17240step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17240step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17240step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17240step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17240 raw17240Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw17240 raw17240Labels = mixedMoment B raw17240step0 raw17240step0Labels := by
      have hz : ∀ j, raw17240 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17240step0 = (fun i j => raw17240 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17240step0 raw17240; decide +kernel
      have hl : raw17240step0Labels = raw17240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17240 raw17240Labels permutation346 hz
    mixedMoment B raw17240step0 raw17240step0Labels = mixedMoment B raw17240step1 raw17240step1Labels := by
      have ha : raw17240step1 = (fun i j => raw17240step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17240step1 raw17240step0; decide +kernel
      have hl : raw17240step1Labels = raw17240step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17240step0 raw17240step0Labels permutation151 permutation7
    mixedMoment B raw17240step1 raw17240step1Labels = mixedMoment B raw17240step2 raw17240step2Labels := by
      have ha : raw17240step2 = -raw17240step1 := by apply Matrix.ext; change ∀ i j, raw17240step2 i j = -(raw17240step1 i j); unfold raw17240step2 raw17240step1; decide +kernel
      have hl : raw17240step2Labels = raw17240step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17240step2 raw17240step2Labels = mixedMoment B raw17240step3 raw17240step3Labels := by
      have ha : raw17240step3 = raw17240step2 := by apply Matrix.ext; unfold raw17240step3 raw17240step2; decide +kernel
      have hl : raw17240step2Labels = labelEmbedding1 ∘ raw17240step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17240step2 raw17240step2Labels raw17240step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw17241 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw17241Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17241step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17241step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17241step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17241step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17241step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17241 raw17241Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw17241 raw17241Labels = mixedMoment B raw17241step0 raw17241step0Labels := by
      have ha : raw17241step0 = (fun i j => raw17241 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17241step0 raw17241; decide +kernel
      have hl : raw17241step0Labels = raw17241Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17241 raw17241Labels permutation682 permutation7
    mixedMoment B raw17241step0 raw17241step0Labels = mixedMoment B raw17241step1 raw17241step1Labels := by
      have ha : raw17241step1 = -raw17241step0 := by apply Matrix.ext; change ∀ i j, raw17241step1 i j = -(raw17241step0 i j); unfold raw17241step1 raw17241step0; decide +kernel
      have hl : raw17241step1Labels = raw17241step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17241step1 raw17241step1Labels = mixedMoment B raw17241step2 raw17241step2Labels := by
      have ha : raw17241step2 = raw17241step1 := by apply Matrix.ext; unfold raw17241step2 raw17241step1; decide +kernel
      have hl : raw17241step1Labels = labelEmbedding1 ∘ raw17241step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17241step1 raw17241step1Labels raw17241step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

def raw17242 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw17242Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17242step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17242step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17242step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17242step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17242step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17242step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17242 raw17242Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw17242 raw17242Labels = mixedMoment B raw17242step0 raw17242step0Labels := by
      have ha : raw17242step0 = (fun i j => raw17242 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17242step0 raw17242; decide +kernel
      have hl : raw17242step0Labels = raw17242Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17242 raw17242Labels permutation682 permutation7
    mixedMoment B raw17242step0 raw17242step0Labels = mixedMoment B raw17242step1 raw17242step1Labels := by
      have ha : raw17242step1 = -raw17242step0 := by apply Matrix.ext; change ∀ i j, raw17242step1 i j = -(raw17242step0 i j); unfold raw17242step1 raw17242step0; decide +kernel
      have hl : raw17242step1Labels = raw17242step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17242step1 raw17242step1Labels = mixedMoment B raw17242step2 raw17242step2Labels := by
      have ha : raw17242step2 = raw17242step1 := by apply Matrix.ext; unfold raw17242step2 raw17242step1; decide +kernel
      have hl : raw17242step1Labels = labelEmbedding1 ∘ raw17242step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17242step1 raw17242step1Labels raw17242step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

def raw17243 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17243Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17243step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17243step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17243step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17243step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17243step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17243step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17243 raw17243Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw17243 raw17243Labels = mixedMoment B raw17243step0 raw17243step0Labels := by
      have hz : ∀ j, raw17243 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17243step0 = (fun i j => raw17243 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17243step0 raw17243; decide +kernel
      have hl : raw17243step0Labels = raw17243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17243 raw17243Labels permutation346 hz
    mixedMoment B raw17243step0 raw17243step0Labels = mixedMoment B raw17243step1 raw17243step1Labels := by
      have ha : raw17243step1 = (fun i j => raw17243step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17243step1 raw17243step0; decide +kernel
      have hl : raw17243step1Labels = raw17243step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17243step0 raw17243step0Labels permutation151 permutation7
    mixedMoment B raw17243step1 raw17243step1Labels = mixedMoment B raw17243step2 raw17243step2Labels := by
      have ha : raw17243step2 = -raw17243step1 := by apply Matrix.ext; change ∀ i j, raw17243step2 i j = -(raw17243step1 i j); unfold raw17243step2 raw17243step1; decide +kernel
      have hl : raw17243step2Labels = raw17243step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17243step2 raw17243step2Labels = mixedMoment B raw17243step3 raw17243step3Labels := by
      have ha : raw17243step3 = raw17243step2 := by apply Matrix.ext; unfold raw17243step3 raw17243step2; decide +kernel
      have hl : raw17243step2Labels = labelEmbedding1 ∘ raw17243step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17243step2 raw17243step2Labels raw17243step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw17244 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17244Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17244step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17244step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17244step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17244step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17244step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17244step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17244 raw17244Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw17244 raw17244Labels = mixedMoment B raw17244step0 raw17244step0Labels := by
      have hz : ∀ j, raw17244 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17244step0 = (fun i j => raw17244 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17244step0 raw17244; decide +kernel
      have hl : raw17244step0Labels = raw17244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17244 raw17244Labels permutation434 hz
    mixedMoment B raw17244step0 raw17244step0Labels = mixedMoment B raw17244step1 raw17244step1Labels := by
      have ha : raw17244step1 = (fun i j => raw17244step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17244step1 raw17244step0; decide +kernel
      have hl : raw17244step1Labels = raw17244step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17244step0 raw17244step0Labels permutation151 permutation7
    mixedMoment B raw17244step1 raw17244step1Labels = mixedMoment B raw17244step2 raw17244step2Labels := by
      have ha : raw17244step2 = -raw17244step1 := by apply Matrix.ext; change ∀ i j, raw17244step2 i j = -(raw17244step1 i j); unfold raw17244step2 raw17244step1; decide +kernel
      have hl : raw17244step2Labels = raw17244step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17244step2 raw17244step2Labels = mixedMoment B raw17244step3 raw17244step3Labels := by
      have ha : raw17244step3 = raw17244step2 := by apply Matrix.ext; unfold raw17244step3 raw17244step2; decide +kernel
      have hl : raw17244step2Labels = labelEmbedding1 ∘ raw17244step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17244step2 raw17244step2Labels raw17244step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw17245 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw17245Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17245step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17245step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17245step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17245step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17245step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17245step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17245 raw17245Labels = mixedMoment B node3525 node3525Labels := by
  calc
    mixedMoment B raw17245 raw17245Labels = mixedMoment B raw17245step0 raw17245step0Labels := by
      have ha : raw17245step0 = (fun i j => raw17245 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17245step0 raw17245; decide +kernel
      have hl : raw17245step0Labels = raw17245Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17245 raw17245Labels permutation682 permutation7
    mixedMoment B raw17245step0 raw17245step0Labels = mixedMoment B raw17245step1 raw17245step1Labels := by
      have ha : raw17245step1 = -raw17245step0 := by apply Matrix.ext; change ∀ i j, raw17245step1 i j = -(raw17245step0 i j); unfold raw17245step1 raw17245step0; decide +kernel
      have hl : raw17245step1Labels = raw17245step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17245step1 raw17245step1Labels = mixedMoment B raw17245step2 raw17245step2Labels := by
      have ha : raw17245step2 = raw17245step1 := by apply Matrix.ext; unfold raw17245step2 raw17245step1; decide +kernel
      have hl : raw17245step1Labels = labelEmbedding1 ∘ raw17245step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17245step1 raw17245step1Labels raw17245step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3525 node3525Labels := by rfl

def raw17246 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17246Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17246step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17246step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17246step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17246step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17246step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17246 raw17246Labels = mixedMoment B node3976 node3976Labels := by
  calc
    mixedMoment B raw17246 raw17246Labels = mixedMoment B raw17246step0 raw17246step0Labels := by
      have ha : raw17246step0 = (fun i j => raw17246 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17246step0 raw17246; decide +kernel
      have hl : raw17246step0Labels = raw17246Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17246 raw17246Labels permutation682 permutation7
    mixedMoment B raw17246step0 raw17246step0Labels = mixedMoment B raw17246step1 raw17246step1Labels := by
      have ha : raw17246step1 = -raw17246step0 := by apply Matrix.ext; change ∀ i j, raw17246step1 i j = -(raw17246step0 i j); unfold raw17246step1 raw17246step0; decide +kernel
      have hl : raw17246step1Labels = raw17246step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17246step1 raw17246step1Labels = mixedMoment B raw17246step2 raw17246step2Labels := by
      have ha : raw17246step2 = raw17246step1 := by apply Matrix.ext; unfold raw17246step2 raw17246step1; decide +kernel
      have hl : raw17246step1Labels = labelEmbedding1 ∘ raw17246step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17246step1 raw17246step1Labels raw17246step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3976 node3976Labels := by rfl

def raw17247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17247step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17247step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17247step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17247 raw17247Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw17247 raw17247Labels = mixedMoment B raw17247step0 raw17247step0Labels := by
      have hz : ∀ j, raw17247 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17247step0 = (fun i j => raw17247 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17247step0 raw17247; decide +kernel
      have hl : raw17247step0Labels = raw17247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17247 raw17247Labels permutation434 hz
    mixedMoment B raw17247step0 raw17247step0Labels = mixedMoment B raw17247step1 raw17247step1Labels := by
      have ha : raw17247step1 = (fun i j => raw17247step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17247step1 raw17247step0; decide +kernel
      have hl : raw17247step1Labels = raw17247step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17247step0 raw17247step0Labels permutation144 permutation7
    mixedMoment B raw17247step1 raw17247step1Labels = mixedMoment B raw17247step2 raw17247step2Labels := by
      have ha : raw17247step2 = raw17247step1 := by apply Matrix.ext; unfold raw17247step2 raw17247step1; decide +kernel
      have hl : raw17247step1Labels = labelEmbedding10 ∘ raw17247step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17247step1 raw17247step1Labels raw17247step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw17248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw17248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17248step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17248step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17248 raw17248Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw17248 raw17248Labels = mixedMoment B raw17248step0 raw17248step0Labels := by
      have hz : ∀ j, raw17248 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17248step0 = (fun i j => raw17248 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17248step0 raw17248; decide +kernel
      have hl : raw17248step0Labels = raw17248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17248 raw17248Labels permutation434 hz
    mixedMoment B raw17248step0 raw17248step0Labels = mixedMoment B raw17248step1 raw17248step1Labels := by
      have ha : raw17248step1 = (fun i j => raw17248step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17248step1 raw17248step0; decide +kernel
      have hl : raw17248step1Labels = raw17248step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17248step0 raw17248step0Labels permutation150 permutation2
    mixedMoment B raw17248step1 raw17248step1Labels = mixedMoment B raw17248step2 raw17248step2Labels := by
      have ha : raw17248step2 = -raw17248step1 := by apply Matrix.ext; change ∀ i j, raw17248step2 i j = -(raw17248step1 i j); unfold raw17248step2 raw17248step1; decide +kernel
      have hl : raw17248step2Labels = raw17248step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw17249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17249step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17249step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17249 raw17249Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw17249 raw17249Labels = mixedMoment B raw17249step0 raw17249step0Labels := by
      have ha : raw17249step0 = (fun i j => raw17249 (permutation639 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17249step0 raw17249; decide +kernel
      have hl : raw17249step0Labels = raw17249Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17249 raw17249Labels permutation639 permutation7
    mixedMoment B raw17249step0 raw17249step0Labels = mixedMoment B raw17249step1 raw17249step1Labels := by
      have ha : raw17249step1 = raw17249step0 := by apply Matrix.ext; unfold raw17249step1 raw17249step0; decide +kernel
      have hl : raw17249step0Labels = labelEmbedding10 ∘ raw17249step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17249step0 raw17249step0Labels raw17249step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw17250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw17250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17250step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17250step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17250step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17250 raw17250Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw17250 raw17250Labels = mixedMoment B raw17250step0 raw17250step0Labels := by
      have hz : ∀ j, raw17250 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17250step0 = (fun i j => raw17250 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17250step0 raw17250; decide +kernel
      have hl : raw17250step0Labels = raw17250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17250 raw17250Labels permutation434 hz
    mixedMoment B raw17250step0 raw17250step0Labels = mixedMoment B raw17250step1 raw17250step1Labels := by
      have ha : raw17250step1 = (fun i j => raw17250step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17250step1 raw17250step0; decide +kernel
      have hl : raw17250step1Labels = raw17250step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17250step0 raw17250step0Labels permutation144 permutation7
    mixedMoment B raw17250step1 raw17250step1Labels = mixedMoment B raw17250step2 raw17250step2Labels := by
      have ha : raw17250step2 = raw17250step1 := by apply Matrix.ext; unfold raw17250step2 raw17250step1; decide +kernel
      have hl : raw17250step1Labels = labelEmbedding10 ∘ raw17250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17250step1 raw17250step1Labels raw17250step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw17251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw17251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw17251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17251step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17251step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17251step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17251 raw17251Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw17251 raw17251Labels = mixedMoment B raw17251step0 raw17251step0Labels := by
      have hz : ∀ j, raw17251 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17251step0 = (fun i j => raw17251 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17251step0 raw17251; decide +kernel
      have hl : raw17251step0Labels = raw17251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17251 raw17251Labels permutation434 hz
    mixedMoment B raw17251step0 raw17251step0Labels = mixedMoment B raw17251step1 raw17251step1Labels := by
      have ha : raw17251step1 = (fun i j => raw17251step0 (permutation140 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17251step1 raw17251step0; decide +kernel
      have hl : raw17251step1Labels = raw17251step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17251step0 raw17251step0Labels permutation140 permutation6
    mixedMoment B raw17251step1 raw17251step1Labels = mixedMoment B raw17251step2 raw17251step2Labels := by
      have ha : raw17251step2 = raw17251step1 := by apply Matrix.ext; unfold raw17251step2 raw17251step1; decide +kernel
      have hl : raw17251step1Labels = labelEmbedding9 ∘ raw17251step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17251step1 raw17251step1Labels raw17251step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw17252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17252step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17252step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17252 raw17252Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw17252 raw17252Labels = mixedMoment B raw17252step0 raw17252step0Labels := by
      have hz : ∀ j, raw17252 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17252step0 = (fun i j => raw17252 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17252step0 raw17252; decide +kernel
      have hl : raw17252step0Labels = raw17252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17252 raw17252Labels permutation434 hz
    mixedMoment B raw17252step0 raw17252step0Labels = mixedMoment B raw17252step1 raw17252step1Labels := by
      have ha : raw17252step1 = (fun i j => raw17252step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17252step1 raw17252step0; decide +kernel
      have hl : raw17252step1Labels = raw17252step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17252step0 raw17252step0Labels permutation38 permutation3
    mixedMoment B raw17252step1 raw17252step1Labels = mixedMoment B raw17252step2 raw17252step2Labels := by
      have ha : raw17252step2 = raw17252step1 := by apply Matrix.ext; unfold raw17252step2 raw17252step1; decide +kernel
      have hl : raw17252step1Labels = labelEmbedding6 ∘ raw17252step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17252step1 raw17252step1Labels raw17252step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw17253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17253step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17253step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17253 raw17253Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw17253 raw17253Labels = mixedMoment B raw17253step0 raw17253step0Labels := by
      have hz : ∀ j, raw17253 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17253step0 = (fun i j => raw17253 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17253step0 raw17253; decide +kernel
      have hl : raw17253step0Labels = raw17253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17253 raw17253Labels permutation434 hz
    mixedMoment B raw17253step0 raw17253step0Labels = mixedMoment B raw17253step1 raw17253step1Labels := by
      have ha : raw17253step1 = (fun i j => raw17253step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17253step1 raw17253step0; decide +kernel
      have hl : raw17253step1Labels = raw17253step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17253step0 raw17253step0Labels permutation149 permutation2
    mixedMoment B raw17253step1 raw17253step1Labels = mixedMoment B raw17253step2 raw17253step2Labels := by
      have ha : raw17253step2 = -raw17253step1 := by apply Matrix.ext; change ∀ i j, raw17253step2 i j = -(raw17253step1 i j); unfold raw17253step2 raw17253step1; decide +kernel
      have hl : raw17253step2Labels = raw17253step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw17254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17254step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17254step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17254step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17254 raw17254Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw17254 raw17254Labels = mixedMoment B raw17254step0 raw17254step0Labels := by
      have ha : raw17254step0 = (fun i j => raw17254 (permutation640 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17254step0 raw17254; decide +kernel
      have hl : raw17254step0Labels = raw17254Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17254 raw17254Labels permutation640 permutation7
    mixedMoment B raw17254step0 raw17254step0Labels = mixedMoment B raw17254step1 raw17254step1Labels := by
      have ha : raw17254step1 = raw17254step0 := by apply Matrix.ext; unfold raw17254step1 raw17254step0; decide +kernel
      have hl : raw17254step0Labels = labelEmbedding10 ∘ raw17254step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17254step0 raw17254step0Labels raw17254step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw17255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw17255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17255step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17255step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17255step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17255 raw17255Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw17255 raw17255Labels = mixedMoment B raw17255step0 raw17255step0Labels := by
      have hz : ∀ j, raw17255 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17255step0 = (fun i j => raw17255 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17255step0 raw17255; decide +kernel
      have hl : raw17255step0Labels = raw17255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17255 raw17255Labels permutation434 hz
    mixedMoment B raw17255step0 raw17255step0Labels = mixedMoment B raw17255step1 raw17255step1Labels := by
      have ha : raw17255step1 = (fun i j => raw17255step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17255step1 raw17255step0; decide +kernel
      have hl : raw17255step1Labels = raw17255step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17255step0 raw17255step0Labels permutation143 permutation7
    mixedMoment B raw17255step1 raw17255step1Labels = mixedMoment B raw17255step2 raw17255step2Labels := by
      have ha : raw17255step2 = raw17255step1 := by apply Matrix.ext; unfold raw17255step2 raw17255step1; decide +kernel
      have hl : raw17255step1Labels = labelEmbedding10 ∘ raw17255step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17255step1 raw17255step1Labels raw17255step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw17256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw17256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw17256step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17256step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17256step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17256 raw17256Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw17256 raw17256Labels = mixedMoment B raw17256step0 raw17256step0Labels := by
      have hz : ∀ j, raw17256 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17256step0 = (fun i j => raw17256 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17256step0 raw17256; decide +kernel
      have hl : raw17256step0Labels = raw17256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17256 raw17256Labels permutation434 hz
    mixedMoment B raw17256step0 raw17256step0Labels = mixedMoment B raw17256step1 raw17256step1Labels := by
      have ha : raw17256step1 = (fun i j => raw17256step0 (permutation110 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17256step1 raw17256step0; decide +kernel
      have hl : raw17256step1Labels = raw17256step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17256step0 raw17256step0Labels permutation110 permutation4
    mixedMoment B raw17256step1 raw17256step1Labels = mixedMoment B raw17256step2 raw17256step2Labels := by
      have ha : raw17256step2 = raw17256step1 := by apply Matrix.ext; unfold raw17256step2 raw17256step1; decide +kernel
      have hl : raw17256step1Labels = labelEmbedding7 ∘ raw17256step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17256step1 raw17256step1Labels raw17256step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw17257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17257step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17257step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17257step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17257step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17257 raw17257Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw17257 raw17257Labels = mixedMoment B raw17257step0 raw17257step0Labels := by
      have hz : ∀ j, raw17257 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17257step0 = (fun i j => raw17257 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17257step0 raw17257; decide +kernel
      have hl : raw17257step0Labels = raw17257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17257 raw17257Labels permutation434 hz
    mixedMoment B raw17257step0 raw17257step0Labels = mixedMoment B raw17257step1 raw17257step1Labels := by
      have ha : raw17257step1 = (fun i j => raw17257step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17257step1 raw17257step0; decide +kernel
      have hl : raw17257step1Labels = raw17257step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17257step0 raw17257step0Labels permutation32 permutation3
    mixedMoment B raw17257step1 raw17257step1Labels = mixedMoment B raw17257step2 raw17257step2Labels := by
      have ha : raw17257step2 = raw17257step1 := by apply Matrix.ext; unfold raw17257step2 raw17257step1; decide +kernel
      have hl : raw17257step1Labels = labelEmbedding6 ∘ raw17257step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17257step1 raw17257step1Labels raw17257step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw17258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17258step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17258step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17258step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17258step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17258 raw17258Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw17258 raw17258Labels = mixedMoment B raw17258step0 raw17258step0Labels := by
      have hz : ∀ j, raw17258 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17258step0 = (fun i j => raw17258 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17258step0 raw17258; decide +kernel
      have hl : raw17258step0Labels = raw17258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17258 raw17258Labels permutation434 hz
    mixedMoment B raw17258step0 raw17258step0Labels = mixedMoment B raw17258step1 raw17258step1Labels := by
      have ha : raw17258step1 = (fun i j => raw17258step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17258step1 raw17258step0; decide +kernel
      have hl : raw17258step1Labels = raw17258step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17258step0 raw17258step0Labels permutation144 permutation2
    mixedMoment B raw17258step1 raw17258step1Labels = mixedMoment B raw17258step2 raw17258step2Labels := by
      have ha : raw17258step2 = -raw17258step1 := by apply Matrix.ext; change ∀ i j, raw17258step2 i j = -(raw17258step1 i j); unfold raw17258step2 raw17258step1; decide +kernel
      have hl : raw17258step2Labels = raw17258step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5404 node5404Labels := by rfl

def raw17259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17259step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17259 raw17259Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw17259 raw17259Labels = mixedMoment B raw17259step0 raw17259step0Labels := by
      have ha : raw17259step0 = (fun i j => raw17259 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17259step0 raw17259; decide +kernel
      have hl : raw17259step0Labels = raw17259Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17259 raw17259Labels permutation646 permutation2
    mixedMoment B raw17259step0 raw17259step0Labels = mixedMoment B raw17259step1 raw17259step1Labels := by
      have ha : raw17259step1 = -raw17259step0 := by apply Matrix.ext; change ∀ i j, raw17259step1 i j = -(raw17259step0 i j); unfold raw17259step1 raw17259step0; decide +kernel
      have hl : raw17259step1Labels = raw17259step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw17260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw17260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17260step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17260step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17260step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17260 raw17260Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw17260 raw17260Labels = mixedMoment B raw17260step0 raw17260step0Labels := by
      have hz : ∀ j, raw17260 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17260step0 = (fun i j => raw17260 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17260step0 raw17260; decide +kernel
      have hl : raw17260step0Labels = raw17260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17260 raw17260Labels permutation434 hz
    mixedMoment B raw17260step0 raw17260step0Labels = mixedMoment B raw17260step1 raw17260step1Labels := by
      have ha : raw17260step1 = (fun i j => raw17260step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17260step1 raw17260step0; decide +kernel
      have hl : raw17260step1Labels = raw17260step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17260step0 raw17260step0Labels permutation145 permutation2
    mixedMoment B raw17260step1 raw17260step1Labels = mixedMoment B raw17260step2 raw17260step2Labels := by
      have ha : raw17260step2 = -raw17260step1 := by apply Matrix.ext; change ∀ i j, raw17260step2 i j = -(raw17260step1 i j); unfold raw17260step2 raw17260step1; decide +kernel
      have hl : raw17260step2Labels = raw17260step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw17261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw17261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw17261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17261step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17261 raw17261Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw17261 raw17261Labels = mixedMoment B raw17261step0 raw17261step0Labels := by
      have hz : ∀ j, raw17261 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17261step0 = (fun i j => raw17261 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17261step0 raw17261; decide +kernel
      have hl : raw17261step0Labels = raw17261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17261 raw17261Labels permutation434 hz
    mixedMoment B raw17261step0 raw17261step0Labels = mixedMoment B raw17261step1 raw17261step1Labels := by
      have ha : raw17261step1 = (fun i j => raw17261step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17261step1 raw17261step0; decide +kernel
      have hl : raw17261step1Labels = raw17261step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17261step0 raw17261step0Labels permutation34 permutation2
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw17262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17262step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17262step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17262step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17262 raw17262Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw17262 raw17262Labels = mixedMoment B raw17262step0 raw17262step0Labels := by
      have ha : raw17262step0 = (fun i j => raw17262 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17262step0 raw17262; decide +kernel
      have hl : raw17262step0Labels = raw17262Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17262 raw17262Labels permutation152 permutation3
    mixedMoment B raw17262step0 raw17262step0Labels = mixedMoment B raw17262step1 raw17262step1Labels := by
      have ha : raw17262step1 = raw17262step0 := by apply Matrix.ext; unfold raw17262step1 raw17262step0; decide +kernel
      have hl : raw17262step0Labels = labelEmbedding6 ∘ raw17262step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17262step0 raw17262step0Labels raw17262step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5138 node5138Labels := by rfl

def raw17263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17263step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17263step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17263step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17263 raw17263Labels = mixedMoment B node5419 node5419Labels := by
  calc
    mixedMoment B raw17263 raw17263Labels = mixedMoment B raw17263step0 raw17263step0Labels := by
      have ha : raw17263step0 = (fun i j => raw17263 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17263step0 raw17263; decide +kernel
      have hl : raw17263step0Labels = raw17263Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17263 raw17263Labels permutation663 permutation2
    mixedMoment B raw17263step0 raw17263step0Labels = mixedMoment B raw17263step1 raw17263step1Labels := by
      have ha : raw17263step1 = -raw17263step0 := by apply Matrix.ext; change ∀ i j, raw17263step1 i j = -(raw17263step0 i j); unfold raw17263step1 raw17263step0; decide +kernel
      have hl : raw17263step1Labels = raw17263step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5419 node5419Labels := by rfl

def raw17264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17264step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17264step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17264 raw17264Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw17264 raw17264Labels = mixedMoment B raw17264step0 raw17264step0Labels := by
      have ha : raw17264step0 = (fun i j => raw17264 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17264step0 raw17264; decide +kernel
      have hl : raw17264step0Labels = raw17264Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17264 raw17264Labels permutation664 permutation2
    mixedMoment B raw17264step0 raw17264step0Labels = mixedMoment B raw17264step1 raw17264step1Labels := by
      have ha : raw17264step1 = -raw17264step0 := by apply Matrix.ext; change ∀ i j, raw17264step1 i j = -(raw17264step0 i j); unfold raw17264step1 raw17264step0; decide +kernel
      have hl : raw17264step1Labels = raw17264step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5421 node5421Labels := by rfl

def raw17265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw17265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17265step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17265step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17265step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17265 raw17265Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw17265 raw17265Labels = mixedMoment B raw17265step0 raw17265step0Labels := by
      have ha : raw17265step0 = (fun i j => raw17265 (permutation658 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17265step0 raw17265; decide +kernel
      have hl : raw17265step0Labels = raw17265Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17265 raw17265Labels permutation658 permutation2
    mixedMoment B raw17265step0 raw17265step0Labels = mixedMoment B raw17265step1 raw17265step1Labels := by
      have ha : raw17265step1 = -raw17265step0 := by apply Matrix.ext; change ∀ i j, raw17265step1 i j = -(raw17265step0 i j); unfold raw17265step1 raw17265step0; decide +kernel
      have hl : raw17265step1Labels = raw17265step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw17266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw17266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17266step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17266 raw17266Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw17266 raw17266Labels = mixedMoment B raw17266step0 raw17266step0Labels := by
      have ha : raw17266step0 = (fun i j => raw17266 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17266step0 raw17266; decide +kernel
      have hl : raw17266step0Labels = raw17266Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17266 raw17266Labels permutation154 permutation2
    _ = mixedMoment B node5480 node5480Labels := by rfl

def raw17267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw17267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw17267step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw17267step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17267 raw17267Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw17267 raw17267Labels = mixedMoment B raw17267step0 raw17267step0Labels := by
      have hz : ∀ j, raw17267 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17267step0 = (fun i j => raw17267 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17267step0 raw17267; decide +kernel
      have hl : raw17267step0Labels = raw17267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17267 raw17267Labels permutation434 hz
    mixedMoment B raw17267step0 raw17267step0Labels = mixedMoment B raw17267step1 raw17267step1Labels := by
      have ha : raw17267step1 = (fun i j => raw17267step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17267step1 raw17267step0; decide +kernel
      have hl : raw17267step1Labels = raw17267step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17267step0 raw17267step0Labels permutation33 permutation3
    mixedMoment B raw17267step1 raw17267step1Labels = mixedMoment B raw17267step2 raw17267step2Labels := by
      have ha : raw17267step2 = raw17267step1 := by apply Matrix.ext; unfold raw17267step2 raw17267step1; decide +kernel
      have hl : raw17267step1Labels = labelEmbedding6 ∘ raw17267step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17267step1 raw17267step1Labels raw17267step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5140 node5140Labels := by rfl

def raw17268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw17268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17268step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17268step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17268 raw17268Labels = mixedMoment B node5236 node5236Labels := by
  calc
    mixedMoment B raw17268 raw17268Labels = mixedMoment B raw17268step0 raw17268step0Labels := by
      have hz : ∀ j, raw17268 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17268step0 = (fun i j => raw17268 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17268step0 raw17268; decide +kernel
      have hl : raw17268step0Labels = raw17268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17268 raw17268Labels permutation434 hz
    mixedMoment B raw17268step0 raw17268step0Labels = mixedMoment B raw17268step1 raw17268step1Labels := by
      have ha : raw17268step1 = (fun i j => raw17268step0 (permutation126 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17268step1 raw17268step0; decide +kernel
      have hl : raw17268step1Labels = raw17268step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17268step0 raw17268step0Labels permutation126 permutation5
    mixedMoment B raw17268step1 raw17268step1Labels = mixedMoment B raw17268step2 raw17268step2Labels := by
      have ha : raw17268step2 = raw17268step1 := by apply Matrix.ext; unfold raw17268step2 raw17268step1; decide +kernel
      have hl : raw17268step1Labels = labelEmbedding8 ∘ raw17268step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17268step1 raw17268step1Labels raw17268step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5236 node5236Labels := by rfl

def raw17269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw17269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17269step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17269step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17269step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17269step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17269 raw17269Labels = mixedMoment B node5229 node5229Labels := by
  calc
    mixedMoment B raw17269 raw17269Labels = mixedMoment B raw17269step0 raw17269step0Labels := by
      have hz : ∀ j, raw17269 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17269step0 = (fun i j => raw17269 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17269step0 raw17269; decide +kernel
      have hl : raw17269step0Labels = raw17269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17269 raw17269Labels permutation434 hz
    mixedMoment B raw17269step0 raw17269step0Labels = mixedMoment B raw17269step1 raw17269step1Labels := by
      have ha : raw17269step1 = (fun i j => raw17269step0 (permutation124 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17269step1 raw17269step0; decide +kernel
      have hl : raw17269step1Labels = raw17269step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17269step0 raw17269step0Labels permutation124 permutation5
    mixedMoment B raw17269step1 raw17269step1Labels = mixedMoment B raw17269step2 raw17269step2Labels := by
      have ha : raw17269step2 = raw17269step1 := by apply Matrix.ext; unfold raw17269step2 raw17269step1; decide +kernel
      have hl : raw17269step1Labels = labelEmbedding8 ∘ raw17269step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17269step1 raw17269step1Labels raw17269step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5229 node5229Labels := by rfl

def raw17270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17270step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17270step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17270step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17270 raw17270Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw17270 raw17270Labels = mixedMoment B raw17270step0 raw17270step0Labels := by
      have ha : raw17270step0 = (fun i j => raw17270 (permutation577 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17270step0 raw17270; decide +kernel
      have hl : raw17270step0Labels = raw17270Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17270 raw17270Labels permutation577 permutation5
    mixedMoment B raw17270step0 raw17270step0Labels = mixedMoment B raw17270step1 raw17270step1Labels := by
      have ha : raw17270step1 = raw17270step0 := by apply Matrix.ext; unfold raw17270step1 raw17270step0; decide +kernel
      have hl : raw17270step0Labels = labelEmbedding8 ∘ raw17270step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17270step0 raw17270step0Labels raw17270step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw17271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw17271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw17271step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17271step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17271step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17271step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17271 raw17271Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw17271 raw17271Labels = mixedMoment B raw17271step0 raw17271step0Labels := by
      have hz : ∀ j, raw17271 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17271step0 = (fun i j => raw17271 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17271step0 raw17271; decide +kernel
      have hl : raw17271step0Labels = raw17271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17271 raw17271Labels permutation434 hz
    mixedMoment B raw17271step0 raw17271step0Labels = mixedMoment B raw17271step1 raw17271step1Labels := by
      have ha : raw17271step1 = (fun i j => raw17271step0 (permutation115 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17271step1 raw17271step0; decide +kernel
      have hl : raw17271step1Labels = raw17271step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17271step0 raw17271step0Labels permutation115 permutation5
    mixedMoment B raw17271step1 raw17271step1Labels = mixedMoment B raw17271step2 raw17271step2Labels := by
      have ha : raw17271step2 = raw17271step1 := by apply Matrix.ext; unfold raw17271step2 raw17271step1; decide +kernel
      have hl : raw17271step1Labels = labelEmbedding8 ∘ raw17271step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17271step1 raw17271step1Labels raw17271step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw17272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17272step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17272step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17272 raw17272Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw17272 raw17272Labels = mixedMoment B raw17272step0 raw17272step0Labels := by
      have hz : ∀ j, raw17272 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17272step0 = (fun i j => raw17272 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17272step0 raw17272; decide +kernel
      have hl : raw17272step0Labels = raw17272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17272 raw17272Labels permutation434 hz
    mixedMoment B raw17272step0 raw17272step0Labels = mixedMoment B raw17272step1 raw17272step1Labels := by
      have ha : raw17272step1 = (fun i j => raw17272step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17272step1 raw17272step0; decide +kernel
      have hl : raw17272step1Labels = raw17272step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17272step0 raw17272step0Labels permutation32 permutation3
    mixedMoment B raw17272step1 raw17272step1Labels = mixedMoment B raw17272step2 raw17272step2Labels := by
      have ha : raw17272step2 = raw17272step1 := by apply Matrix.ext; unfold raw17272step2 raw17272step1; decide +kernel
      have hl : raw17272step1Labels = labelEmbedding6 ∘ raw17272step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17272step1 raw17272step1Labels raw17272step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5139 node5139Labels := by rfl

def raw17273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17273step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17273step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17273 raw17273Labels = mixedMoment B node5189 node5189Labels := by
  calc
    mixedMoment B raw17273 raw17273Labels = mixedMoment B raw17273step0 raw17273step0Labels := by
      have hz : ∀ j, raw17273 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17273step0 = (fun i j => raw17273 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17273step0 raw17273; decide +kernel
      have hl : raw17273step0Labels = raw17273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17273 raw17273Labels permutation434 hz
    mixedMoment B raw17273step0 raw17273step0Labels = mixedMoment B raw17273step1 raw17273step1Labels := by
      have ha : raw17273step1 = (fun i j => raw17273step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17273step1 raw17273step0; decide +kernel
      have hl : raw17273step1Labels = raw17273step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17273step0 raw17273step0Labels permutation150 permutation2
    mixedMoment B raw17273step1 raw17273step1Labels = mixedMoment B raw17273step2 raw17273step2Labels := by
      have ha : raw17273step2 = -raw17273step1 := by apply Matrix.ext; change ∀ i j, raw17273step2 i j = -(raw17273step1 i j); unfold raw17273step2 raw17273step1; decide +kernel
      have hl : raw17273step2Labels = raw17273step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5189 node5189Labels := by rfl

def raw17274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17274step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17274step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17274step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17274step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17274 raw17274Labels = mixedMoment B node5199 node5199Labels := by
  calc
    mixedMoment B raw17274 raw17274Labels = mixedMoment B raw17274step0 raw17274step0Labels := by
      have hz : ∀ j, raw17274 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17274step0 = (fun i j => raw17274 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17274step0 raw17274; decide +kernel
      have hl : raw17274step0Labels = raw17274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17274 raw17274Labels permutation434 hz
    mixedMoment B raw17274step0 raw17274step0Labels = mixedMoment B raw17274step1 raw17274step1Labels := by
      have ha : raw17274step1 = (fun i j => raw17274step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17274step1 raw17274step0; decide +kernel
      have hl : raw17274step1Labels = raw17274step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17274step0 raw17274step0Labels permutation151 permutation2
    mixedMoment B raw17274step1 raw17274step1Labels = mixedMoment B raw17274step2 raw17274step2Labels := by
      have ha : raw17274step2 = -raw17274step1 := by apply Matrix.ext; change ∀ i j, raw17274step2 i j = -(raw17274step1 i j); unfold raw17274step2 raw17274step1; decide +kernel
      have hl : raw17274step2Labels = raw17274step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5199 node5199Labels := by rfl

def raw17275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17275step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17275step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17275 raw17275Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw17275 raw17275Labels = mixedMoment B raw17275step0 raw17275step0Labels := by
      have ha : raw17275step0 = (fun i j => raw17275 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17275step0 raw17275; decide +kernel
      have hl : raw17275step0Labels = raw17275Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17275 raw17275Labels permutation682 permutation2
    mixedMoment B raw17275step0 raw17275step0Labels = mixedMoment B raw17275step1 raw17275step1Labels := by
      have ha : raw17275step1 = -raw17275step0 := by apply Matrix.ext; change ∀ i j, raw17275step1 i j = -(raw17275step0 i j); unfold raw17275step1 raw17275step0; decide +kernel
      have hl : raw17275step1Labels = raw17275step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5185 node5185Labels := by rfl

def raw17276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw17276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw17276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17276step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17276step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17276 raw17276Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw17276 raw17276Labels = mixedMoment B raw17276step0 raw17276step0Labels := by
      have hz : ∀ j, raw17276 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17276step0 = (fun i j => raw17276 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17276step0 raw17276; decide +kernel
      have hl : raw17276step0Labels = raw17276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17276 raw17276Labels permutation434 hz
    mixedMoment B raw17276step0 raw17276step0Labels = mixedMoment B raw17276step1 raw17276step1Labels := by
      have ha : raw17276step1 = (fun i j => raw17276step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17276step1 raw17276step0; decide +kernel
      have hl : raw17276step1Labels = raw17276step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17276step0 raw17276step0Labels permutation145 permutation2
    mixedMoment B raw17276step1 raw17276step1Labels = mixedMoment B raw17276step2 raw17276step2Labels := by
      have ha : raw17276step2 = -raw17276step1 := by apply Matrix.ext; change ∀ i j, raw17276step2 i j = -(raw17276step1 i j); unfold raw17276step2 raw17276step1; decide +kernel
      have hl : raw17276step2Labels = raw17276step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw17277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17277Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17277step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17277step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17277step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17277step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17277 raw17277Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw17277 raw17277Labels = mixedMoment B raw17277step0 raw17277step0Labels := by
      have hz : ∀ j, raw17277 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17277step0 = (fun i j => raw17277 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17277step0 raw17277; decide +kernel
      have hl : raw17277step0Labels = raw17277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17277 raw17277Labels permutation434 hz
    mixedMoment B raw17277step0 raw17277step0Labels = mixedMoment B raw17277step1 raw17277step1Labels := by
      have ha : raw17277step1 = (fun i j => raw17277step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17277step1 raw17277step0; decide +kernel
      have hl : raw17277step1Labels = raw17277step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17277step0 raw17277step0Labels permutation144 permutation7
    mixedMoment B raw17277step1 raw17277step1Labels = mixedMoment B raw17277step2 raw17277step2Labels := by
      have ha : raw17277step2 = raw17277step1 := by apply Matrix.ext; unfold raw17277step2 raw17277step1; decide +kernel
      have hl : raw17277step1Labels = labelEmbedding1 ∘ raw17277step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17277step1 raw17277step1Labels raw17277step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3857 node3857Labels := by rfl

def raw17278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17278Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17278step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17278step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17278step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17278step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17278 raw17278Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw17278 raw17278Labels = mixedMoment B raw17278step0 raw17278step0Labels := by
      have hz : ∀ j, raw17278 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17278step0 = (fun i j => raw17278 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17278step0 raw17278; decide +kernel
      have hl : raw17278step0Labels = raw17278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17278 raw17278Labels permutation434 hz
    mixedMoment B raw17278step0 raw17278step0Labels = mixedMoment B raw17278step1 raw17278step1Labels := by
      have ha : raw17278step1 = (fun i j => raw17278step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17278step1 raw17278step0; decide +kernel
      have hl : raw17278step1Labels = raw17278step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17278step0 raw17278step0Labels permutation144 permutation7
    mixedMoment B raw17278step1 raw17278step1Labels = mixedMoment B raw17278step2 raw17278step2Labels := by
      have ha : raw17278step2 = raw17278step1 := by apply Matrix.ext; unfold raw17278step2 raw17278step1; decide +kernel
      have hl : raw17278step1Labels = labelEmbedding1 ∘ raw17278step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17278step1 raw17278step1Labels raw17278step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3885 node3885Labels := by rfl

def raw17279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17279Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17279step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17279step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17279step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17279 raw17279Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw17279 raw17279Labels = mixedMoment B raw17279step0 raw17279step0Labels := by
      have ha : raw17279step0 = (fun i j => raw17279 (permutation639 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17279step0 raw17279; decide +kernel
      have hl : raw17279step0Labels = raw17279Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17279 raw17279Labels permutation639 permutation7
    mixedMoment B raw17279step0 raw17279step0Labels = mixedMoment B raw17279step1 raw17279step1Labels := by
      have ha : raw17279step1 = raw17279step0 := by apply Matrix.ext; unfold raw17279step1 raw17279step0; decide +kernel
      have hl : raw17279step0Labels = labelEmbedding1 ∘ raw17279step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17279step0 raw17279step0Labels raw17279step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3849 node3849Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
