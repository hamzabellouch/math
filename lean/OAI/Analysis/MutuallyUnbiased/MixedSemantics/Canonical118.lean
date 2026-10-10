import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw15104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15104Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15104step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw15104step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15104 raw15104Labels = mixedMoment B node3694 node3694Labels := by
  calc
    mixedMoment B raw15104 raw15104Labels = mixedMoment B raw15104step0 raw15104step0Labels := by
      have hz : ∀ j, raw15104 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15104step0 = (fun i j => raw15104 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15104step0 raw15104; decide +kernel
      have hl : raw15104step0Labels = raw15104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15104 raw15104Labels permutation346 hz
    mixedMoment B raw15104step0 raw15104step0Labels = mixedMoment B raw15104step1 raw15104step1Labels := by
      have ha : raw15104step1 = (fun i j => raw15104step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15104step1 raw15104step0; decide +kernel
      have hl : raw15104step1Labels = raw15104step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15104step0 raw15104step0Labels permutation32 permutation3
    _ = mixedMoment B node3694 node3694Labels := by rfl

def raw15105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15105Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15105step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw15105step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15105 raw15105Labels = mixedMoment B node3779 node3779Labels := by
  calc
    mixedMoment B raw15105 raw15105Labels = mixedMoment B raw15105step0 raw15105step0Labels := by
      have ha : raw15105step0 = (fun i j => raw15105 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15105step0 raw15105; decide +kernel
      have hl : raw15105step0Labels = raw15105Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15105 raw15105Labels permutation176 permutation3
    _ = mixedMoment B node3779 node3779Labels := by rfl

def raw15106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15106Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw15106step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw15106step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15106 raw15106Labels = mixedMoment B node3824 node3824Labels := by
  calc
    mixedMoment B raw15106 raw15106Labels = mixedMoment B raw15106step0 raw15106step0Labels := by
      have hz : ∀ j, raw15106 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15106step0 = (fun i j => raw15106 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15106step0 raw15106; decide +kernel
      have hl : raw15106step0Labels = raw15106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15106 raw15106Labels permutation346 hz
    mixedMoment B raw15106step0 raw15106step0Labels = mixedMoment B raw15106step1 raw15106step1Labels := by
      have ha : raw15106step1 = (fun i j => raw15106step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15106step1 raw15106step0; decide +kernel
      have hl : raw15106step1Labels = raw15106step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15106step0 raw15106step0Labels permutation32 permutation3
    _ = mixedMoment B node3824 node3824Labels := by rfl

def raw15107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw15107Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw15107step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15107 raw15107Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw15107 raw15107Labels = mixedMoment B raw15107step0 raw15107step0Labels := by
      have hz : ∀ j, raw15107 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15107step0 = (fun i j => raw15107 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15107step0 raw15107; decide +kernel
      have hl : raw15107step0Labels = raw15107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15107 raw15107Labels permutation346 hz
    mixedMoment B raw15107step0 raw15107step0Labels = mixedMoment B raw15107step1 raw15107step1Labels := by
      have ha : raw15107step1 = (fun i j => raw15107step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15107step1 raw15107step0; decide +kernel
      have hl : raw15107step1Labels = raw15107step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15107step0 raw15107step0Labels permutation33 permutation3
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw15108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15108Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15108step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw15108step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15108 raw15108Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw15108 raw15108Labels = mixedMoment B raw15108step0 raw15108step0Labels := by
      have hz : ∀ j, raw15108 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15108step0 = (fun i j => raw15108 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15108step0 raw15108; decide +kernel
      have hl : raw15108step0Labels = raw15108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15108 raw15108Labels permutation346 hz
    mixedMoment B raw15108step0 raw15108step0Labels = mixedMoment B raw15108step1 raw15108step1Labels := by
      have ha : raw15108step1 = (fun i j => raw15108step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15108step1 raw15108step0; decide +kernel
      have hl : raw15108step1Labels = raw15108step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15108step0 raw15108step0Labels permutation32 permutation3
    _ = mixedMoment B node2022 node2022Labels := by rfl

def raw15109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15109Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15109step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw15109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15109step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15109step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15109 raw15109Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw15109 raw15109Labels = mixedMoment B raw15109step0 raw15109step0Labels := by
      have hz : ∀ j, raw15109 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15109step0 = (fun i j => raw15109 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15109step0 raw15109; decide +kernel
      have hl : raw15109step0Labels = raw15109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15109 raw15109Labels permutation346 hz
    mixedMoment B raw15109step0 raw15109step0Labels = mixedMoment B raw15109step1 raw15109step1Labels := by
      have ha : raw15109step1 = (fun i j => raw15109step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15109step1 raw15109step0; decide +kernel
      have hl : raw15109step1Labels = raw15109step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15109step0 raw15109step0Labels permutation151 permutation3
    mixedMoment B raw15109step1 raw15109step1Labels = mixedMoment B raw15109step2 raw15109step2Labels := by
      have ha : raw15109step2 = -raw15109step1 := by apply Matrix.ext; change ∀ i j, raw15109step2 i j = -(raw15109step1 i j); unfold raw15109step2 raw15109step1; decide +kernel
      have hl : raw15109step2Labels = raw15109step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2561 node2561Labels := by rfl

def raw15110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15110Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15110step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15110step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15110step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15110 raw15110Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw15110 raw15110Labels = mixedMoment B raw15110step0 raw15110step0Labels := by
      have ha : raw15110step0 = (fun i j => raw15110 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15110step0 raw15110; decide +kernel
      have hl : raw15110step0Labels = raw15110Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15110 raw15110Labels permutation686 permutation3
    mixedMoment B raw15110step0 raw15110step0Labels = mixedMoment B raw15110step1 raw15110step1Labels := by
      have ha : raw15110step1 = -raw15110step0 := by apply Matrix.ext; change ∀ i j, raw15110step1 i j = -(raw15110step0 i j); unfold raw15110step1 raw15110step0; decide +kernel
      have hl : raw15110step1Labels = raw15110step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2553 node2553Labels := by rfl

def raw15111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15111Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw15111step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15111step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15111step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15111step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15111 raw15111Labels = mixedMoment B node2594 node2594Labels := by
  calc
    mixedMoment B raw15111 raw15111Labels = mixedMoment B raw15111step0 raw15111step0Labels := by
      have hz : ∀ j, raw15111 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15111step0 = (fun i j => raw15111 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15111step0 raw15111; decide +kernel
      have hl : raw15111step0Labels = raw15111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15111 raw15111Labels permutation346 hz
    mixedMoment B raw15111step0 raw15111step0Labels = mixedMoment B raw15111step1 raw15111step1Labels := by
      have ha : raw15111step1 = (fun i j => raw15111step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15111step1 raw15111step0; decide +kernel
      have hl : raw15111step1Labels = raw15111step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15111step0 raw15111step0Labels permutation149 permutation3
    mixedMoment B raw15111step1 raw15111step1Labels = mixedMoment B raw15111step2 raw15111step2Labels := by
      have ha : raw15111step2 = -raw15111step1 := by apply Matrix.ext; change ∀ i j, raw15111step2 i j = -(raw15111step1 i j); unfold raw15111step2 raw15111step1; decide +kernel
      have hl : raw15111step2Labels = raw15111step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2594 node2594Labels := by rfl

def raw15112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw15112Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw15112step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw15112step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw15112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15112 raw15112Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw15112 raw15112Labels = mixedMoment B raw15112step0 raw15112step0Labels := by
      have hz : ∀ j, raw15112 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15112step0 = (fun i j => raw15112 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15112step0 raw15112; decide +kernel
      have hl : raw15112step0Labels = raw15112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15112 raw15112Labels permutation346 hz
    mixedMoment B raw15112step0 raw15112step0Labels = mixedMoment B raw15112step1 raw15112step1Labels := by
      have ha : raw15112step1 = (fun i j => raw15112step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15112step1 raw15112step0; decide +kernel
      have hl : raw15112step1Labels = raw15112step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15112step0 raw15112step0Labels permutation145 permutation3
    mixedMoment B raw15112step1 raw15112step1Labels = mixedMoment B raw15112step2 raw15112step2Labels := by
      have ha : raw15112step2 = -raw15112step1 := by apply Matrix.ext; change ∀ i j, raw15112step2 i j = -(raw15112step1 i j); unfold raw15112step2 raw15112step1; decide +kernel
      have hl : raw15112step2Labels = raw15112step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw15113 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15113step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15113step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15113step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15113 raw15113Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw15113 raw15113Labels = mixedMoment B raw15113step0 raw15113step0Labels := by
      have hz : ∀ j, raw15113 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15113step0 = (fun i j => raw15113 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15113step0 raw15113; decide +kernel
      have hl : raw15113step0Labels = raw15113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15113 raw15113Labels permutation346 hz
    mixedMoment B raw15113step0 raw15113step0Labels = mixedMoment B raw15113step1 raw15113step1Labels := by
      have ha : raw15113step1 = (fun i j => raw15113step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15113step1 raw15113step0; decide +kernel
      have hl : raw15113step1Labels = raw15113step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15113step0 raw15113step0Labels permutation32 permutation6
    mixedMoment B raw15113step1 raw15113step1Labels = mixedMoment B raw15113step2 raw15113step2Labels := by
      have ha : raw15113step2 = raw15113step1 := by apply Matrix.ext; unfold raw15113step2 raw15113step1; decide +kernel
      have hl : raw15113step1Labels = labelEmbedding9 ∘ raw15113step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15113step1 raw15113step1Labels raw15113step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw15114 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15114Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15114step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15114step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15114step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15114 raw15114Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw15114 raw15114Labels = mixedMoment B raw15114step0 raw15114step0Labels := by
      have ha : raw15114step0 = (fun i j => raw15114 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15114step0 raw15114; decide +kernel
      have hl : raw15114step0Labels = raw15114Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15114 raw15114Labels permutation158 permutation7
    mixedMoment B raw15114step0 raw15114step0Labels = mixedMoment B raw15114step1 raw15114step1Labels := by
      have ha : raw15114step1 = raw15114step0 := by apply Matrix.ext; unfold raw15114step1 raw15114step0; decide +kernel
      have hl : raw15114step0Labels = labelEmbedding10 ∘ raw15114step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15114step0 raw15114step0Labels raw15114step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

def raw15115 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15115step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15115step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15115step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15115step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15115step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15115step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15115step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15115 raw15115Labels = mixedMoment B node5487 node5487Labels := by
  calc
    mixedMoment B raw15115 raw15115Labels = mixedMoment B raw15115step0 raw15115step0Labels := by
      have hz : ∀ j, raw15115 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15115step0 = (fun i j => raw15115 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15115step0 raw15115; decide +kernel
      have hl : raw15115step0Labels = raw15115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15115 raw15115Labels permutation434 hz
    mixedMoment B raw15115step0 raw15115step0Labels = mixedMoment B raw15115step1 raw15115step1Labels := by
      have hz : ∀ j, raw15115step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15115step1 = (fun i j => raw15115step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15115step1 raw15115step0; decide +kernel
      have hl : raw15115step1Labels = raw15115step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15115step0 raw15115step0Labels permutation80 hz
    mixedMoment B raw15115step1 raw15115step1Labels = mixedMoment B raw15115step2 raw15115step2Labels := by
      have ha : raw15115step2 = (fun i j => raw15115step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15115step2 raw15115step1; decide +kernel
      have hl : raw15115step2Labels = raw15115step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15115step1 raw15115step1Labels permutation8 permutation7
    mixedMoment B raw15115step2 raw15115step2Labels = mixedMoment B raw15115step3 raw15115step3Labels := by
      have ha : raw15115step3 = raw15115step2 := by apply Matrix.ext; unfold raw15115step3 raw15115step2; decide +kernel
      have hl : raw15115step2Labels = labelEmbedding10 ∘ raw15115step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15115step2 raw15115step2Labels raw15115step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5487 node5487Labels := by rfl

def raw15116 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15116step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15116step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15116step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15116step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15116step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15116step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15116 raw15116Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw15116 raw15116Labels = mixedMoment B raw15116step0 raw15116step0Labels := by
      have hz : ∀ j, raw15116 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15116step0 = (fun i j => raw15116 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15116step0 raw15116; decide +kernel
      have hl : raw15116step0Labels = raw15116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15116 raw15116Labels permutation346 hz
    mixedMoment B raw15116step0 raw15116step0Labels = mixedMoment B raw15116step1 raw15116step1Labels := by
      have ha : raw15116step1 = (fun i j => raw15116step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15116step1 raw15116step0; decide +kernel
      have hl : raw15116step1Labels = raw15116step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15116step0 raw15116step0Labels permutation151 permutation7
    mixedMoment B raw15116step1 raw15116step1Labels = mixedMoment B raw15116step2 raw15116step2Labels := by
      have ha : raw15116step2 = -raw15116step1 := by apply Matrix.ext; change ∀ i j, raw15116step2 i j = -(raw15116step1 i j); unfold raw15116step2 raw15116step1; decide +kernel
      have hl : raw15116step2Labels = raw15116step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15116step2 raw15116step2Labels = mixedMoment B raw15116step3 raw15116step3Labels := by
      have ha : raw15116step3 = raw15116step2 := by apply Matrix.ext; unfold raw15116step3 raw15116step2; decide +kernel
      have hl : raw15116step2Labels = labelEmbedding10 ∘ raw15116step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15116step2 raw15116step2Labels raw15116step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw15117 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15117Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15117step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15117step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15117step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15117step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15117step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15117step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15117 raw15117Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw15117 raw15117Labels = mixedMoment B raw15117step0 raw15117step0Labels := by
      have hz : ∀ j, raw15117 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15117step0 = (fun i j => raw15117 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15117step0 raw15117; decide +kernel
      have hl : raw15117step0Labels = raw15117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15117 raw15117Labels permutation346 hz
    mixedMoment B raw15117step0 raw15117step0Labels = mixedMoment B raw15117step1 raw15117step1Labels := by
      have ha : raw15117step1 = (fun i j => raw15117step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15117step1 raw15117step0; decide +kernel
      have hl : raw15117step1Labels = raw15117step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15117step0 raw15117step0Labels permutation151 permutation7
    mixedMoment B raw15117step1 raw15117step1Labels = mixedMoment B raw15117step2 raw15117step2Labels := by
      have ha : raw15117step2 = -raw15117step1 := by apply Matrix.ext; change ∀ i j, raw15117step2 i j = -(raw15117step1 i j); unfold raw15117step2 raw15117step1; decide +kernel
      have hl : raw15117step2Labels = raw15117step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15117step2 raw15117step2Labels = mixedMoment B raw15117step3 raw15117step3Labels := by
      have ha : raw15117step3 = raw15117step2 := by apply Matrix.ext; unfold raw15117step3 raw15117step2; decide +kernel
      have hl : raw15117step2Labels = labelEmbedding10 ∘ raw15117step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15117step2 raw15117step2Labels raw15117step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw15118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15118step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15118step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15118step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15118step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15118step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15118 raw15118Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw15118 raw15118Labels = mixedMoment B raw15118step0 raw15118step0Labels := by
      have hz : ∀ j, raw15118 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15118step0 = (fun i j => raw15118 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15118step0 raw15118; decide +kernel
      have hl : raw15118step0Labels = raw15118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15118 raw15118Labels permutation346 hz
    mixedMoment B raw15118step0 raw15118step0Labels = mixedMoment B raw15118step1 raw15118step1Labels := by
      have ha : raw15118step1 = (fun i j => raw15118step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15118step1 raw15118step0; decide +kernel
      have hl : raw15118step1Labels = raw15118step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15118step0 raw15118step0Labels permutation44 permutation4
    mixedMoment B raw15118step1 raw15118step1Labels = mixedMoment B raw15118step2 raw15118step2Labels := by
      have ha : raw15118step2 = -raw15118step1 := by apply Matrix.ext; change ∀ i j, raw15118step2 i j = -(raw15118step1 i j); unfold raw15118step2 raw15118step1; decide +kernel
      have hl : raw15118step2Labels = raw15118step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15118step2 raw15118step2Labels = mixedMoment B raw15118step3 raw15118step3Labels := by
      have ha : raw15118step3 = raw15118step2 := by apply Matrix.ext; unfold raw15118step3 raw15118step2; decide +kernel
      have hl : raw15118step2Labels = labelEmbedding7 ∘ raw15118step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15118step2 raw15118step2Labels raw15118step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw15119 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15119step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15119step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15119step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15119step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15119step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15119step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15119 raw15119Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw15119 raw15119Labels = mixedMoment B raw15119step0 raw15119step0Labels := by
      have ha : raw15119step0 = (fun i j => raw15119 (permutation188 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15119step0 raw15119; decide +kernel
      have hl : raw15119step0Labels = raw15119Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15119 raw15119Labels permutation188 permutation4
    mixedMoment B raw15119step0 raw15119step0Labels = mixedMoment B raw15119step1 raw15119step1Labels := by
      have ha : raw15119step1 = -raw15119step0 := by apply Matrix.ext; change ∀ i j, raw15119step1 i j = -(raw15119step0 i j); unfold raw15119step1 raw15119step0; decide +kernel
      have hl : raw15119step1Labels = raw15119step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15119step1 raw15119step1Labels = mixedMoment B raw15119step2 raw15119step2Labels := by
      have ha : raw15119step2 = raw15119step1 := by apply Matrix.ext; unfold raw15119step2 raw15119step1; decide +kernel
      have hl : raw15119step1Labels = labelEmbedding7 ∘ raw15119step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15119step1 raw15119step1Labels raw15119step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw15120 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15120step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15120step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15120step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15120step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15120step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15120step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15120 raw15120Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw15120 raw15120Labels = mixedMoment B raw15120step0 raw15120step0Labels := by
      have hz : ∀ j, raw15120 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15120step0 = (fun i j => raw15120 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15120step0 raw15120; decide +kernel
      have hl : raw15120step0Labels = raw15120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15120 raw15120Labels permutation434 hz
    mixedMoment B raw15120step0 raw15120step0Labels = mixedMoment B raw15120step1 raw15120step1Labels := by
      have hz : ∀ j, raw15120step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15120step1 = (fun i j => raw15120step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15120step1 raw15120step0; decide +kernel
      have hl : raw15120step1Labels = raw15120step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15120step0 raw15120step0Labels permutation80 hz
    mixedMoment B raw15120step1 raw15120step1Labels = mixedMoment B raw15120step2 raw15120step2Labels := by
      have ha : raw15120step2 = (fun i j => raw15120step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15120step2 raw15120step1; decide +kernel
      have hl : raw15120step2Labels = raw15120step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15120step1 raw15120step1Labels permutation8 permutation6
    mixedMoment B raw15120step2 raw15120step2Labels = mixedMoment B raw15120step3 raw15120step3Labels := by
      have ha : raw15120step3 = raw15120step2 := by apply Matrix.ext; unfold raw15120step3 raw15120step2; decide +kernel
      have hl : raw15120step2Labels = labelEmbedding9 ∘ raw15120step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15120step2 raw15120step2Labels raw15120step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw15121 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15121step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15121step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15121step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15121 raw15121Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw15121 raw15121Labels = mixedMoment B raw15121step0 raw15121step0Labels := by
      have hz : ∀ j, raw15121 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15121step0 = (fun i j => raw15121 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15121step0 raw15121; decide +kernel
      have hl : raw15121step0Labels = raw15121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15121 raw15121Labels permutation346 hz
    mixedMoment B raw15121step0 raw15121step0Labels = mixedMoment B raw15121step1 raw15121step1Labels := by
      have ha : raw15121step1 = (fun i j => raw15121step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15121step1 raw15121step0; decide +kernel
      have hl : raw15121step1Labels = raw15121step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15121step0 raw15121step0Labels permutation32 permutation6
    mixedMoment B raw15121step1 raw15121step1Labels = mixedMoment B raw15121step2 raw15121step2Labels := by
      have ha : raw15121step2 = raw15121step1 := by apply Matrix.ext; unfold raw15121step2 raw15121step1; decide +kernel
      have hl : raw15121step1Labels = labelEmbedding9 ∘ raw15121step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15121step1 raw15121step1Labels raw15121step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw15122 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15122step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15122step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15122step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15122step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15122step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15122 raw15122Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw15122 raw15122Labels = mixedMoment B raw15122step0 raw15122step0Labels := by
      have hz : ∀ j, raw15122 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15122step0 = (fun i j => raw15122 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15122step0 raw15122; decide +kernel
      have hl : raw15122step0Labels = raw15122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15122 raw15122Labels permutation346 hz
    mixedMoment B raw15122step0 raw15122step0Labels = mixedMoment B raw15122step1 raw15122step1Labels := by
      have ha : raw15122step1 = (fun i j => raw15122step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15122step1 raw15122step0; decide +kernel
      have hl : raw15122step1Labels = raw15122step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15122step0 raw15122step0Labels permutation151 permutation7
    mixedMoment B raw15122step1 raw15122step1Labels = mixedMoment B raw15122step2 raw15122step2Labels := by
      have ha : raw15122step2 = -raw15122step1 := by apply Matrix.ext; change ∀ i j, raw15122step2 i j = -(raw15122step1 i j); unfold raw15122step2 raw15122step1; decide +kernel
      have hl : raw15122step2Labels = raw15122step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15122step2 raw15122step2Labels = mixedMoment B raw15122step3 raw15122step3Labels := by
      have ha : raw15122step3 = raw15122step2 := by apply Matrix.ext; unfold raw15122step3 raw15122step2; decide +kernel
      have hl : raw15122step2Labels = labelEmbedding10 ∘ raw15122step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15122step2 raw15122step2Labels raw15122step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw15123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15123step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15123step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15123step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15123step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15123step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15123 raw15123Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw15123 raw15123Labels = mixedMoment B raw15123step0 raw15123step0Labels := by
      have ha : raw15123step0 = (fun i j => raw15123 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15123step0 raw15123; decide +kernel
      have hl : raw15123step0Labels = raw15123Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15123 raw15123Labels permutation164 permutation4
    mixedMoment B raw15123step0 raw15123step0Labels = mixedMoment B raw15123step1 raw15123step1Labels := by
      have ha : raw15123step1 = -raw15123step0 := by apply Matrix.ext; change ∀ i j, raw15123step1 i j = -(raw15123step0 i j); unfold raw15123step1 raw15123step0; decide +kernel
      have hl : raw15123step1Labels = raw15123step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15123step1 raw15123step1Labels = mixedMoment B raw15123step2 raw15123step2Labels := by
      have ha : raw15123step2 = raw15123step1 := by apply Matrix.ext; unfold raw15123step2 raw15123step1; decide +kernel
      have hl : raw15123step1Labels = labelEmbedding7 ∘ raw15123step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15123step1 raw15123step1Labels raw15123step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5256 node5256Labels := by rfl

def raw15124 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15124step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15124step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15124step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15124 raw15124Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw15124 raw15124Labels = mixedMoment B raw15124step0 raw15124step0Labels := by
      have ha : raw15124step0 = (fun i j => raw15124 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15124step0 raw15124; decide +kernel
      have hl : raw15124step0Labels = raw15124Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15124 raw15124Labels permutation152 permutation6
    mixedMoment B raw15124step0 raw15124step0Labels = mixedMoment B raw15124step1 raw15124step1Labels := by
      have ha : raw15124step1 = raw15124step0 := by apply Matrix.ext; unfold raw15124step1 raw15124step0; decide +kernel
      have hl : raw15124step0Labels = labelEmbedding9 ∘ raw15124step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15124step0 raw15124step0Labels raw15124step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw15125 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15125step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15125step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15125step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15125step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15125 raw15125Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw15125 raw15125Labels = mixedMoment B raw15125step0 raw15125step0Labels := by
      have hz : ∀ j, raw15125 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15125step0 = (fun i j => raw15125 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15125step0 raw15125; decide +kernel
      have hl : raw15125step0Labels = raw15125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15125 raw15125Labels permutation434 hz
    mixedMoment B raw15125step0 raw15125step0Labels = mixedMoment B raw15125step1 raw15125step1Labels := by
      have ha : raw15125step1 = (fun i j => raw15125step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15125step1 raw15125step0; decide +kernel
      have hl : raw15125step1Labels = raw15125step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15125step0 raw15125step0Labels permutation32 permutation6
    mixedMoment B raw15125step1 raw15125step1Labels = mixedMoment B raw15125step2 raw15125step2Labels := by
      have ha : raw15125step2 = raw15125step1 := by apply Matrix.ext; unfold raw15125step2 raw15125step1; decide +kernel
      have hl : raw15125step1Labels = labelEmbedding9 ∘ raw15125step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15125step1 raw15125step1Labels raw15125step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw15126 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15126step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15126step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15126step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15126step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15126 raw15126Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw15126 raw15126Labels = mixedMoment B raw15126step0 raw15126step0Labels := by
      have ha : raw15126step0 = (fun i j => raw15126 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15126step0 raw15126; decide +kernel
      have hl : raw15126step0Labels = raw15126Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15126 raw15126Labels permutation152 permutation6
    mixedMoment B raw15126step0 raw15126step0Labels = mixedMoment B raw15126step1 raw15126step1Labels := by
      have ha : raw15126step1 = raw15126step0 := by apply Matrix.ext; unfold raw15126step1 raw15126step0; decide +kernel
      have hl : raw15126step0Labels = labelEmbedding9 ∘ raw15126step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15126step0 raw15126step0Labels raw15126step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw15127 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15127step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15127step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15127step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15127step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15127step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15127step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15127 raw15127Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw15127 raw15127Labels = mixedMoment B raw15127step0 raw15127step0Labels := by
      have ha : raw15127step0 = (fun i j => raw15127 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15127step0 raw15127; decide +kernel
      have hl : raw15127step0Labels = raw15127Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15127 raw15127Labels permutation682 permutation7
    mixedMoment B raw15127step0 raw15127step0Labels = mixedMoment B raw15127step1 raw15127step1Labels := by
      have ha : raw15127step1 = -raw15127step0 := by apply Matrix.ext; change ∀ i j, raw15127step1 i j = -(raw15127step0 i j); unfold raw15127step1 raw15127step0; decide +kernel
      have hl : raw15127step1Labels = raw15127step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15127step1 raw15127step1Labels = mixedMoment B raw15127step2 raw15127step2Labels := by
      have ha : raw15127step2 = raw15127step1 := by apply Matrix.ext; unfold raw15127step2 raw15127step1; decide +kernel
      have hl : raw15127step1Labels = labelEmbedding10 ∘ raw15127step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15127step1 raw15127step1Labels raw15127step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw15128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15128step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15128step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15128step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15128step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15128 raw15128Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw15128 raw15128Labels = mixedMoment B raw15128step0 raw15128step0Labels := by
      have hz : ∀ j, raw15128 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15128step0 = (fun i j => raw15128 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15128step0 raw15128; decide +kernel
      have hl : raw15128step0Labels = raw15128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15128 raw15128Labels permutation346 hz
    mixedMoment B raw15128step0 raw15128step0Labels = mixedMoment B raw15128step1 raw15128step1Labels := by
      have ha : raw15128step1 = (fun i j => raw15128step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15128step1 raw15128step0; decide +kernel
      have hl : raw15128step1Labels = raw15128step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15128step0 raw15128step0Labels permutation35 permutation4
    mixedMoment B raw15128step1 raw15128step1Labels = mixedMoment B raw15128step2 raw15128step2Labels := by
      have ha : raw15128step2 = -raw15128step1 := by apply Matrix.ext; change ∀ i j, raw15128step2 i j = -(raw15128step1 i j); unfold raw15128step2 raw15128step1; decide +kernel
      have hl : raw15128step2Labels = raw15128step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15128step2 raw15128step2Labels = mixedMoment B raw15128step3 raw15128step3Labels := by
      have ha : raw15128step3 = raw15128step2 := by apply Matrix.ext; unfold raw15128step3 raw15128step2; decide +kernel
      have hl : raw15128step2Labels = labelEmbedding7 ∘ raw15128step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15128step2 raw15128step2Labels raw15128step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw15129 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15129step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15129step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15129step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15129step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15129step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15129step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15129 raw15129Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw15129 raw15129Labels = mixedMoment B raw15129step0 raw15129step0Labels := by
      have hz : ∀ j, raw15129 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15129step0 = (fun i j => raw15129 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15129step0 raw15129; decide +kernel
      have hl : raw15129step0Labels = raw15129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15129 raw15129Labels permutation346 hz
    mixedMoment B raw15129step0 raw15129step0Labels = mixedMoment B raw15129step1 raw15129step1Labels := by
      have ha : raw15129step1 = (fun i j => raw15129step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15129step1 raw15129step0; decide +kernel
      have hl : raw15129step1Labels = raw15129step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15129step0 raw15129step0Labels permutation35 permutation4
    mixedMoment B raw15129step1 raw15129step1Labels = mixedMoment B raw15129step2 raw15129step2Labels := by
      have ha : raw15129step2 = -raw15129step1 := by apply Matrix.ext; change ∀ i j, raw15129step2 i j = -(raw15129step1 i j); unfold raw15129step2 raw15129step1; decide +kernel
      have hl : raw15129step2Labels = raw15129step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15129step2 raw15129step2Labels = mixedMoment B raw15129step3 raw15129step3Labels := by
      have ha : raw15129step3 = raw15129step2 := by apply Matrix.ext; unfold raw15129step3 raw15129step2; decide +kernel
      have hl : raw15129step2Labels = labelEmbedding7 ∘ raw15129step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15129step2 raw15129step2Labels raw15129step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw15130 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15130step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15130step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15130step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15130step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15130step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15130step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15130 raw15130Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw15130 raw15130Labels = mixedMoment B raw15130step0 raw15130step0Labels := by
      have ha : raw15130step0 = (fun i j => raw15130 (permutation179 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15130step0 raw15130; decide +kernel
      have hl : raw15130step0Labels = raw15130Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15130 raw15130Labels permutation179 permutation4
    mixedMoment B raw15130step0 raw15130step0Labels = mixedMoment B raw15130step1 raw15130step1Labels := by
      have ha : raw15130step1 = -raw15130step0 := by apply Matrix.ext; change ∀ i j, raw15130step1 i j = -(raw15130step0 i j); unfold raw15130step1 raw15130step0; decide +kernel
      have hl : raw15130step1Labels = raw15130step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15130step1 raw15130step1Labels = mixedMoment B raw15130step2 raw15130step2Labels := by
      have ha : raw15130step2 = raw15130step1 := by apply Matrix.ext; unfold raw15130step2 raw15130step1; decide +kernel
      have hl : raw15130step1Labels = labelEmbedding7 ∘ raw15130step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15130step1 raw15130step1Labels raw15130step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw15131 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15131step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw15131step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15131step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15131step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15131step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15131step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15131 raw15131Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw15131 raw15131Labels = mixedMoment B raw15131step0 raw15131step0Labels := by
      have hz : ∀ j, raw15131 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15131step0 = (fun i j => raw15131 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15131step0 raw15131; decide +kernel
      have hl : raw15131step0Labels = raw15131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15131 raw15131Labels permutation346 hz
    mixedMoment B raw15131step0 raw15131step0Labels = mixedMoment B raw15131step1 raw15131step1Labels := by
      have ha : raw15131step1 = (fun i j => raw15131step0 (permutation87 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15131step1 raw15131step0; decide +kernel
      have hl : raw15131step1Labels = raw15131step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15131step0 raw15131step0Labels permutation87 permutation3
    mixedMoment B raw15131step1 raw15131step1Labels = mixedMoment B raw15131step2 raw15131step2Labels := by
      have ha : raw15131step2 = -raw15131step1 := by apply Matrix.ext; change ∀ i j, raw15131step2 i j = -(raw15131step1 i j); unfold raw15131step2 raw15131step1; decide +kernel
      have hl : raw15131step2Labels = raw15131step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15131step2 raw15131step2Labels = mixedMoment B raw15131step3 raw15131step3Labels := by
      have ha : raw15131step3 = raw15131step2 := by apply Matrix.ext; unfold raw15131step3 raw15131step2; decide +kernel
      have hl : raw15131step2Labels = labelEmbedding6 ∘ raw15131step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15131step2 raw15131step2Labels raw15131step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5436 node5436Labels := by rfl

def raw15132 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15132step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15132step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15132 raw15132Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw15132 raw15132Labels = mixedMoment B raw15132step0 raw15132step0Labels := by
      have hz : ∀ j, raw15132 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15132step0 = (fun i j => raw15132 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15132step0 raw15132; decide +kernel
      have hl : raw15132step0Labels = raw15132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15132 raw15132Labels permutation346 hz
    mixedMoment B raw15132step0 raw15132step0Labels = mixedMoment B raw15132step1 raw15132step1Labels := by
      have ha : raw15132step1 = (fun i j => raw15132step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15132step1 raw15132step0; decide +kernel
      have hl : raw15132step1Labels = raw15132step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15132step0 raw15132step0Labels permutation146 permutation2
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw15133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw15133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw15133step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15133step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15133step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15133step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15133step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15133step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15133 raw15133Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw15133 raw15133Labels = mixedMoment B raw15133step0 raw15133step0Labels := by
      have hz : ∀ j, raw15133 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15133step0 = (fun i j => raw15133 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15133step0 raw15133; decide +kernel
      have hl : raw15133step0Labels = raw15133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15133 raw15133Labels permutation346 hz
    mixedMoment B raw15133step0 raw15133step0Labels = mixedMoment B raw15133step1 raw15133step1Labels := by
      have ha : raw15133step1 = (fun i j => raw15133step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15133step1 raw15133step0; decide +kernel
      have hl : raw15133step1Labels = raw15133step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15133step0 raw15133step0Labels permutation32 permutation4
    mixedMoment B raw15133step1 raw15133step1Labels = mixedMoment B raw15133step2 raw15133step2Labels := by
      have ha : raw15133step2 = -raw15133step1 := by apply Matrix.ext; change ∀ i j, raw15133step2 i j = -(raw15133step1 i j); unfold raw15133step2 raw15133step1; decide +kernel
      have hl : raw15133step2Labels = raw15133step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15133step2 raw15133step2Labels = mixedMoment B raw15133step3 raw15133step3Labels := by
      have ha : raw15133step3 = raw15133step2 := by apply Matrix.ext; unfold raw15133step3 raw15133step2; decide +kernel
      have hl : raw15133step2Labels = labelEmbedding7 ∘ raw15133step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15133step2 raw15133step2Labels raw15133step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw15134 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw15134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw15134step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15134step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15134step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15134step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15134 raw15134Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw15134 raw15134Labels = mixedMoment B raw15134step0 raw15134step0Labels := by
      have hz : ∀ j, raw15134 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15134step0 = (fun i j => raw15134 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15134step0 raw15134; decide +kernel
      have hl : raw15134step0Labels = raw15134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15134 raw15134Labels permutation346 hz
    mixedMoment B raw15134step0 raw15134step0Labels = mixedMoment B raw15134step1 raw15134step1Labels := by
      have ha : raw15134step1 = (fun i j => raw15134step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15134step1 raw15134step0; decide +kernel
      have hl : raw15134step1Labels = raw15134step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15134step0 raw15134step0Labels permutation32 permutation6
    mixedMoment B raw15134step1 raw15134step1Labels = mixedMoment B raw15134step2 raw15134step2Labels := by
      have ha : raw15134step2 = raw15134step1 := by apply Matrix.ext; unfold raw15134step2 raw15134step1; decide +kernel
      have hl : raw15134step1Labels = labelEmbedding9 ∘ raw15134step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15134step1 raw15134step1Labels raw15134step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw15135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw15135step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15135step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw15135step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15135step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw15135step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15135 raw15135Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw15135 raw15135Labels = mixedMoment B raw15135step0 raw15135step0Labels := by
      have hz : ∀ j, raw15135 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15135step0 = (fun i j => raw15135 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15135step0 raw15135; decide +kernel
      have hl : raw15135step0Labels = raw15135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15135 raw15135Labels permutation346 hz
    mixedMoment B raw15135step0 raw15135step0Labels = mixedMoment B raw15135step1 raw15135step1Labels := by
      have ha : raw15135step1 = (fun i j => raw15135step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15135step1 raw15135step0; decide +kernel
      have hl : raw15135step1Labels = raw15135step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15135step0 raw15135step0Labels permutation34 permutation4
    mixedMoment B raw15135step1 raw15135step1Labels = mixedMoment B raw15135step2 raw15135step2Labels := by
      have ha : raw15135step2 = -raw15135step1 := by apply Matrix.ext; change ∀ i j, raw15135step2 i j = -(raw15135step1 i j); unfold raw15135step2 raw15135step1; decide +kernel
      have hl : raw15135step2Labels = raw15135step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15135step2 raw15135step2Labels = mixedMoment B raw15135step3 raw15135step3Labels := by
      have ha : raw15135step3 = raw15135step2 := by apply Matrix.ext; unfold raw15135step3 raw15135step2; decide +kernel
      have hl : raw15135step2Labels = labelEmbedding7 ∘ raw15135step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15135step2 raw15135step2Labels raw15135step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw15136 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15136step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15136step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw15136step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15136step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw15136step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15136step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw15136step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15136 raw15136Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw15136 raw15136Labels = mixedMoment B raw15136step0 raw15136step0Labels := by
      have hz : ∀ j, raw15136 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15136step0 = (fun i j => raw15136 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15136step0 raw15136; decide +kernel
      have hl : raw15136step0Labels = raw15136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15136 raw15136Labels permutation346 hz
    mixedMoment B raw15136step0 raw15136step0Labels = mixedMoment B raw15136step1 raw15136step1Labels := by
      have ha : raw15136step1 = (fun i j => raw15136step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15136step1 raw15136step0; decide +kernel
      have hl : raw15136step1Labels = raw15136step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15136step0 raw15136step0Labels permutation34 permutation4
    mixedMoment B raw15136step1 raw15136step1Labels = mixedMoment B raw15136step2 raw15136step2Labels := by
      have ha : raw15136step2 = -raw15136step1 := by apply Matrix.ext; change ∀ i j, raw15136step2 i j = -(raw15136step1 i j); unfold raw15136step2 raw15136step1; decide +kernel
      have hl : raw15136step2Labels = raw15136step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15136step2 raw15136step2Labels = mixedMoment B raw15136step3 raw15136step3Labels := by
      have ha : raw15136step3 = raw15136step2 := by apply Matrix.ext; unfold raw15136step3 raw15136step2; decide +kernel
      have hl : raw15136step2Labels = labelEmbedding7 ∘ raw15136step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15136step2 raw15136step2Labels raw15136step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5409 node5409Labels := by rfl

def raw15137 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw15137step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15137step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw15137step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15137 raw15137Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw15137 raw15137Labels = mixedMoment B raw15137step0 raw15137step0Labels := by
      have ha : raw15137step0 = (fun i j => raw15137 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15137step0 raw15137; decide +kernel
      have hl : raw15137step0Labels = raw15137Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15137 raw15137Labels permutation662 permutation4
    mixedMoment B raw15137step0 raw15137step0Labels = mixedMoment B raw15137step1 raw15137step1Labels := by
      have ha : raw15137step1 = raw15137step0 := by apply Matrix.ext; unfold raw15137step1 raw15137step0; decide +kernel
      have hl : raw15137step0Labels = labelEmbedding7 ∘ raw15137step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15137step0 raw15137step0Labels raw15137step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5423 node5423Labels := by rfl

def raw15138 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15138step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 0, 1], ![0, -2, 2]]
def raw15138step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15138step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15138step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15138step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15138step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15138 raw15138Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw15138 raw15138Labels = mixedMoment B raw15138step0 raw15138step0Labels := by
      have hz : ∀ j, raw15138 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15138step0 = (fun i j => raw15138 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15138step0 raw15138; decide +kernel
      have hl : raw15138step0Labels = raw15138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15138 raw15138Labels permutation434 hz
    mixedMoment B raw15138step0 raw15138step0Labels = mixedMoment B raw15138step1 raw15138step1Labels := by
      have hz : ∀ j, raw15138step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15138step1 = (fun i j => raw15138step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15138step1 raw15138step0; decide +kernel
      have hl : raw15138step1Labels = raw15138step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15138step0 raw15138step0Labels permutation80 hz
    mixedMoment B raw15138step1 raw15138step1Labels = mixedMoment B raw15138step2 raw15138step2Labels := by
      have ha : raw15138step2 = (fun i j => raw15138step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15138step2 raw15138step1; decide +kernel
      have hl : raw15138step2Labels = raw15138step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15138step1 raw15138step1Labels permutation8 permutation6
    mixedMoment B raw15138step2 raw15138step2Labels = mixedMoment B raw15138step3 raw15138step3Labels := by
      have ha : raw15138step3 = raw15138step2 := by apply Matrix.ext; unfold raw15138step3 raw15138step2; decide +kernel
      have hl : raw15138step2Labels = labelEmbedding9 ∘ raw15138step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15138step2 raw15138step2Labels raw15138step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5441 node5441Labels := by rfl

def raw15139 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15139step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15139step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15139step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15139 raw15139Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw15139 raw15139Labels = mixedMoment B raw15139step0 raw15139step0Labels := by
      have hz : ∀ j, raw15139 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15139step0 = (fun i j => raw15139 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15139step0 raw15139; decide +kernel
      have hl : raw15139step0Labels = raw15139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15139 raw15139Labels permutation346 hz
    mixedMoment B raw15139step0 raw15139step0Labels = mixedMoment B raw15139step1 raw15139step1Labels := by
      have ha : raw15139step1 = (fun i j => raw15139step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15139step1 raw15139step0; decide +kernel
      have hl : raw15139step1Labels = raw15139step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15139step0 raw15139step0Labels permutation143 permutation4
    mixedMoment B raw15139step1 raw15139step1Labels = mixedMoment B raw15139step2 raw15139step2Labels := by
      have ha : raw15139step2 = raw15139step1 := by apply Matrix.ext; unfold raw15139step2 raw15139step1; decide +kernel
      have hl : raw15139step1Labels = labelEmbedding7 ∘ raw15139step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15139step1 raw15139step1Labels raw15139step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw15140 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15140Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15140step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15140step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15140step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15140step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15140step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15140 raw15140Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw15140 raw15140Labels = mixedMoment B raw15140step0 raw15140step0Labels := by
      have hz : ∀ j, raw15140 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15140step0 = (fun i j => raw15140 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15140step0 raw15140; decide +kernel
      have hl : raw15140step0Labels = raw15140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15140 raw15140Labels permutation346 hz
    mixedMoment B raw15140step0 raw15140step0Labels = mixedMoment B raw15140step1 raw15140step1Labels := by
      have ha : raw15140step1 = (fun i j => raw15140step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15140step1 raw15140step0; decide +kernel
      have hl : raw15140step1Labels = raw15140step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15140step0 raw15140step0Labels permutation151 permutation7
    mixedMoment B raw15140step1 raw15140step1Labels = mixedMoment B raw15140step2 raw15140step2Labels := by
      have ha : raw15140step2 = -raw15140step1 := by apply Matrix.ext; change ∀ i j, raw15140step2 i j = -(raw15140step1 i j); unfold raw15140step2 raw15140step1; decide +kernel
      have hl : raw15140step2Labels = raw15140step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15140step2 raw15140step2Labels = mixedMoment B raw15140step3 raw15140step3Labels := by
      have ha : raw15140step3 = raw15140step2 := by apply Matrix.ext; unfold raw15140step3 raw15140step2; decide +kernel
      have hl : raw15140step2Labels = labelEmbedding1 ∘ raw15140step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15140step2 raw15140step2Labels raw15140step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw15141 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15141Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15141step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15141step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15141 raw15141Labels = mixedMoment B node3971 node3971Labels := by
  calc
    mixedMoment B raw15141 raw15141Labels = mixedMoment B raw15141step0 raw15141step0Labels := by
      have ha : raw15141step0 = (fun i j => raw15141 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15141step0 raw15141; decide +kernel
      have hl : raw15141step0Labels = raw15141Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15141 raw15141Labels permutation158 permutation7
    mixedMoment B raw15141step0 raw15141step0Labels = mixedMoment B raw15141step1 raw15141step1Labels := by
      have ha : raw15141step1 = raw15141step0 := by apply Matrix.ext; unfold raw15141step1 raw15141step0; decide +kernel
      have hl : raw15141step0Labels = labelEmbedding1 ∘ raw15141step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15141step0 raw15141step0Labels raw15141step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3971 node3971Labels := by rfl

def raw15142 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15142Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15142step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15142step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15142step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15142step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15142step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15142step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15142step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15142 raw15142Labels = mixedMoment B node3986 node3986Labels := by
  calc
    mixedMoment B raw15142 raw15142Labels = mixedMoment B raw15142step0 raw15142step0Labels := by
      have hz : ∀ j, raw15142 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15142step0 = (fun i j => raw15142 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15142step0 raw15142; decide +kernel
      have hl : raw15142step0Labels = raw15142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15142 raw15142Labels permutation434 hz
    mixedMoment B raw15142step0 raw15142step0Labels = mixedMoment B raw15142step1 raw15142step1Labels := by
      have hz : ∀ j, raw15142step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15142step1 = (fun i j => raw15142step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15142step1 raw15142step0; decide +kernel
      have hl : raw15142step1Labels = raw15142step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15142step0 raw15142step0Labels permutation80 hz
    mixedMoment B raw15142step1 raw15142step1Labels = mixedMoment B raw15142step2 raw15142step2Labels := by
      have ha : raw15142step2 = (fun i j => raw15142step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15142step2 raw15142step1; decide +kernel
      have hl : raw15142step2Labels = raw15142step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15142step1 raw15142step1Labels permutation8 permutation7
    mixedMoment B raw15142step2 raw15142step2Labels = mixedMoment B raw15142step3 raw15142step3Labels := by
      have ha : raw15142step3 = raw15142step2 := by apply Matrix.ext; unfold raw15142step3 raw15142step2; decide +kernel
      have hl : raw15142step2Labels = labelEmbedding1 ∘ raw15142step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15142step2 raw15142step2Labels raw15142step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3986 node3986Labels := by rfl

def raw15143 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15143Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15143step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15143step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15143step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15143step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15143step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15143 raw15143Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw15143 raw15143Labels = mixedMoment B raw15143step0 raw15143step0Labels := by
      have hz : ∀ j, raw15143 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15143step0 = (fun i j => raw15143 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15143step0 raw15143; decide +kernel
      have hl : raw15143step0Labels = raw15143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15143 raw15143Labels permutation346 hz
    mixedMoment B raw15143step0 raw15143step0Labels = mixedMoment B raw15143step1 raw15143step1Labels := by
      have ha : raw15143step1 = (fun i j => raw15143step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15143step1 raw15143step0; decide +kernel
      have hl : raw15143step1Labels = raw15143step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15143step0 raw15143step0Labels permutation151 permutation7
    mixedMoment B raw15143step1 raw15143step1Labels = mixedMoment B raw15143step2 raw15143step2Labels := by
      have ha : raw15143step2 = -raw15143step1 := by apply Matrix.ext; change ∀ i j, raw15143step2 i j = -(raw15143step1 i j); unfold raw15143step2 raw15143step1; decide +kernel
      have hl : raw15143step2Labels = raw15143step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15143step2 raw15143step2Labels = mixedMoment B raw15143step3 raw15143step3Labels := by
      have ha : raw15143step3 = raw15143step2 := by apply Matrix.ext; unfold raw15143step3 raw15143step2; decide +kernel
      have hl : raw15143step2Labels = labelEmbedding1 ∘ raw15143step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15143step2 raw15143step2Labels raw15143step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw15144 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15144Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15144step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15144step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15144step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15144step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15144step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15144step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15144 raw15144Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw15144 raw15144Labels = mixedMoment B raw15144step0 raw15144step0Labels := by
      have hz : ∀ j, raw15144 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15144step0 = (fun i j => raw15144 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15144step0 raw15144; decide +kernel
      have hl : raw15144step0Labels = raw15144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15144 raw15144Labels permutation346 hz
    mixedMoment B raw15144step0 raw15144step0Labels = mixedMoment B raw15144step1 raw15144step1Labels := by
      have ha : raw15144step1 = (fun i j => raw15144step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15144step1 raw15144step0; decide +kernel
      have hl : raw15144step1Labels = raw15144step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15144step0 raw15144step0Labels permutation151 permutation7
    mixedMoment B raw15144step1 raw15144step1Labels = mixedMoment B raw15144step2 raw15144step2Labels := by
      have ha : raw15144step2 = -raw15144step1 := by apply Matrix.ext; change ∀ i j, raw15144step2 i j = -(raw15144step1 i j); unfold raw15144step2 raw15144step1; decide +kernel
      have hl : raw15144step2Labels = raw15144step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15144step2 raw15144step2Labels = mixedMoment B raw15144step3 raw15144step3Labels := by
      have ha : raw15144step3 = raw15144step2 := by apply Matrix.ext; unfold raw15144step3 raw15144step2; decide +kernel
      have hl : raw15144step2Labels = labelEmbedding1 ∘ raw15144step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15144step2 raw15144step2Labels raw15144step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3808 node3808Labels := by rfl

def raw15145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15145Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15145step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15145step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15145step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15145step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15145step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15145step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15145 raw15145Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw15145 raw15145Labels = mixedMoment B raw15145step0 raw15145step0Labels := by
      have hz : ∀ j, raw15145 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15145step0 = (fun i j => raw15145 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15145step0 raw15145; decide +kernel
      have hl : raw15145step0Labels = raw15145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15145 raw15145Labels permutation346 hz
    mixedMoment B raw15145step0 raw15145step0Labels = mixedMoment B raw15145step1 raw15145step1Labels := by
      have ha : raw15145step1 = (fun i j => raw15145step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15145step1 raw15145step0; decide +kernel
      have hl : raw15145step1Labels = raw15145step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15145step0 raw15145step0Labels permutation49 permutation5
    mixedMoment B raw15145step1 raw15145step1Labels = mixedMoment B raw15145step2 raw15145step2Labels := by
      have ha : raw15145step2 = -raw15145step1 := by apply Matrix.ext; change ∀ i j, raw15145step2 i j = -(raw15145step1 i j); unfold raw15145step2 raw15145step1; decide +kernel
      have hl : raw15145step2Labels = raw15145step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15145step2 raw15145step2Labels = mixedMoment B raw15145step3 raw15145step3Labels := by
      have ha : raw15145step3 = raw15145step2 := by apply Matrix.ext; unfold raw15145step3 raw15145step2; decide +kernel
      have hl : raw15145step2Labels = labelEmbedding1 ∘ raw15145step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15145step2 raw15145step2Labels raw15145step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw15146 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15146Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15146step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15146step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15146step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15146step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15146step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15146 raw15146Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw15146 raw15146Labels = mixedMoment B raw15146step0 raw15146step0Labels := by
      have ha : raw15146step0 = (fun i j => raw15146 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15146step0 raw15146; decide +kernel
      have hl : raw15146step0Labels = raw15146Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15146 raw15146Labels permutation682 permutation7
    mixedMoment B raw15146step0 raw15146step0Labels = mixedMoment B raw15146step1 raw15146step1Labels := by
      have ha : raw15146step1 = -raw15146step0 := by apply Matrix.ext; change ∀ i j, raw15146step1 i j = -(raw15146step0 i j); unfold raw15146step1 raw15146step0; decide +kernel
      have hl : raw15146step1Labels = raw15146step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15146step1 raw15146step1Labels = mixedMoment B raw15146step2 raw15146step2Labels := by
      have ha : raw15146step2 = raw15146step1 := by apply Matrix.ext; unfold raw15146step2 raw15146step1; decide +kernel
      have hl : raw15146step1Labels = labelEmbedding1 ∘ raw15146step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15146step1 raw15146step1Labels raw15146step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw15147 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15147Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15147step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15147step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15147step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15147step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15147step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15147step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15147step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15147step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15147step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15147 raw15147Labels = mixedMoment B node3987 node3987Labels := by
  calc
    mixedMoment B raw15147 raw15147Labels = mixedMoment B raw15147step0 raw15147step0Labels := by
      have hz : ∀ j, raw15147 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15147step0 = (fun i j => raw15147 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15147step0 raw15147; decide +kernel
      have hl : raw15147step0Labels = raw15147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15147 raw15147Labels permutation434 hz
    mixedMoment B raw15147step0 raw15147step0Labels = mixedMoment B raw15147step1 raw15147step1Labels := by
      have hz : ∀ j, raw15147step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15147step1 = (fun i j => raw15147step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15147step1 raw15147step0; decide +kernel
      have hl : raw15147step1Labels = raw15147step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15147step0 raw15147step0Labels permutation80 hz
    mixedMoment B raw15147step1 raw15147step1Labels = mixedMoment B raw15147step2 raw15147step2Labels := by
      have ha : raw15147step2 = (fun i j => raw15147step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15147step2 raw15147step1; decide +kernel
      have hl : raw15147step2Labels = raw15147step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15147step1 raw15147step1Labels permutation31 permutation7
    mixedMoment B raw15147step2 raw15147step2Labels = mixedMoment B raw15147step3 raw15147step3Labels := by
      have ha : raw15147step3 = -raw15147step2 := by apply Matrix.ext; change ∀ i j, raw15147step3 i j = -(raw15147step2 i j); unfold raw15147step3 raw15147step2; decide +kernel
      have hl : raw15147step3Labels = raw15147step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15147step3 raw15147step3Labels = mixedMoment B raw15147step4 raw15147step4Labels := by
      have ha : raw15147step4 = raw15147step3 := by apply Matrix.ext; unfold raw15147step4 raw15147step3; decide +kernel
      have hl : raw15147step3Labels = labelEmbedding1 ∘ raw15147step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15147step3 raw15147step3Labels raw15147step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3987 node3987Labels := by rfl

def raw15148 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15148Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15148step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15148step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15148step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15148step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15148step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15148 raw15148Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw15148 raw15148Labels = mixedMoment B raw15148step0 raw15148step0Labels := by
      have hz : ∀ j, raw15148 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15148step0 = (fun i j => raw15148 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15148step0 raw15148; decide +kernel
      have hl : raw15148step0Labels = raw15148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15148 raw15148Labels permutation346 hz
    mixedMoment B raw15148step0 raw15148step0Labels = mixedMoment B raw15148step1 raw15148step1Labels := by
      have ha : raw15148step1 = (fun i j => raw15148step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15148step1 raw15148step0; decide +kernel
      have hl : raw15148step1Labels = raw15148step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15148step0 raw15148step0Labels permutation151 permutation7
    mixedMoment B raw15148step1 raw15148step1Labels = mixedMoment B raw15148step2 raw15148step2Labels := by
      have ha : raw15148step2 = -raw15148step1 := by apply Matrix.ext; change ∀ i j, raw15148step2 i j = -(raw15148step1 i j); unfold raw15148step2 raw15148step1; decide +kernel
      have hl : raw15148step2Labels = raw15148step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15148step2 raw15148step2Labels = mixedMoment B raw15148step3 raw15148step3Labels := by
      have ha : raw15148step3 = raw15148step2 := by apply Matrix.ext; unfold raw15148step3 raw15148step2; decide +kernel
      have hl : raw15148step2Labels = labelEmbedding1 ∘ raw15148step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15148step2 raw15148step2Labels raw15148step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw15149 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15149Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15149step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15149step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15149step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15149step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15149step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15149step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15149 raw15149Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw15149 raw15149Labels = mixedMoment B raw15149step0 raw15149step0Labels := by
      have hz : ∀ j, raw15149 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15149step0 = (fun i j => raw15149 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15149step0 raw15149; decide +kernel
      have hl : raw15149step0Labels = raw15149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15149 raw15149Labels permutation346 hz
    mixedMoment B raw15149step0 raw15149step0Labels = mixedMoment B raw15149step1 raw15149step1Labels := by
      have ha : raw15149step1 = (fun i j => raw15149step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15149step1 raw15149step0; decide +kernel
      have hl : raw15149step1Labels = raw15149step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15149step0 raw15149step0Labels permutation151 permutation7
    mixedMoment B raw15149step1 raw15149step1Labels = mixedMoment B raw15149step2 raw15149step2Labels := by
      have ha : raw15149step2 = -raw15149step1 := by apply Matrix.ext; change ∀ i j, raw15149step2 i j = -(raw15149step1 i j); unfold raw15149step2 raw15149step1; decide +kernel
      have hl : raw15149step2Labels = raw15149step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15149step2 raw15149step2Labels = mixedMoment B raw15149step3 raw15149step3Labels := by
      have ha : raw15149step3 = raw15149step2 := by apply Matrix.ext; unfold raw15149step3 raw15149step2; decide +kernel
      have hl : raw15149step2Labels = labelEmbedding1 ∘ raw15149step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15149step2 raw15149step2Labels raw15149step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw15150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15150Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15150step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15150step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15150step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15150step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15150step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15150step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15150 raw15150Labels = mixedMoment B node3085 node3085Labels := by
  calc
    mixedMoment B raw15150 raw15150Labels = mixedMoment B raw15150step0 raw15150step0Labels := by
      have ha : raw15150step0 = (fun i j => raw15150 (permutation228 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15150step0 raw15150; decide +kernel
      have hl : raw15150step0Labels = raw15150Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15150 raw15150Labels permutation228 permutation5
    mixedMoment B raw15150step0 raw15150step0Labels = mixedMoment B raw15150step1 raw15150step1Labels := by
      have ha : raw15150step1 = -raw15150step0 := by apply Matrix.ext; change ∀ i j, raw15150step1 i j = -(raw15150step0 i j); unfold raw15150step1 raw15150step0; decide +kernel
      have hl : raw15150step1Labels = raw15150step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15150step1 raw15150step1Labels = mixedMoment B raw15150step2 raw15150step2Labels := by
      have ha : raw15150step2 = raw15150step1 := by apply Matrix.ext; unfold raw15150step2 raw15150step1; decide +kernel
      have hl : raw15150step1Labels = labelEmbedding1 ∘ raw15150step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15150step1 raw15150step1Labels raw15150step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3085 node3085Labels := by rfl

def raw15151 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15151Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw15151step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15151step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15151step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15151step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15151step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15151 raw15151Labels = mixedMoment B node3977 node3977Labels := by
  calc
    mixedMoment B raw15151 raw15151Labels = mixedMoment B raw15151step0 raw15151step0Labels := by
      have ha : raw15151step0 = (fun i j => raw15151 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15151step0 raw15151; decide +kernel
      have hl : raw15151step0Labels = raw15151Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15151 raw15151Labels permutation682 permutation7
    mixedMoment B raw15151step0 raw15151step0Labels = mixedMoment B raw15151step1 raw15151step1Labels := by
      have ha : raw15151step1 = -raw15151step0 := by apply Matrix.ext; change ∀ i j, raw15151step1 i j = -(raw15151step0 i j); unfold raw15151step1 raw15151step0; decide +kernel
      have hl : raw15151step1Labels = raw15151step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15151step1 raw15151step1Labels = mixedMoment B raw15151step2 raw15151step2Labels := by
      have ha : raw15151step2 = raw15151step1 := by apply Matrix.ext; unfold raw15151step2 raw15151step1; decide +kernel
      have hl : raw15151step1Labels = labelEmbedding1 ∘ raw15151step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15151step1 raw15151step1Labels raw15151step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3977 node3977Labels := by rfl

def raw15152 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15152Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15152step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15152step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15152step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15152step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15152step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15152 raw15152Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw15152 raw15152Labels = mixedMoment B raw15152step0 raw15152step0Labels := by
      have hz : ∀ j, raw15152 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15152step0 = (fun i j => raw15152 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15152step0 raw15152; decide +kernel
      have hl : raw15152step0Labels = raw15152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15152 raw15152Labels permutation434 hz
    mixedMoment B raw15152step0 raw15152step0Labels = mixedMoment B raw15152step1 raw15152step1Labels := by
      have ha : raw15152step1 = (fun i j => raw15152step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15152step1 raw15152step0; decide +kernel
      have hl : raw15152step1Labels = raw15152step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15152step0 raw15152step0Labels permutation151 permutation7
    mixedMoment B raw15152step1 raw15152step1Labels = mixedMoment B raw15152step2 raw15152step2Labels := by
      have ha : raw15152step2 = -raw15152step1 := by apply Matrix.ext; change ∀ i j, raw15152step2 i j = -(raw15152step1 i j); unfold raw15152step2 raw15152step1; decide +kernel
      have hl : raw15152step2Labels = raw15152step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15152step2 raw15152step2Labels = mixedMoment B raw15152step3 raw15152step3Labels := by
      have ha : raw15152step3 = raw15152step2 := by apply Matrix.ext; unfold raw15152step3 raw15152step2; decide +kernel
      have hl : raw15152step2Labels = labelEmbedding1 ∘ raw15152step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15152step2 raw15152step2Labels raw15152step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw15153 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15153Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15153step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15153step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15153step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15153step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15153step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15153step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15153 raw15153Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw15153 raw15153Labels = mixedMoment B raw15153step0 raw15153step0Labels := by
      have ha : raw15153step0 = (fun i j => raw15153 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15153step0 raw15153; decide +kernel
      have hl : raw15153step0Labels = raw15153Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15153 raw15153Labels permutation682 permutation7
    mixedMoment B raw15153step0 raw15153step0Labels = mixedMoment B raw15153step1 raw15153step1Labels := by
      have ha : raw15153step1 = -raw15153step0 := by apply Matrix.ext; change ∀ i j, raw15153step1 i j = -(raw15153step0 i j); unfold raw15153step1 raw15153step0; decide +kernel
      have hl : raw15153step1Labels = raw15153step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15153step1 raw15153step1Labels = mixedMoment B raw15153step2 raw15153step2Labels := by
      have ha : raw15153step2 = raw15153step1 := by apply Matrix.ext; unfold raw15153step2 raw15153step1; decide +kernel
      have hl : raw15153step1Labels = labelEmbedding1 ∘ raw15153step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15153step1 raw15153step1Labels raw15153step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3954 node3954Labels := by rfl

def raw15154 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15154Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15154step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15154step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15154step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15154step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15154step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15154 raw15154Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw15154 raw15154Labels = mixedMoment B raw15154step0 raw15154step0Labels := by
      have ha : raw15154step0 = (fun i j => raw15154 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15154step0 raw15154; decide +kernel
      have hl : raw15154step0Labels = raw15154Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15154 raw15154Labels permutation682 permutation7
    mixedMoment B raw15154step0 raw15154step0Labels = mixedMoment B raw15154step1 raw15154step1Labels := by
      have ha : raw15154step1 = -raw15154step0 := by apply Matrix.ext; change ∀ i j, raw15154step1 i j = -(raw15154step0 i j); unfold raw15154step1 raw15154step0; decide +kernel
      have hl : raw15154step1Labels = raw15154step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15154step1 raw15154step1Labels = mixedMoment B raw15154step2 raw15154step2Labels := by
      have ha : raw15154step2 = raw15154step1 := by apply Matrix.ext; unfold raw15154step2 raw15154step1; decide +kernel
      have hl : raw15154step1Labels = labelEmbedding1 ∘ raw15154step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15154step1 raw15154step1Labels raw15154step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3801 node3801Labels := by rfl

def raw15155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15155Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15155step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw15155step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15155step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15155step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15155step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15155step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15155 raw15155Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw15155 raw15155Labels = mixedMoment B raw15155step0 raw15155step0Labels := by
      have hz : ∀ j, raw15155 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15155step0 = (fun i j => raw15155 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15155step0 raw15155; decide +kernel
      have hl : raw15155step0Labels = raw15155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15155 raw15155Labels permutation346 hz
    mixedMoment B raw15155step0 raw15155step0Labels = mixedMoment B raw15155step1 raw15155step1Labels := by
      have ha : raw15155step1 = (fun i j => raw15155step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15155step1 raw15155step0; decide +kernel
      have hl : raw15155step1Labels = raw15155step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15155step0 raw15155step0Labels permutation45 permutation5
    mixedMoment B raw15155step1 raw15155step1Labels = mixedMoment B raw15155step2 raw15155step2Labels := by
      have ha : raw15155step2 = -raw15155step1 := by apply Matrix.ext; change ∀ i j, raw15155step2 i j = -(raw15155step1 i j); unfold raw15155step2 raw15155step1; decide +kernel
      have hl : raw15155step2Labels = raw15155step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15155step2 raw15155step2Labels = mixedMoment B raw15155step3 raw15155step3Labels := by
      have ha : raw15155step3 = raw15155step2 := by apply Matrix.ext; unfold raw15155step3 raw15155step2; decide +kernel
      have hl : raw15155step2Labels = labelEmbedding1 ∘ raw15155step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15155step2 raw15155step2Labels raw15155step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw15156 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15156Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15156step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15156step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15156step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15156step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15156 raw15156Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw15156 raw15156Labels = mixedMoment B raw15156step0 raw15156step0Labels := by
      have hz : ∀ j, raw15156 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15156step0 = (fun i j => raw15156 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15156step0 raw15156; decide +kernel
      have hl : raw15156step0Labels = raw15156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15156 raw15156Labels permutation346 hz
    mixedMoment B raw15156step0 raw15156step0Labels = mixedMoment B raw15156step1 raw15156step1Labels := by
      have ha : raw15156step1 = (fun i j => raw15156step0 (permutation103 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15156step1 raw15156step0; decide +kernel
      have hl : raw15156step1Labels = raw15156step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15156step0 raw15156step0Labels permutation103 permutation5
    mixedMoment B raw15156step1 raw15156step1Labels = mixedMoment B raw15156step2 raw15156step2Labels := by
      have ha : raw15156step2 = raw15156step1 := by apply Matrix.ext; unfold raw15156step2 raw15156step1; decide +kernel
      have hl : raw15156step1Labels = labelEmbedding1 ∘ raw15156step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15156step1 raw15156step1Labels raw15156step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3883 node3883Labels := by rfl

def raw15157 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15157Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15157step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15157step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15157step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15157 raw15157Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw15157 raw15157Labels = mixedMoment B raw15157step0 raw15157step0Labels := by
      have ha : raw15157step0 = (fun i j => raw15157 (permutation511 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15157step0 raw15157; decide +kernel
      have hl : raw15157step0Labels = raw15157Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15157 raw15157Labels permutation511 permutation5
    mixedMoment B raw15157step0 raw15157step0Labels = mixedMoment B raw15157step1 raw15157step1Labels := by
      have ha : raw15157step1 = raw15157step0 := by apply Matrix.ext; unfold raw15157step1 raw15157step0; decide +kernel
      have hl : raw15157step0Labels = labelEmbedding1 ∘ raw15157step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15157step0 raw15157step0Labels raw15157step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw15158 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15158Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15158step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15158step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15158step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15158step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15158 raw15158Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw15158 raw15158Labels = mixedMoment B raw15158step0 raw15158step0Labels := by
      have hz : ∀ j, raw15158 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15158step0 = (fun i j => raw15158 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15158step0 raw15158; decide +kernel
      have hl : raw15158step0Labels = raw15158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15158 raw15158Labels permutation346 hz
    mixedMoment B raw15158step0 raw15158step0Labels = mixedMoment B raw15158step1 raw15158step1Labels := by
      have ha : raw15158step1 = (fun i j => raw15158step0 (permutation101 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15158step1 raw15158step0; decide +kernel
      have hl : raw15158step1Labels = raw15158step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15158step0 raw15158step0Labels permutation101 permutation5
    mixedMoment B raw15158step1 raw15158step1Labels = mixedMoment B raw15158step2 raw15158step2Labels := by
      have ha : raw15158step2 = raw15158step1 := by apply Matrix.ext; unfold raw15158step2 raw15158step1; decide +kernel
      have hl : raw15158step1Labels = labelEmbedding1 ∘ raw15158step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15158step1 raw15158step1Labels raw15158step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw15159 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15159Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15159step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15159step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15159step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15159step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15159step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15159step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15159 raw15159Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw15159 raw15159Labels = mixedMoment B raw15159step0 raw15159step0Labels := by
      have hz : ∀ j, raw15159 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15159step0 = (fun i j => raw15159 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15159step0 raw15159; decide +kernel
      have hl : raw15159step0Labels = raw15159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15159 raw15159Labels permutation346 hz
    mixedMoment B raw15159step0 raw15159step0Labels = mixedMoment B raw15159step1 raw15159step1Labels := by
      have ha : raw15159step1 = (fun i j => raw15159step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15159step1 raw15159step0; decide +kernel
      have hl : raw15159step1Labels = raw15159step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15159step0 raw15159step0Labels permutation151 permutation7
    mixedMoment B raw15159step1 raw15159step1Labels = mixedMoment B raw15159step2 raw15159step2Labels := by
      have ha : raw15159step2 = -raw15159step1 := by apply Matrix.ext; change ∀ i j, raw15159step2 i j = -(raw15159step1 i j); unfold raw15159step2 raw15159step1; decide +kernel
      have hl : raw15159step2Labels = raw15159step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15159step2 raw15159step2Labels = mixedMoment B raw15159step3 raw15159step3Labels := by
      have ha : raw15159step3 = raw15159step2 := by apply Matrix.ext; unfold raw15159step3 raw15159step2; decide +kernel
      have hl : raw15159step2Labels = labelEmbedding1 ∘ raw15159step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15159step2 raw15159step2Labels raw15159step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw15160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw15160Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw15160step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw15160step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15160step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw15160step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15160step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw15160step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15160 raw15160Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw15160 raw15160Labels = mixedMoment B raw15160step0 raw15160step0Labels := by
      have hz : ∀ j, raw15160 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15160step0 = (fun i j => raw15160 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15160step0 raw15160; decide +kernel
      have hl : raw15160step0Labels = raw15160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15160 raw15160Labels permutation346 hz
    mixedMoment B raw15160step0 raw15160step0Labels = mixedMoment B raw15160step1 raw15160step1Labels := by
      have ha : raw15160step1 = (fun i j => raw15160step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15160step1 raw15160step0; decide +kernel
      have hl : raw15160step1Labels = raw15160step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15160step0 raw15160step0Labels permutation37 permutation5
    mixedMoment B raw15160step1 raw15160step1Labels = mixedMoment B raw15160step2 raw15160step2Labels := by
      have ha : raw15160step2 = -raw15160step1 := by apply Matrix.ext; change ∀ i j, raw15160step2 i j = -(raw15160step1 i j); unfold raw15160step2 raw15160step1; decide +kernel
      have hl : raw15160step2Labels = raw15160step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15160step2 raw15160step2Labels = mixedMoment B raw15160step3 raw15160step3Labels := by
      have ha : raw15160step3 = raw15160step2 := by apply Matrix.ext; unfold raw15160step3 raw15160step2; decide +kernel
      have hl : raw15160step2Labels = labelEmbedding1 ∘ raw15160step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15160step2 raw15160step2Labels raw15160step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw15161 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw15161Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw15161step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw15161step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15161step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15161step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15161step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15161step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15161 raw15161Labels = mixedMoment B node3996 node3996Labels := by
  calc
    mixedMoment B raw15161 raw15161Labels = mixedMoment B raw15161step0 raw15161step0Labels := by
      have hz : ∀ j, raw15161 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15161step0 = (fun i j => raw15161 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15161step0 raw15161; decide +kernel
      have hl : raw15161step0Labels = raw15161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15161 raw15161Labels permutation346 hz
    mixedMoment B raw15161step0 raw15161step0Labels = mixedMoment B raw15161step1 raw15161step1Labels := by
      have ha : raw15161step1 = (fun i j => raw15161step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15161step1 raw15161step0; decide +kernel
      have hl : raw15161step1Labels = raw15161step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15161step0 raw15161step0Labels permutation151 permutation7
    mixedMoment B raw15161step1 raw15161step1Labels = mixedMoment B raw15161step2 raw15161step2Labels := by
      have ha : raw15161step2 = -raw15161step1 := by apply Matrix.ext; change ∀ i j, raw15161step2 i j = -(raw15161step1 i j); unfold raw15161step2 raw15161step1; decide +kernel
      have hl : raw15161step2Labels = raw15161step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15161step2 raw15161step2Labels = mixedMoment B raw15161step3 raw15161step3Labels := by
      have ha : raw15161step3 = raw15161step2 := by apply Matrix.ext; unfold raw15161step3 raw15161step2; decide +kernel
      have hl : raw15161step2Labels = labelEmbedding1 ∘ raw15161step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15161step2 raw15161step2Labels raw15161step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3996 node3996Labels := by rfl

def raw15162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15162Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15162step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15162step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15162step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15162step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15162step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15162 raw15162Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw15162 raw15162Labels = mixedMoment B raw15162step0 raw15162step0Labels := by
      have hz : ∀ j, raw15162 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15162step0 = (fun i j => raw15162 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15162step0 raw15162; decide +kernel
      have hl : raw15162step0Labels = raw15162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15162 raw15162Labels permutation346 hz
    mixedMoment B raw15162step0 raw15162step0Labels = mixedMoment B raw15162step1 raw15162step1Labels := by
      have ha : raw15162step1 = (fun i j => raw15162step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15162step1 raw15162step0; decide +kernel
      have hl : raw15162step1Labels = raw15162step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15162step0 raw15162step0Labels permutation44 permutation5
    mixedMoment B raw15162step1 raw15162step1Labels = mixedMoment B raw15162step2 raw15162step2Labels := by
      have ha : raw15162step2 = -raw15162step1 := by apply Matrix.ext; change ∀ i j, raw15162step2 i j = -(raw15162step1 i j); unfold raw15162step2 raw15162step1; decide +kernel
      have hl : raw15162step2Labels = raw15162step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15162step2 raw15162step2Labels = mixedMoment B raw15162step3 raw15162step3Labels := by
      have ha : raw15162step3 = raw15162step2 := by apply Matrix.ext; unfold raw15162step3 raw15162step2; decide +kernel
      have hl : raw15162step2Labels = labelEmbedding1 ∘ raw15162step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15162step2 raw15162step2Labels raw15162step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw15163 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15163Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15163step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15163step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15163step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15163step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15163 raw15163Labels = mixedMoment B node4035 node4035Labels := by
  calc
    mixedMoment B raw15163 raw15163Labels = mixedMoment B raw15163step0 raw15163step0Labels := by
      have hz : ∀ j, raw15163 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15163step0 = (fun i j => raw15163 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15163step0 raw15163; decide +kernel
      have hl : raw15163step0Labels = raw15163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15163 raw15163Labels permutation346 hz
    mixedMoment B raw15163step0 raw15163step0Labels = mixedMoment B raw15163step1 raw15163step1Labels := by
      have ha : raw15163step1 = (fun i j => raw15163step0 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15163step1 raw15163step0; decide +kernel
      have hl : raw15163step1Labels = raw15163step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15163step0 raw15163step0Labels permutation145 permutation5
    mixedMoment B raw15163step1 raw15163step1Labels = mixedMoment B raw15163step2 raw15163step2Labels := by
      have ha : raw15163step2 = raw15163step1 := by apply Matrix.ext; unfold raw15163step2 raw15163step1; decide +kernel
      have hl : raw15163step1Labels = labelEmbedding1 ∘ raw15163step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15163step1 raw15163step1Labels raw15163step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4035 node4035Labels := by rfl

def raw15164 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15164Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15164step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15164step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15164step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15164 raw15164Labels = mixedMoment B node4032 node4032Labels := by
  calc
    mixedMoment B raw15164 raw15164Labels = mixedMoment B raw15164step0 raw15164step0Labels := by
      have ha : raw15164step0 = (fun i j => raw15164 (permutation654 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15164step0 raw15164; decide +kernel
      have hl : raw15164step0Labels = raw15164Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15164 raw15164Labels permutation654 permutation5
    mixedMoment B raw15164step0 raw15164step0Labels = mixedMoment B raw15164step1 raw15164step1Labels := by
      have ha : raw15164step1 = raw15164step0 := by apply Matrix.ext; unfold raw15164step1 raw15164step0; decide +kernel
      have hl : raw15164step0Labels = labelEmbedding1 ∘ raw15164step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15164step0 raw15164step0Labels raw15164step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4032 node4032Labels := by rfl

def raw15165 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15165Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw15165step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15165step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 0, 1], ![0, -2, 2]]
def raw15165step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15165step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0]]
def raw15165step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15165step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0]]
def raw15165step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15165 raw15165Labels = mixedMoment B node4037 node4037Labels := by
  calc
    mixedMoment B raw15165 raw15165Labels = mixedMoment B raw15165step0 raw15165step0Labels := by
      have hz : ∀ j, raw15165 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15165step0 = (fun i j => raw15165 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15165step0 raw15165; decide +kernel
      have hl : raw15165step0Labels = raw15165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15165 raw15165Labels permutation434 hz
    mixedMoment B raw15165step0 raw15165step0Labels = mixedMoment B raw15165step1 raw15165step1Labels := by
      have hz : ∀ j, raw15165step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw15165step1 = (fun i j => raw15165step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw15165step1 raw15165step0; decide +kernel
      have hl : raw15165step1Labels = raw15165step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15165step0 raw15165step0Labels permutation80 hz
    mixedMoment B raw15165step1 raw15165step1Labels = mixedMoment B raw15165step2 raw15165step2Labels := by
      have ha : raw15165step2 = (fun i j => raw15165step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15165step2 raw15165step1; decide +kernel
      have hl : raw15165step2Labels = raw15165step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15165step1 raw15165step1Labels permutation8 permutation7
    mixedMoment B raw15165step2 raw15165step2Labels = mixedMoment B raw15165step3 raw15165step3Labels := by
      have ha : raw15165step3 = raw15165step2 := by apply Matrix.ext; unfold raw15165step3 raw15165step2; decide +kernel
      have hl : raw15165step2Labels = labelEmbedding1 ∘ raw15165step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15165step2 raw15165step2Labels raw15165step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4037 node4037Labels := by rfl

def raw15166 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15166Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15166step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15166step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15166step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15166step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15166step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15166step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15166step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15166 raw15166Labels = mixedMoment B node4027 node4027Labels := by
  calc
    mixedMoment B raw15166 raw15166Labels = mixedMoment B raw15166step0 raw15166step0Labels := by
      have hz : ∀ j, raw15166 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15166step0 = (fun i j => raw15166 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15166step0 raw15166; decide +kernel
      have hl : raw15166step0Labels = raw15166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15166 raw15166Labels permutation346 hz
    mixedMoment B raw15166step0 raw15166step0Labels = mixedMoment B raw15166step1 raw15166step1Labels := by
      have ha : raw15166step1 = (fun i j => raw15166step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15166step1 raw15166step0; decide +kernel
      have hl : raw15166step1Labels = raw15166step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15166step0 raw15166step0Labels permutation44 permutation5
    mixedMoment B raw15166step1 raw15166step1Labels = mixedMoment B raw15166step2 raw15166step2Labels := by
      have ha : raw15166step2 = -raw15166step1 := by apply Matrix.ext; change ∀ i j, raw15166step2 i j = -(raw15166step1 i j); unfold raw15166step2 raw15166step1; decide +kernel
      have hl : raw15166step2Labels = raw15166step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15166step2 raw15166step2Labels = mixedMoment B raw15166step3 raw15166step3Labels := by
      have ha : raw15166step3 = raw15166step2 := by apply Matrix.ext; unfold raw15166step3 raw15166step2; decide +kernel
      have hl : raw15166step2Labels = labelEmbedding1 ∘ raw15166step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15166step2 raw15166step2Labels raw15166step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4027 node4027Labels := by rfl

def raw15167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15167Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15167step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw15167step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15167step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15167step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15167step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15167step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15167 raw15167Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw15167 raw15167Labels = mixedMoment B raw15167step0 raw15167step0Labels := by
      have hz : ∀ j, raw15167 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15167step0 = (fun i j => raw15167 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15167step0 raw15167; decide +kernel
      have hl : raw15167step0Labels = raw15167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15167 raw15167Labels permutation346 hz
    mixedMoment B raw15167step0 raw15167step0Labels = mixedMoment B raw15167step1 raw15167step1Labels := by
      have ha : raw15167step1 = (fun i j => raw15167step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15167step1 raw15167step0; decide +kernel
      have hl : raw15167step1Labels = raw15167step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15167step0 raw15167step0Labels permutation150 permutation3
    mixedMoment B raw15167step1 raw15167step1Labels = mixedMoment B raw15167step2 raw15167step2Labels := by
      have ha : raw15167step2 = -raw15167step1 := by apply Matrix.ext; change ∀ i j, raw15167step2 i j = -(raw15167step1 i j); unfold raw15167step2 raw15167step1; decide +kernel
      have hl : raw15167step2Labels = raw15167step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15167step2 raw15167step2Labels = mixedMoment B raw15167step3 raw15167step3Labels := by
      have ha : raw15167step3 = raw15167step2 := by apply Matrix.ext; unfold raw15167step3 raw15167step2; decide +kernel
      have hl : raw15167step2Labels = labelEmbedding6 ∘ raw15167step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15167step2 raw15167step2Labels raw15167step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw15168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15168Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15168step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15168step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15168step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15168step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15168step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15168step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15168 raw15168Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw15168 raw15168Labels = mixedMoment B raw15168step0 raw15168step0Labels := by
      have ha : raw15168step0 = (fun i j => raw15168 (permutation683 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15168step0 raw15168; decide +kernel
      have hl : raw15168step0Labels = raw15168Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15168 raw15168Labels permutation683 permutation3
    mixedMoment B raw15168step0 raw15168step0Labels = mixedMoment B raw15168step1 raw15168step1Labels := by
      have ha : raw15168step1 = -raw15168step0 := by apply Matrix.ext; change ∀ i j, raw15168step1 i j = -(raw15168step0 i j); unfold raw15168step1 raw15168step0; decide +kernel
      have hl : raw15168step1Labels = raw15168step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15168step1 raw15168step1Labels = mixedMoment B raw15168step2 raw15168step2Labels := by
      have ha : raw15168step2 = raw15168step1 := by apply Matrix.ext; unfold raw15168step2 raw15168step1; decide +kernel
      have hl : raw15168step1Labels = labelEmbedding6 ∘ raw15168step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15168step1 raw15168step1Labels raw15168step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw15169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15169Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15169step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15169step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15169step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15169step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15169step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15169 raw15169Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw15169 raw15169Labels = mixedMoment B raw15169step0 raw15169step0Labels := by
      have hz : ∀ j, raw15169 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15169step0 = (fun i j => raw15169 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15169step0 raw15169; decide +kernel
      have hl : raw15169step0Labels = raw15169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15169 raw15169Labels permutation346 hz
    mixedMoment B raw15169step0 raw15169step0Labels = mixedMoment B raw15169step1 raw15169step1Labels := by
      have ha : raw15169step1 = (fun i j => raw15169step0 (permutation146 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15169step1 raw15169step0; decide +kernel
      have hl : raw15169step1Labels = raw15169step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15169step0 raw15169step0Labels permutation146 permutation3
    mixedMoment B raw15169step1 raw15169step1Labels = mixedMoment B raw15169step2 raw15169step2Labels := by
      have ha : raw15169step2 = -raw15169step1 := by apply Matrix.ext; change ∀ i j, raw15169step2 i j = -(raw15169step1 i j); unfold raw15169step2 raw15169step1; decide +kernel
      have hl : raw15169step2Labels = raw15169step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15169step2 raw15169step2Labels = mixedMoment B raw15169step3 raw15169step3Labels := by
      have ha : raw15169step3 = raw15169step2 := by apply Matrix.ext; unfold raw15169step3 raw15169step2; decide +kernel
      have hl : raw15169step2Labels = labelEmbedding6 ∘ raw15169step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15169step2 raw15169step2Labels raw15169step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw15170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw15170Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw15170step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw15170step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15170step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15170step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15170step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15170step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15170 raw15170Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw15170 raw15170Labels = mixedMoment B raw15170step0 raw15170step0Labels := by
      have hz : ∀ j, raw15170 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15170step0 = (fun i j => raw15170 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15170step0 raw15170; decide +kernel
      have hl : raw15170step0Labels = raw15170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15170 raw15170Labels permutation346 hz
    mixedMoment B raw15170step0 raw15170step0Labels = mixedMoment B raw15170step1 raw15170step1Labels := by
      have ha : raw15170step1 = (fun i j => raw15170step0 (permutation51 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15170step1 raw15170step0; decide +kernel
      have hl : raw15170step1Labels = raw15170step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15170step0 raw15170step0Labels permutation51 permutation6
    mixedMoment B raw15170step1 raw15170step1Labels = mixedMoment B raw15170step2 raw15170step2Labels := by
      have ha : raw15170step2 = -raw15170step1 := by apply Matrix.ext; change ∀ i j, raw15170step2 i j = -(raw15170step1 i j); unfold raw15170step2 raw15170step1; decide +kernel
      have hl : raw15170step2Labels = raw15170step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15170step2 raw15170step2Labels = mixedMoment B raw15170step3 raw15170step3Labels := by
      have ha : raw15170step3 = raw15170step2 := by apply Matrix.ext; unfold raw15170step3 raw15170step2; decide +kernel
      have hl : raw15170step2Labels = labelEmbedding9 ∘ raw15170step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15170step2 raw15170step2Labels raw15170step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw15171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15171Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15171step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15171step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15171step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15171step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15171 raw15171Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw15171 raw15171Labels = mixedMoment B raw15171step0 raw15171step0Labels := by
      have ha : raw15171step0 = (fun i j => raw15171 (permutation273 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15171step0 raw15171; decide +kernel
      have hl : raw15171step0Labels = raw15171Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15171 raw15171Labels permutation273 permutation3
    mixedMoment B raw15171step0 raw15171step0Labels = mixedMoment B raw15171step1 raw15171step1Labels := by
      have ha : raw15171step1 = raw15171step0 := by apply Matrix.ext; unfold raw15171step1 raw15171step0; decide +kernel
      have hl : raw15171step0Labels = labelEmbedding6 ∘ raw15171step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15171step0 raw15171step0Labels raw15171step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw15172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15172Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15172step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15172step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15172step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15172step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15172step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15172step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15172 raw15172Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw15172 raw15172Labels = mixedMoment B raw15172step0 raw15172step0Labels := by
      have ha : raw15172step0 = (fun i j => raw15172 (permutation644 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15172step0 raw15172; decide +kernel
      have hl : raw15172step0Labels = raw15172Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15172 raw15172Labels permutation644 permutation3
    mixedMoment B raw15172step0 raw15172step0Labels = mixedMoment B raw15172step1 raw15172step1Labels := by
      have ha : raw15172step1 = -raw15172step0 := by apply Matrix.ext; change ∀ i j, raw15172step1 i j = -(raw15172step0 i j); unfold raw15172step1 raw15172step0; decide +kernel
      have hl : raw15172step1Labels = raw15172step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15172step1 raw15172step1Labels = mixedMoment B raw15172step2 raw15172step2Labels := by
      have ha : raw15172step2 = raw15172step1 := by apply Matrix.ext; unfold raw15172step2 raw15172step1; decide +kernel
      have hl : raw15172step1Labels = labelEmbedding6 ∘ raw15172step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15172step1 raw15172step1Labels raw15172step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw15173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw15173Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15173step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15173 raw15173Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw15173 raw15173Labels = mixedMoment B raw15173step0 raw15173step0Labels := by
      have ha : raw15173step0 = (fun i j => raw15173 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15173step0 raw15173; decide +kernel
      have hl : raw15173step0Labels = raw15173Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15173 raw15173Labels permutation159 permutation2
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw15174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15174Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15174step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15174step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15174step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15174 raw15174Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw15174 raw15174Labels = mixedMoment B raw15174step0 raw15174step0Labels := by
      have hz : ∀ j, raw15174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15174step0 = (fun i j => raw15174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15174step0 raw15174; decide +kernel
      have hl : raw15174step0Labels = raw15174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15174 raw15174Labels permutation346 hz
    mixedMoment B raw15174step0 raw15174step0Labels = mixedMoment B raw15174step1 raw15174step1Labels := by
      have ha : raw15174step1 = (fun i j => raw15174step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15174step1 raw15174step0; decide +kernel
      have hl : raw15174step1Labels = raw15174step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15174step0 raw15174step0Labels permutation56 permutation3
    mixedMoment B raw15174step1 raw15174step1Labels = mixedMoment B raw15174step2 raw15174step2Labels := by
      have ha : raw15174step2 = raw15174step1 := by apply Matrix.ext; unfold raw15174step2 raw15174step1; decide +kernel
      have hl : raw15174step1Labels = labelEmbedding6 ∘ raw15174step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15174step1 raw15174step1Labels raw15174step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5387 node5387Labels := by rfl

def raw15175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15175Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15175 raw15175Labels = mixedMoment B node5417 node5417Labels := by
  calc
    _ = mixedMoment B node5417 node5417Labels := by rfl

def raw15176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw15176Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw15176step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15176step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15176step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15176step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15176step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15176step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15176 raw15176Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw15176 raw15176Labels = mixedMoment B raw15176step0 raw15176step0Labels := by
      have hz : ∀ j, raw15176 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15176step0 = (fun i j => raw15176 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15176step0 raw15176; decide +kernel
      have hl : raw15176step0Labels = raw15176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15176 raw15176Labels permutation346 hz
    mixedMoment B raw15176step0 raw15176step0Labels = mixedMoment B raw15176step1 raw15176step1Labels := by
      have ha : raw15176step1 = (fun i j => raw15176step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15176step1 raw15176step0; decide +kernel
      have hl : raw15176step1Labels = raw15176step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15176step0 raw15176step0Labels permutation150 permutation3
    mixedMoment B raw15176step1 raw15176step1Labels = mixedMoment B raw15176step2 raw15176step2Labels := by
      have ha : raw15176step2 = -raw15176step1 := by apply Matrix.ext; change ∀ i j, raw15176step2 i j = -(raw15176step1 i j); unfold raw15176step2 raw15176step1; decide +kernel
      have hl : raw15176step2Labels = raw15176step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15176step2 raw15176step2Labels = mixedMoment B raw15176step3 raw15176step3Labels := by
      have ha : raw15176step3 = raw15176step2 := by apply Matrix.ext; unfold raw15176step3 raw15176step2; decide +kernel
      have hl : raw15176step2Labels = labelEmbedding6 ∘ raw15176step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15176step2 raw15176step2Labels raw15176step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw15177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw15177Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15177step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15177step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15177step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15177step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15177step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15177 raw15177Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw15177 raw15177Labels = mixedMoment B raw15177step0 raw15177step0Labels := by
      have ha : raw15177step0 = (fun i j => raw15177 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15177step0 raw15177; decide +kernel
      have hl : raw15177step0Labels = raw15177Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15177 raw15177Labels permutation686 permutation3
    mixedMoment B raw15177step0 raw15177step0Labels = mixedMoment B raw15177step1 raw15177step1Labels := by
      have ha : raw15177step1 = -raw15177step0 := by apply Matrix.ext; change ∀ i j, raw15177step1 i j = -(raw15177step0 i j); unfold raw15177step1 raw15177step0; decide +kernel
      have hl : raw15177step1Labels = raw15177step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15177step1 raw15177step1Labels = mixedMoment B raw15177step2 raw15177step2Labels := by
      have ha : raw15177step2 = raw15177step1 := by apply Matrix.ext; unfold raw15177step2 raw15177step1; decide +kernel
      have hl : raw15177step1Labels = labelEmbedding6 ∘ raw15177step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15177step1 raw15177step1Labels raw15177step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5354 node5354Labels := by rfl

def raw15178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw15178Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw15178step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15178step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15178step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15178step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15178step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15178 raw15178Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw15178 raw15178Labels = mixedMoment B raw15178step0 raw15178step0Labels := by
      have hz : ∀ j, raw15178 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15178step0 = (fun i j => raw15178 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15178step0 raw15178; decide +kernel
      have hl : raw15178step0Labels = raw15178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15178 raw15178Labels permutation346 hz
    mixedMoment B raw15178step0 raw15178step0Labels = mixedMoment B raw15178step1 raw15178step1Labels := by
      have ha : raw15178step1 = (fun i j => raw15178step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15178step1 raw15178step0; decide +kernel
      have hl : raw15178step1Labels = raw15178step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15178step0 raw15178step0Labels permutation149 permutation3
    mixedMoment B raw15178step1 raw15178step1Labels = mixedMoment B raw15178step2 raw15178step2Labels := by
      have ha : raw15178step2 = -raw15178step1 := by apply Matrix.ext; change ∀ i j, raw15178step2 i j = -(raw15178step1 i j); unfold raw15178step2 raw15178step1; decide +kernel
      have hl : raw15178step2Labels = raw15178step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15178step2 raw15178step2Labels = mixedMoment B raw15178step3 raw15178step3Labels := by
      have ha : raw15178step3 = raw15178step2 := by apply Matrix.ext; unfold raw15178step3 raw15178step2; decide +kernel
      have hl : raw15178step2Labels = labelEmbedding6 ∘ raw15178step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15178step2 raw15178step2Labels raw15178step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw15179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw15179Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw15179step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15179step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15179 raw15179Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw15179 raw15179Labels = mixedMoment B raw15179step0 raw15179step0Labels := by
      have hz : ∀ j, raw15179 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15179step0 = (fun i j => raw15179 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15179step0 raw15179; decide +kernel
      have hl : raw15179step0Labels = raw15179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15179 raw15179Labels permutation346 hz
    mixedMoment B raw15179step0 raw15179step0Labels = mixedMoment B raw15179step1 raw15179step1Labels := by
      have ha : raw15179step1 = (fun i j => raw15179step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15179step1 raw15179step0; decide +kernel
      have hl : raw15179step1Labels = raw15179step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15179step0 raw15179step0Labels permutation33 permutation2
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw15180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw15180Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw15180step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15180step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15180step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15180step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15180step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15180 raw15180Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw15180 raw15180Labels = mixedMoment B raw15180step0 raw15180step0Labels := by
      have hz : ∀ j, raw15180 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15180step0 = (fun i j => raw15180 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15180step0 raw15180; decide +kernel
      have hl : raw15180step0Labels = raw15180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15180 raw15180Labels permutation346 hz
    mixedMoment B raw15180step0 raw15180step0Labels = mixedMoment B raw15180step1 raw15180step1Labels := by
      have ha : raw15180step1 = (fun i j => raw15180step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15180step1 raw15180step0; decide +kernel
      have hl : raw15180step1Labels = raw15180step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15180step0 raw15180step0Labels permutation150 permutation3
    mixedMoment B raw15180step1 raw15180step1Labels = mixedMoment B raw15180step2 raw15180step2Labels := by
      have ha : raw15180step2 = -raw15180step1 := by apply Matrix.ext; change ∀ i j, raw15180step2 i j = -(raw15180step1 i j); unfold raw15180step2 raw15180step1; decide +kernel
      have hl : raw15180step2Labels = raw15180step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15180step2 raw15180step2Labels = mixedMoment B raw15180step3 raw15180step3Labels := by
      have ha : raw15180step3 = raw15180step2 := by apply Matrix.ext; unfold raw15180step3 raw15180step2; decide +kernel
      have hl : raw15180step2Labels = labelEmbedding6 ∘ raw15180step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15180step2 raw15180step2Labels raw15180step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw15181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw15181Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15181step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15181step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15181step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15181step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15181 raw15181Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw15181 raw15181Labels = mixedMoment B raw15181step0 raw15181step0Labels := by
      have ha : raw15181step0 = (fun i j => raw15181 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15181step0 raw15181; decide +kernel
      have hl : raw15181step0Labels = raw15181Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15181 raw15181Labels permutation686 permutation3
    mixedMoment B raw15181step0 raw15181step0Labels = mixedMoment B raw15181step1 raw15181step1Labels := by
      have ha : raw15181step1 = -raw15181step0 := by apply Matrix.ext; change ∀ i j, raw15181step1 i j = -(raw15181step0 i j); unfold raw15181step1 raw15181step0; decide +kernel
      have hl : raw15181step1Labels = raw15181step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15181step1 raw15181step1Labels = mixedMoment B raw15181step2 raw15181step2Labels := by
      have ha : raw15181step2 = raw15181step1 := by apply Matrix.ext; unfold raw15181step2 raw15181step1; decide +kernel
      have hl : raw15181step1Labels = labelEmbedding6 ∘ raw15181step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15181step1 raw15181step1Labels raw15181step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

def raw15182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw15182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw15182step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15182step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15182step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15182step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15182step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15182step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15182 raw15182Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw15182 raw15182Labels = mixedMoment B raw15182step0 raw15182step0Labels := by
      have hz : ∀ j, raw15182 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15182step0 = (fun i j => raw15182 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15182step0 raw15182; decide +kernel
      have hl : raw15182step0Labels = raw15182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15182 raw15182Labels permutation346 hz
    mixedMoment B raw15182step0 raw15182step0Labels = mixedMoment B raw15182step1 raw15182step1Labels := by
      have ha : raw15182step1 = (fun i j => raw15182step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15182step1 raw15182step0; decide +kernel
      have hl : raw15182step1Labels = raw15182step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15182step0 raw15182step0Labels permutation149 permutation3
    mixedMoment B raw15182step1 raw15182step1Labels = mixedMoment B raw15182step2 raw15182step2Labels := by
      have ha : raw15182step2 = -raw15182step1 := by apply Matrix.ext; change ∀ i j, raw15182step2 i j = -(raw15182step1 i j); unfold raw15182step2 raw15182step1; decide +kernel
      have hl : raw15182step2Labels = raw15182step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15182step2 raw15182step2Labels = mixedMoment B raw15182step3 raw15182step3Labels := by
      have ha : raw15182step3 = raw15182step2 := by apply Matrix.ext; unfold raw15182step3 raw15182step2; decide +kernel
      have hl : raw15182step2Labels = labelEmbedding6 ∘ raw15182step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15182step2 raw15182step2Labels raw15182step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw15183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15183Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15183step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw15183step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15183step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15183 raw15183Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw15183 raw15183Labels = mixedMoment B raw15183step0 raw15183step0Labels := by
      have hz : ∀ j, raw15183 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15183step0 = (fun i j => raw15183 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15183step0 raw15183; decide +kernel
      have hl : raw15183step0Labels = raw15183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15183 raw15183Labels permutation346 hz
    mixedMoment B raw15183step0 raw15183step0Labels = mixedMoment B raw15183step1 raw15183step1Labels := by
      have ha : raw15183step1 = (fun i j => raw15183step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15183step1 raw15183step0; decide +kernel
      have hl : raw15183step1Labels = raw15183step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15183step0 raw15183step0Labels permutation150 permutation3
    mixedMoment B raw15183step1 raw15183step1Labels = mixedMoment B raw15183step2 raw15183step2Labels := by
      have ha : raw15183step2 = -raw15183step1 := by apply Matrix.ext; change ∀ i j, raw15183step2 i j = -(raw15183step1 i j); unfold raw15183step2 raw15183step1; decide +kernel
      have hl : raw15183step2Labels = raw15183step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw15184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15184Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15184step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15184step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15184step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15184 raw15184Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw15184 raw15184Labels = mixedMoment B raw15184step0 raw15184step0Labels := by
      have ha : raw15184step0 = (fun i j => raw15184 (permutation683 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15184step0 raw15184; decide +kernel
      have hl : raw15184step0Labels = raw15184Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15184 raw15184Labels permutation683 permutation3
    mixedMoment B raw15184step0 raw15184step0Labels = mixedMoment B raw15184step1 raw15184step1Labels := by
      have ha : raw15184step1 = -raw15184step0 := by apply Matrix.ext; change ∀ i j, raw15184step1 i j = -(raw15184step0 i j); unfold raw15184step1 raw15184step0; decide +kernel
      have hl : raw15184step1Labels = raw15184step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3849 node3849Labels := by rfl

def raw15185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15185Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15185step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15185step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15185step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15185 raw15185Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw15185 raw15185Labels = mixedMoment B raw15185step0 raw15185step0Labels := by
      have hz : ∀ j, raw15185 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15185step0 = (fun i j => raw15185 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15185step0 raw15185; decide +kernel
      have hl : raw15185step0Labels = raw15185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15185 raw15185Labels permutation346 hz
    mixedMoment B raw15185step0 raw15185step0Labels = mixedMoment B raw15185step1 raw15185step1Labels := by
      have ha : raw15185step1 = (fun i j => raw15185step0 (permutation146 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15185step1 raw15185step0; decide +kernel
      have hl : raw15185step1Labels = raw15185step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15185step0 raw15185step0Labels permutation146 permutation3
    mixedMoment B raw15185step1 raw15185step1Labels = mixedMoment B raw15185step2 raw15185step2Labels := by
      have ha : raw15185step2 = -raw15185step1 := by apply Matrix.ext; change ∀ i j, raw15185step2 i j = -(raw15185step1 i j); unfold raw15185step2 raw15185step1; decide +kernel
      have hl : raw15185step2Labels = raw15185step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3857 node3857Labels := by rfl

def raw15186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw15186Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw15186step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw15186step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15186 raw15186Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw15186 raw15186Labels = mixedMoment B raw15186step0 raw15186step0Labels := by
      have hz : ∀ j, raw15186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15186step0 = (fun i j => raw15186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15186step0 raw15186; decide +kernel
      have hl : raw15186step0Labels = raw15186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15186 raw15186Labels permutation346 hz
    mixedMoment B raw15186step0 raw15186step0Labels = mixedMoment B raw15186step1 raw15186step1Labels := by
      have ha : raw15186step1 = (fun i j => raw15186step0 (permutation51 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15186step1 raw15186step0; decide +kernel
      have hl : raw15186step1Labels = raw15186step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15186step0 raw15186step0Labels permutation51 permutation6
    mixedMoment B raw15186step1 raw15186step1Labels = mixedMoment B raw15186step2 raw15186step2Labels := by
      have ha : raw15186step2 = -raw15186step1 := by apply Matrix.ext; change ∀ i j, raw15186step2 i j = -(raw15186step1 i j); unfold raw15186step2 raw15186step1; decide +kernel
      have hl : raw15186step2Labels = raw15186step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw15187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15187Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15187step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15187 raw15187Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw15187 raw15187Labels = mixedMoment B raw15187step0 raw15187step0Labels := by
      have ha : raw15187step0 = (fun i j => raw15187 (permutation273 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15187step0 raw15187; decide +kernel
      have hl : raw15187step0Labels = raw15187Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15187 raw15187Labels permutation273 permutation3
    _ = mixedMoment B node3719 node3719Labels := by rfl

def raw15188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15188Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15188step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15188step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15188step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15188 raw15188Labels = mixedMoment B node3782 node3782Labels := by
  calc
    mixedMoment B raw15188 raw15188Labels = mixedMoment B raw15188step0 raw15188step0Labels := by
      have ha : raw15188step0 = (fun i j => raw15188 (permutation644 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15188step0 raw15188; decide +kernel
      have hl : raw15188step0Labels = raw15188Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15188 raw15188Labels permutation644 permutation3
    mixedMoment B raw15188step0 raw15188step0Labels = mixedMoment B raw15188step1 raw15188step1Labels := by
      have ha : raw15188step1 = -raw15188step0 := by apply Matrix.ext; change ∀ i j, raw15188step1 i j = -(raw15188step0 i j); unfold raw15188step1 raw15188step0; decide +kernel
      have hl : raw15188step1Labels = raw15188step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3782 node3782Labels := by rfl

def raw15189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw15189Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15189step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15189 raw15189Labels = mixedMoment B node4033 node4033Labels := by
  calc
    mixedMoment B raw15189 raw15189Labels = mixedMoment B raw15189step0 raw15189step0Labels := by
      have ha : raw15189step0 = (fun i j => raw15189 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15189step0 raw15189; decide +kernel
      have hl : raw15189step0Labels = raw15189Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15189 raw15189Labels permutation160 permutation3
    _ = mixedMoment B node4033 node4033Labels := by rfl

def raw15190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15190Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15190step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15190step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15190 raw15190Labels = mixedMoment B node3736 node3736Labels := by
  calc
    mixedMoment B raw15190 raw15190Labels = mixedMoment B raw15190step0 raw15190step0Labels := by
      have hz : ∀ j, raw15190 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15190step0 = (fun i j => raw15190 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15190step0 raw15190; decide +kernel
      have hl : raw15190step0Labels = raw15190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15190 raw15190Labels permutation346 hz
    mixedMoment B raw15190step0 raw15190step0Labels = mixedMoment B raw15190step1 raw15190step1Labels := by
      have ha : raw15190step1 = (fun i j => raw15190step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15190step1 raw15190step0; decide +kernel
      have hl : raw15190step1Labels = raw15190step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15190step0 raw15190step0Labels permutation56 permutation3
    _ = mixedMoment B node3736 node3736Labels := by rfl

def raw15191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15191Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15191step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15191step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15191step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15191step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15191 raw15191Labels = mixedMoment B node3823 node3823Labels := by
  calc
    mixedMoment B raw15191 raw15191Labels = mixedMoment B raw15191step0 raw15191step0Labels := by
      have ha : raw15191step0 = (fun i j => raw15191 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15191step0 raw15191; decide +kernel
      have hl : raw15191step0Labels = raw15191Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15191 raw15191Labels permutation662 permutation3
    mixedMoment B raw15191step0 raw15191step0Labels = mixedMoment B raw15191step1 raw15191step1Labels := by
      have ha : raw15191step1 = -raw15191step0 := by apply Matrix.ext; change ∀ i j, raw15191step1 i j = -(raw15191step0 i j); unfold raw15191step1 raw15191step0; decide +kernel
      have hl : raw15191step1Labels = raw15191step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3823 node3823Labels := by rfl

def raw15192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw15192Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw15192step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15192step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15192 raw15192Labels = mixedMoment B node4036 node4036Labels := by
  calc
    mixedMoment B raw15192 raw15192Labels = mixedMoment B raw15192step0 raw15192step0Labels := by
      have hz : ∀ j, raw15192 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15192step0 = (fun i j => raw15192 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15192step0 raw15192; decide +kernel
      have hl : raw15192step0Labels = raw15192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15192 raw15192Labels permutation346 hz
    mixedMoment B raw15192step0 raw15192step0Labels = mixedMoment B raw15192step1 raw15192step1Labels := by
      have ha : raw15192step1 = (fun i j => raw15192step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15192step1 raw15192step0; decide +kernel
      have hl : raw15192step1Labels = raw15192step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15192step0 raw15192step0Labels permutation32 permutation3
    _ = mixedMoment B node4036 node4036Labels := by rfl

def raw15193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw15193Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw15193step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15193step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15193step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15193 raw15193Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw15193 raw15193Labels = mixedMoment B raw15193step0 raw15193step0Labels := by
      have hz : ∀ j, raw15193 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15193step0 = (fun i j => raw15193 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15193step0 raw15193; decide +kernel
      have hl : raw15193step0Labels = raw15193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15193 raw15193Labels permutation346 hz
    mixedMoment B raw15193step0 raw15193step0Labels = mixedMoment B raw15193step1 raw15193step1Labels := by
      have ha : raw15193step1 = (fun i j => raw15193step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15193step1 raw15193step0; decide +kernel
      have hl : raw15193step1Labels = raw15193step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15193step0 raw15193step0Labels permutation150 permutation3
    mixedMoment B raw15193step1 raw15193step1Labels = mixedMoment B raw15193step2 raw15193step2Labels := by
      have ha : raw15193step2 = -raw15193step1 := by apply Matrix.ext; change ∀ i j, raw15193step2 i j = -(raw15193step1 i j); unfold raw15193step2 raw15193step1; decide +kernel
      have hl : raw15193step2Labels = raw15193step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3693 node3693Labels := by rfl

def raw15194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw15194Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15194step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15194step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15194step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15194 raw15194Labels = mixedMoment B node3692 node3692Labels := by
  calc
    mixedMoment B raw15194 raw15194Labels = mixedMoment B raw15194step0 raw15194step0Labels := by
      have ha : raw15194step0 = (fun i j => raw15194 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15194step0 raw15194; decide +kernel
      have hl : raw15194step0Labels = raw15194Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15194 raw15194Labels permutation686 permutation3
    mixedMoment B raw15194step0 raw15194step0Labels = mixedMoment B raw15194step1 raw15194step1Labels := by
      have ha : raw15194step1 = -raw15194step0 := by apply Matrix.ext; change ∀ i j, raw15194step1 i j = -(raw15194step0 i j); unfold raw15194step1 raw15194step0; decide +kernel
      have hl : raw15194step1Labels = raw15194step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3692 node3692Labels := by rfl

def raw15195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw15195Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw15195step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15195step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15195step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15195 raw15195Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw15195 raw15195Labels = mixedMoment B raw15195step0 raw15195step0Labels := by
      have hz : ∀ j, raw15195 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15195step0 = (fun i j => raw15195 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15195step0 raw15195; decide +kernel
      have hl : raw15195step0Labels = raw15195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15195 raw15195Labels permutation346 hz
    mixedMoment B raw15195step0 raw15195step0Labels = mixedMoment B raw15195step1 raw15195step1Labels := by
      have ha : raw15195step1 = (fun i j => raw15195step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15195step1 raw15195step0; decide +kernel
      have hl : raw15195step1Labels = raw15195step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15195step0 raw15195step0Labels permutation149 permutation3
    mixedMoment B raw15195step1 raw15195step1Labels = mixedMoment B raw15195step2 raw15195step2Labels := by
      have ha : raw15195step2 = -raw15195step1 := by apply Matrix.ext; change ∀ i j, raw15195step2 i j = -(raw15195step1 i j); unfold raw15195step2 raw15195step1; decide +kernel
      have hl : raw15195step2Labels = raw15195step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3706 node3706Labels := by rfl

def raw15196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw15196Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw15196step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15196step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15196step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15196step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15196 raw15196Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw15196 raw15196Labels = mixedMoment B raw15196step0 raw15196step0Labels := by
      have hz : ∀ j, raw15196 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15196step0 = (fun i j => raw15196 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15196step0 raw15196; decide +kernel
      have hl : raw15196step0Labels = raw15196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15196 raw15196Labels permutation346 hz
    mixedMoment B raw15196step0 raw15196step0Labels = mixedMoment B raw15196step1 raw15196step1Labels := by
      have ha : raw15196step1 = (fun i j => raw15196step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15196step1 raw15196step0; decide +kernel
      have hl : raw15196step1Labels = raw15196step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15196step0 raw15196step0Labels permutation127 permutation3
    mixedMoment B raw15196step1 raw15196step1Labels = mixedMoment B raw15196step2 raw15196step2Labels := by
      have ha : raw15196step2 = -raw15196step1 := by apply Matrix.ext; change ∀ i j, raw15196step2 i j = -(raw15196step1 i j); unfold raw15196step2 raw15196step1; decide +kernel
      have hl : raw15196step2Labels = raw15196step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw15197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw15197Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw15197step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw15197step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15197step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15197 raw15197Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw15197 raw15197Labels = mixedMoment B raw15197step0 raw15197step0Labels := by
      have hz : ∀ j, raw15197 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15197step0 = (fun i j => raw15197 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15197step0 raw15197; decide +kernel
      have hl : raw15197step0Labels = raw15197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15197 raw15197Labels permutation346 hz
    mixedMoment B raw15197step0 raw15197step0Labels = mixedMoment B raw15197step1 raw15197step1Labels := by
      have ha : raw15197step1 = (fun i j => raw15197step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15197step1 raw15197step0; decide +kernel
      have hl : raw15197step1Labels = raw15197step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15197step0 raw15197step0Labels permutation150 permutation3
    mixedMoment B raw15197step1 raw15197step1Labels = mixedMoment B raw15197step2 raw15197step2Labels := by
      have ha : raw15197step2 = -raw15197step1 := by apply Matrix.ext; change ∀ i j, raw15197step2 i j = -(raw15197step1 i j); unfold raw15197step2 raw15197step1; decide +kernel
      have hl : raw15197step2Labels = raw15197step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2028 node2028Labels := by rfl

def raw15198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw15198Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15198step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15198step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15198step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15198 raw15198Labels = mixedMoment B node2023 node2023Labels := by
  calc
    mixedMoment B raw15198 raw15198Labels = mixedMoment B raw15198step0 raw15198step0Labels := by
      have ha : raw15198step0 = (fun i j => raw15198 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15198step0 raw15198; decide +kernel
      have hl : raw15198step0Labels = raw15198Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15198 raw15198Labels permutation686 permutation3
    mixedMoment B raw15198step0 raw15198step0Labels = mixedMoment B raw15198step1 raw15198step1Labels := by
      have ha : raw15198step1 = -raw15198step0 := by apply Matrix.ext; change ∀ i j, raw15198step1 i j = -(raw15198step0 i j); unfold raw15198step1 raw15198step0; decide +kernel
      have hl : raw15198step1Labels = raw15198step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2023 node2023Labels := by rfl

def raw15199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw15199Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw15199step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15199step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15199step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15199step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15199 raw15199Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw15199 raw15199Labels = mixedMoment B raw15199step0 raw15199step0Labels := by
      have hz : ∀ j, raw15199 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15199step0 = (fun i j => raw15199 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15199step0 raw15199; decide +kernel
      have hl : raw15199step0Labels = raw15199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15199 raw15199Labels permutation346 hz
    mixedMoment B raw15199step0 raw15199step0Labels = mixedMoment B raw15199step1 raw15199step1Labels := by
      have ha : raw15199step1 = (fun i j => raw15199step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15199step1 raw15199step0; decide +kernel
      have hl : raw15199step1Labels = raw15199step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15199step0 raw15199step0Labels permutation149 permutation3
    mixedMoment B raw15199step1 raw15199step1Labels = mixedMoment B raw15199step2 raw15199step2Labels := by
      have ha : raw15199step2 = -raw15199step1 := by apply Matrix.ext; change ∀ i j, raw15199step2 i j = -(raw15199step1 i j); unfold raw15199step2 raw15199step1; decide +kernel
      have hl : raw15199step2Labels = raw15199step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2058 node2058Labels := by rfl

def raw15200 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15200step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15200step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15200step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15200step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15200step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15200 raw15200Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw15200 raw15200Labels = mixedMoment B raw15200step0 raw15200step0Labels := by
      have hz : ∀ j, raw15200 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15200step0 = (fun i j => raw15200 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15200step0 raw15200; decide +kernel
      have hl : raw15200step0Labels = raw15200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15200 raw15200Labels permutation346 hz
    mixedMoment B raw15200step0 raw15200step0Labels = mixedMoment B raw15200step1 raw15200step1Labels := by
      have ha : raw15200step1 = (fun i j => raw15200step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15200step1 raw15200step0; decide +kernel
      have hl : raw15200step1Labels = raw15200step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15200step0 raw15200step0Labels permutation151 permutation7
    mixedMoment B raw15200step1 raw15200step1Labels = mixedMoment B raw15200step2 raw15200step2Labels := by
      have ha : raw15200step2 = -raw15200step1 := by apply Matrix.ext; change ∀ i j, raw15200step2 i j = -(raw15200step1 i j); unfold raw15200step2 raw15200step1; decide +kernel
      have hl : raw15200step2Labels = raw15200step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15200step2 raw15200step2Labels = mixedMoment B raw15200step3 raw15200step3Labels := by
      have ha : raw15200step3 = raw15200step2 := by apply Matrix.ext; unfold raw15200step3 raw15200step2; decide +kernel
      have hl : raw15200step2Labels = labelEmbedding10 ∘ raw15200step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15200step2 raw15200step2Labels raw15200step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw15201 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw15201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw15201step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15201step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15201 raw15201Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw15201 raw15201Labels = mixedMoment B raw15201step0 raw15201step0Labels := by
      have hz : ∀ j, raw15201 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15201step0 = (fun i j => raw15201 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15201step0 raw15201; decide +kernel
      have hl : raw15201step0Labels = raw15201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15201 raw15201Labels permutation346 hz
    mixedMoment B raw15201step0 raw15201step0Labels = mixedMoment B raw15201step1 raw15201step1Labels := by
      have ha : raw15201step1 = (fun i j => raw15201step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15201step1 raw15201step0; decide +kernel
      have hl : raw15201step1Labels = raw15201step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15201step0 raw15201step0Labels permutation151 permutation2
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw15202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw15202step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw15202step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15202step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw15202step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15202 raw15202Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw15202 raw15202Labels = mixedMoment B raw15202step0 raw15202step0Labels := by
      have hz : ∀ j, raw15202 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15202step0 = (fun i j => raw15202 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15202step0 raw15202; decide +kernel
      have hl : raw15202step0Labels = raw15202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15202 raw15202Labels permutation346 hz
    mixedMoment B raw15202step0 raw15202step0Labels = mixedMoment B raw15202step1 raw15202step1Labels := by
      have ha : raw15202step1 = (fun i j => raw15202step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15202step1 raw15202step0; decide +kernel
      have hl : raw15202step1Labels = raw15202step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15202step0 raw15202step0Labels permutation50 permutation4
    mixedMoment B raw15202step1 raw15202step1Labels = mixedMoment B raw15202step2 raw15202step2Labels := by
      have ha : raw15202step2 = -raw15202step1 := by apply Matrix.ext; change ∀ i j, raw15202step2 i j = -(raw15202step1 i j); unfold raw15202step2 raw15202step1; decide +kernel
      have hl : raw15202step2Labels = raw15202step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15202step2 raw15202step2Labels = mixedMoment B raw15202step3 raw15202step3Labels := by
      have ha : raw15202step3 = raw15202step2 := by apply Matrix.ext; unfold raw15202step3 raw15202step2; decide +kernel
      have hl : raw15202step2Labels = labelEmbedding7 ∘ raw15202step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15202step2 raw15202step2Labels raw15202step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw15203 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw15203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw15203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15203step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15203 raw15203Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw15203 raw15203Labels = mixedMoment B raw15203step0 raw15203step0Labels := by
      have hz : ∀ j, raw15203 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15203step0 = (fun i j => raw15203 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15203step0 raw15203; decide +kernel
      have hl : raw15203step0Labels = raw15203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15203 raw15203Labels permutation346 hz
    mixedMoment B raw15203step0 raw15203step0Labels = mixedMoment B raw15203step1 raw15203step1Labels := by
      have ha : raw15203step1 = (fun i j => raw15203step0 (permutation147 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15203step1 raw15203step0; decide +kernel
      have hl : raw15203step1Labels = raw15203step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15203step0 raw15203step0Labels permutation147 permutation2
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw15204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw15204step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15204step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15204step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15204step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15204step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15204 raw15204Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw15204 raw15204Labels = mixedMoment B raw15204step0 raw15204step0Labels := by
      have ha : raw15204step0 = (fun i j => raw15204 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15204step0 raw15204; decide +kernel
      have hl : raw15204step0Labels = raw15204Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15204 raw15204Labels permutation170 permutation4
    mixedMoment B raw15204step0 raw15204step0Labels = mixedMoment B raw15204step1 raw15204step1Labels := by
      have ha : raw15204step1 = -raw15204step0 := by apply Matrix.ext; change ∀ i j, raw15204step1 i j = -(raw15204step0 i j); unfold raw15204step1 raw15204step0; decide +kernel
      have hl : raw15204step1Labels = raw15204step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15204step1 raw15204step1Labels = mixedMoment B raw15204step2 raw15204step2Labels := by
      have ha : raw15204step2 = raw15204step1 := by apply Matrix.ext; unfold raw15204step2 raw15204step1; decide +kernel
      have hl : raw15204step1Labels = labelEmbedding7 ∘ raw15204step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15204step1 raw15204step1Labels raw15204step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw15205 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15205step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15205step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15205step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15205 raw15205Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw15205 raw15205Labels = mixedMoment B raw15205step0 raw15205step0Labels := by
      have ha : raw15205step0 = (fun i j => raw15205 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15205step0 raw15205; decide +kernel
      have hl : raw15205step0Labels = raw15205Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15205 raw15205Labels permutation152 permutation6
    mixedMoment B raw15205step0 raw15205step0Labels = mixedMoment B raw15205step1 raw15205step1Labels := by
      have ha : raw15205step1 = raw15205step0 := by apply Matrix.ext; unfold raw15205step1 raw15205step0; decide +kernel
      have hl : raw15205step0Labels = labelEmbedding9 ∘ raw15205step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15205step0 raw15205step0Labels raw15205step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw15206 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw15206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15206step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15206 raw15206Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw15206 raw15206Labels = mixedMoment B raw15206step0 raw15206step0Labels := by
      have ha : raw15206step0 = (fun i j => raw15206 (permutation668 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15206step0 raw15206; decide +kernel
      have hl : raw15206step0Labels = raw15206Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15206 raw15206Labels permutation668 permutation2
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw15207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15207step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15207step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15207step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15207step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15207step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15207step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15207step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15207 raw15207Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw15207 raw15207Labels = mixedMoment B raw15207step0 raw15207step0Labels := by
      have hz : ∀ j, raw15207 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15207step0 = (fun i j => raw15207 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15207step0 raw15207; decide +kernel
      have hl : raw15207step0Labels = raw15207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15207 raw15207Labels permutation346 hz
    mixedMoment B raw15207step0 raw15207step0Labels = mixedMoment B raw15207step1 raw15207step1Labels := by
      have ha : raw15207step1 = (fun i j => raw15207step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15207step1 raw15207step0; decide +kernel
      have hl : raw15207step1Labels = raw15207step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15207step0 raw15207step0Labels permutation37 permutation4
    mixedMoment B raw15207step1 raw15207step1Labels = mixedMoment B raw15207step2 raw15207step2Labels := by
      have ha : raw15207step2 = -raw15207step1 := by apply Matrix.ext; change ∀ i j, raw15207step2 i j = -(raw15207step1 i j); unfold raw15207step2 raw15207step1; decide +kernel
      have hl : raw15207step2Labels = raw15207step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15207step2 raw15207step2Labels = mixedMoment B raw15207step3 raw15207step3Labels := by
      have ha : raw15207step3 = raw15207step2 := by apply Matrix.ext; unfold raw15207step3 raw15207step2; decide +kernel
      have hl : raw15207step2Labels = labelEmbedding7 ∘ raw15207step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15207step2 raw15207step2Labels raw15207step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw15208 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15208step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15208step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15208step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15208step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15208 raw15208Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw15208 raw15208Labels = mixedMoment B raw15208step0 raw15208step0Labels := by
      have hz : ∀ j, raw15208 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15208step0 = (fun i j => raw15208 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15208step0 raw15208; decide +kernel
      have hl : raw15208step0Labels = raw15208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15208 raw15208Labels permutation346 hz
    mixedMoment B raw15208step0 raw15208step0Labels = mixedMoment B raw15208step1 raw15208step1Labels := by
      have ha : raw15208step1 = (fun i j => raw15208step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15208step1 raw15208step0; decide +kernel
      have hl : raw15208step1Labels = raw15208step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15208step0 raw15208step0Labels permutation37 permutation4
    mixedMoment B raw15208step1 raw15208step1Labels = mixedMoment B raw15208step2 raw15208step2Labels := by
      have ha : raw15208step2 = -raw15208step1 := by apply Matrix.ext; change ∀ i j, raw15208step2 i j = -(raw15208step1 i j); unfold raw15208step2 raw15208step1; decide +kernel
      have hl : raw15208step2Labels = raw15208step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15208step2 raw15208step2Labels = mixedMoment B raw15208step3 raw15208step3Labels := by
      have ha : raw15208step3 = raw15208step2 := by apply Matrix.ext; unfold raw15208step3 raw15208step2; decide +kernel
      have hl : raw15208step2Labels = labelEmbedding7 ∘ raw15208step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15208step2 raw15208step2Labels raw15208step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw15209 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw15209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw15209step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15209step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15209 raw15209Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw15209 raw15209Labels = mixedMoment B raw15209step0 raw15209step0Labels := by
      have hz : ∀ j, raw15209 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15209step0 = (fun i j => raw15209 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15209step0 raw15209; decide +kernel
      have hl : raw15209step0Labels = raw15209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15209 raw15209Labels permutation346 hz
    mixedMoment B raw15209step0 raw15209step0Labels = mixedMoment B raw15209step1 raw15209step1Labels := by
      have ha : raw15209step1 = (fun i j => raw15209step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15209step1 raw15209step0; decide +kernel
      have hl : raw15209step1Labels = raw15209step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15209step0 raw15209step0Labels permutation146 permutation2
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw15210 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15210step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15210step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15210step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15210step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15210 raw15210Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw15210 raw15210Labels = mixedMoment B raw15210step0 raw15210step0Labels := by
      have hz : ∀ j, raw15210 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15210step0 = (fun i j => raw15210 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15210step0 raw15210; decide +kernel
      have hl : raw15210step0Labels = raw15210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15210 raw15210Labels permutation346 hz
    mixedMoment B raw15210step0 raw15210step0Labels = mixedMoment B raw15210step1 raw15210step1Labels := by
      have ha : raw15210step1 = (fun i j => raw15210step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15210step1 raw15210step0; decide +kernel
      have hl : raw15210step1Labels = raw15210step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15210step0 raw15210step0Labels permutation32 permutation6
    mixedMoment B raw15210step1 raw15210step1Labels = mixedMoment B raw15210step2 raw15210step2Labels := by
      have ha : raw15210step2 = raw15210step1 := by apply Matrix.ext; unfold raw15210step2 raw15210step1; decide +kernel
      have hl : raw15210step1Labels = labelEmbedding9 ∘ raw15210step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15210step1 raw15210step1Labels raw15210step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw15211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15211step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15211step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15211step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15211step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15211step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15211step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15211 raw15211Labels = mixedMoment B node5385 node5385Labels := by
  calc
    mixedMoment B raw15211 raw15211Labels = mixedMoment B raw15211step0 raw15211step0Labels := by
      have hz : ∀ j, raw15211 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15211step0 = (fun i j => raw15211 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15211step0 raw15211; decide +kernel
      have hl : raw15211step0Labels = raw15211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15211 raw15211Labels permutation346 hz
    mixedMoment B raw15211step0 raw15211step0Labels = mixedMoment B raw15211step1 raw15211step1Labels := by
      have ha : raw15211step1 = (fun i j => raw15211step0 (permutation90 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15211step1 raw15211step0; decide +kernel
      have hl : raw15211step1Labels = raw15211step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15211step0 raw15211step0Labels permutation90 permutation4
    mixedMoment B raw15211step1 raw15211step1Labels = mixedMoment B raw15211step2 raw15211step2Labels := by
      have ha : raw15211step2 = -raw15211step1 := by apply Matrix.ext; change ∀ i j, raw15211step2 i j = -(raw15211step1 i j); unfold raw15211step2 raw15211step1; decide +kernel
      have hl : raw15211step2Labels = raw15211step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15211step2 raw15211step2Labels = mixedMoment B raw15211step3 raw15211step3Labels := by
      have ha : raw15211step3 = raw15211step2 := by apply Matrix.ext; unfold raw15211step3 raw15211step2; decide +kernel
      have hl : raw15211step2Labels = labelEmbedding7 ∘ raw15211step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15211step2 raw15211step2Labels raw15211step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5385 node5385Labels := by rfl

def raw15212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15212step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15212step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15212step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15212step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15212 raw15212Labels = mixedMoment B node5414 node5414Labels := by
  calc
    mixedMoment B raw15212 raw15212Labels = mixedMoment B raw15212step0 raw15212step0Labels := by
      have ha : raw15212step0 = (fun i j => raw15212 (permutation458 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15212step0 raw15212; decide +kernel
      have hl : raw15212step0Labels = raw15212Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15212 raw15212Labels permutation458 permutation4
    mixedMoment B raw15212step0 raw15212step0Labels = mixedMoment B raw15212step1 raw15212step1Labels := by
      have ha : raw15212step1 = -raw15212step0 := by apply Matrix.ext; change ∀ i j, raw15212step1 i j = -(raw15212step0 i j); unfold raw15212step1 raw15212step0; decide +kernel
      have hl : raw15212step1Labels = raw15212step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15212step1 raw15212step1Labels = mixedMoment B raw15212step2 raw15212step2Labels := by
      have ha : raw15212step2 = raw15212step1 := by apply Matrix.ext; unfold raw15212step2 raw15212step1; decide +kernel
      have hl : raw15212step1Labels = labelEmbedding7 ∘ raw15212step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15212step1 raw15212step1Labels raw15212step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5414 node5414Labels := by rfl

def raw15213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15213step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15213step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15213step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15213step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15213step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15213step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15213 raw15213Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw15213 raw15213Labels = mixedMoment B raw15213step0 raw15213step0Labels := by
      have hz : ∀ j, raw15213 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15213step0 = (fun i j => raw15213 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15213step0 raw15213; decide +kernel
      have hl : raw15213step0Labels = raw15213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15213 raw15213Labels permutation346 hz
    mixedMoment B raw15213step0 raw15213step0Labels = mixedMoment B raw15213step1 raw15213step1Labels := by
      have ha : raw15213step1 = (fun i j => raw15213step0 (permutation90 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15213step1 raw15213step0; decide +kernel
      have hl : raw15213step1Labels = raw15213step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15213step0 raw15213step0Labels permutation90 permutation4
    mixedMoment B raw15213step1 raw15213step1Labels = mixedMoment B raw15213step2 raw15213step2Labels := by
      have ha : raw15213step2 = -raw15213step1 := by apply Matrix.ext; change ∀ i j, raw15213step2 i j = -(raw15213step1 i j); unfold raw15213step2 raw15213step1; decide +kernel
      have hl : raw15213step2Labels = raw15213step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15213step2 raw15213step2Labels = mixedMoment B raw15213step3 raw15213step3Labels := by
      have ha : raw15213step3 = raw15213step2 := by apply Matrix.ext; unfold raw15213step3 raw15213step2; decide +kernel
      have hl : raw15213step2Labels = labelEmbedding7 ∘ raw15213step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15213step2 raw15213step2Labels raw15213step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5164 node5164Labels := by rfl

def raw15214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw15214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw15214step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15214step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15214step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15214step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15214step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15214step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15214 raw15214Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw15214 raw15214Labels = mixedMoment B raw15214step0 raw15214step0Labels := by
      have hz : ∀ j, raw15214 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15214step0 = (fun i j => raw15214 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15214step0 raw15214; decide +kernel
      have hl : raw15214step0Labels = raw15214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15214 raw15214Labels permutation346 hz
    mixedMoment B raw15214step0 raw15214step0Labels = mixedMoment B raw15214step1 raw15214step1Labels := by
      have ha : raw15214step1 = (fun i j => raw15214step0 (permutation91 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15214step1 raw15214step0; decide +kernel
      have hl : raw15214step1Labels = raw15214step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15214step0 raw15214step0Labels permutation91 permutation4
    mixedMoment B raw15214step1 raw15214step1Labels = mixedMoment B raw15214step2 raw15214step2Labels := by
      have ha : raw15214step2 = -raw15214step1 := by apply Matrix.ext; change ∀ i j, raw15214step2 i j = -(raw15214step1 i j); unfold raw15214step2 raw15214step1; decide +kernel
      have hl : raw15214step2Labels = raw15214step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15214step2 raw15214step2Labels = mixedMoment B raw15214step3 raw15214step3Labels := by
      have ha : raw15214step3 = raw15214step2 := by apply Matrix.ext; unfold raw15214step3 raw15214step2; decide +kernel
      have hl : raw15214step2Labels = labelEmbedding7 ∘ raw15214step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15214step2 raw15214step2Labels raw15214step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw15215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw15215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw15215step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15215step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15215step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15215step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15215step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15215step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15215 raw15215Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw15215 raw15215Labels = mixedMoment B raw15215step0 raw15215step0Labels := by
      have hz : ∀ j, raw15215 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15215step0 = (fun i j => raw15215 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15215step0 raw15215; decide +kernel
      have hl : raw15215step0Labels = raw15215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15215 raw15215Labels permutation346 hz
    mixedMoment B raw15215step0 raw15215step0Labels = mixedMoment B raw15215step1 raw15215step1Labels := by
      have ha : raw15215step1 = (fun i j => raw15215step0 (permutation90 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15215step1 raw15215step0; decide +kernel
      have hl : raw15215step1Labels = raw15215step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15215step0 raw15215step0Labels permutation90 permutation4
    mixedMoment B raw15215step1 raw15215step1Labels = mixedMoment B raw15215step2 raw15215step2Labels := by
      have ha : raw15215step2 = -raw15215step1 := by apply Matrix.ext; change ∀ i j, raw15215step2 i j = -(raw15215step1 i j); unfold raw15215step2 raw15215step1; decide +kernel
      have hl : raw15215step2Labels = raw15215step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15215step2 raw15215step2Labels = mixedMoment B raw15215step3 raw15215step3Labels := by
      have ha : raw15215step3 = raw15215step2 := by apply Matrix.ext; unfold raw15215step3 raw15215step2; decide +kernel
      have hl : raw15215step2Labels = labelEmbedding7 ∘ raw15215step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15215step2 raw15215step2Labels raw15215step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw15216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15216step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15216step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15216step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15216 raw15216Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw15216 raw15216Labels = mixedMoment B raw15216step0 raw15216step0Labels := by
      have hz : ∀ j, raw15216 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15216step0 = (fun i j => raw15216 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15216step0 raw15216; decide +kernel
      have hl : raw15216step0Labels = raw15216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15216 raw15216Labels permutation346 hz
    mixedMoment B raw15216step0 raw15216step0Labels = mixedMoment B raw15216step1 raw15216step1Labels := by
      have hz : ∀ j, raw15216step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw15216step1 = (fun i j => raw15216step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw15216step1 raw15216step0; decide +kernel
      have hl : raw15216step1Labels = raw15216step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15216step0 raw15216step0Labels permutation56 hz
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw15217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15217step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15217step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15217step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15217step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15217 raw15217Labels = mixedMoment B node5375 node5375Labels := by
  calc
    mixedMoment B raw15217 raw15217Labels = mixedMoment B raw15217step0 raw15217step0Labels := by
      have ha : raw15217step0 = (fun i j => raw15217 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15217step0 raw15217; decide +kernel
      have hl : raw15217step0Labels = raw15217Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15217 raw15217Labels permutation271 permutation3
    mixedMoment B raw15217step0 raw15217step0Labels = mixedMoment B raw15217step1 raw15217step1Labels := by
      have ha : raw15217step1 = raw15217step0 := by apply Matrix.ext; unfold raw15217step1 raw15217step0; decide +kernel
      have hl : raw15217step0Labels = labelEmbedding6 ∘ raw15217step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15217step0 raw15217step0Labels raw15217step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5375 node5375Labels := by rfl

def raw15218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15218step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15218step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw15218step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15218step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw15218step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15218 raw15218Labels = mixedMoment B node5153 node5153Labels := by
  calc
    mixedMoment B raw15218 raw15218Labels = mixedMoment B raw15218step0 raw15218step0Labels := by
      have ha : raw15218step0 = (fun i j => raw15218 (permutation455 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15218step0 raw15218; decide +kernel
      have hl : raw15218step0Labels = raw15218Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15218 raw15218Labels permutation455 permutation4
    mixedMoment B raw15218step0 raw15218step0Labels = mixedMoment B raw15218step1 raw15218step1Labels := by
      have ha : raw15218step1 = -raw15218step0 := by apply Matrix.ext; change ∀ i j, raw15218step1 i j = -(raw15218step0 i j); unfold raw15218step1 raw15218step0; decide +kernel
      have hl : raw15218step1Labels = raw15218step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15218step1 raw15218step1Labels = mixedMoment B raw15218step2 raw15218step2Labels := by
      have ha : raw15218step2 = raw15218step1 := by apply Matrix.ext; unfold raw15218step2 raw15218step1; decide +kernel
      have hl : raw15218step1Labels = labelEmbedding7 ∘ raw15218step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15218step1 raw15218step1Labels raw15218step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5153 node5153Labels := by rfl

def raw15219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1]]
def raw15219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15219step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15219step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15219step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15219step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15219step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15219 raw15219Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw15219 raw15219Labels = mixedMoment B raw15219step0 raw15219step0Labels := by
      have ha : raw15219step0 = (fun i j => raw15219 (permutation225 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15219step0 raw15219; decide +kernel
      have hl : raw15219step0Labels = raw15219Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15219 raw15219Labels permutation225 permutation7
    mixedMoment B raw15219step0 raw15219step0Labels = mixedMoment B raw15219step1 raw15219step1Labels := by
      have ha : raw15219step1 = -raw15219step0 := by apply Matrix.ext; change ∀ i j, raw15219step1 i j = -(raw15219step0 i j); unfold raw15219step1 raw15219step0; decide +kernel
      have hl : raw15219step1Labels = raw15219step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15219step1 raw15219step1Labels = mixedMoment B raw15219step2 raw15219step2Labels := by
      have ha : raw15219step2 = raw15219step1 := by apply Matrix.ext; unfold raw15219step2 raw15219step1; decide +kernel
      have hl : raw15219step1Labels = labelEmbedding10 ∘ raw15219step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15219step1 raw15219step1Labels raw15219step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw15220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw15220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15220step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15220step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15220step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15220 raw15220Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw15220 raw15220Labels = mixedMoment B raw15220step0 raw15220step0Labels := by
      have ha : raw15220step0 = (fun i j => raw15220 (permutation509 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15220step0 raw15220; decide +kernel
      have hl : raw15220step0Labels = raw15220Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15220 raw15220Labels permutation509 permutation6
    mixedMoment B raw15220step0 raw15220step0Labels = mixedMoment B raw15220step1 raw15220step1Labels := by
      have ha : raw15220step1 = raw15220step0 := by apply Matrix.ext; unfold raw15220step1 raw15220step0; decide +kernel
      have hl : raw15220step0Labels = labelEmbedding9 ∘ raw15220step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15220step0 raw15220step0Labels raw15220step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw15221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15221step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15221step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15221 raw15221Labels = mixedMoment B node5385 node5385Labels := by
  calc
    mixedMoment B raw15221 raw15221Labels = mixedMoment B raw15221step0 raw15221step0Labels := by
      have hz : ∀ j, raw15221 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15221step0 = (fun i j => raw15221 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15221step0 raw15221; decide +kernel
      have hl : raw15221step0Labels = raw15221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15221 raw15221Labels permutation346 hz
    mixedMoment B raw15221step0 raw15221step0Labels = mixedMoment B raw15221step1 raw15221step1Labels := by
      have ha : raw15221step1 = (fun i j => raw15221step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15221step1 raw15221step0; decide +kernel
      have hl : raw15221step1Labels = raw15221step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15221step0 raw15221step0Labels permutation34 permutation2
    _ = mixedMoment B node5385 node5385Labels := by rfl

def raw15222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15222 raw15222Labels = mixedMoment B node5414 node5414Labels := by
  calc
    mixedMoment B raw15222 raw15222Labels = mixedMoment B raw15222step0 raw15222step0Labels := by
      have ha : raw15222step0 = (fun i j => raw15222 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15222step0 raw15222; decide +kernel
      have hl : raw15222step0Labels = raw15222Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15222 raw15222Labels permutation154 permutation2
    _ = mixedMoment B node5414 node5414Labels := by rfl

def raw15223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw15223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw15223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15223step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15223 raw15223Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw15223 raw15223Labels = mixedMoment B raw15223step0 raw15223step0Labels := by
      have hz : ∀ j, raw15223 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15223step0 = (fun i j => raw15223 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15223step0 raw15223; decide +kernel
      have hl : raw15223step0Labels = raw15223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15223 raw15223Labels permutation346 hz
    mixedMoment B raw15223step0 raw15223step0Labels = mixedMoment B raw15223step1 raw15223step1Labels := by
      have ha : raw15223step1 = (fun i j => raw15223step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15223step1 raw15223step0; decide +kernel
      have hl : raw15223step1Labels = raw15223step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15223step0 raw15223step0Labels permutation34 permutation2
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw15224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw15224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw15224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15224step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15224 raw15224Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw15224 raw15224Labels = mixedMoment B raw15224step0 raw15224step0Labels := by
      have hz : ∀ j, raw15224 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15224step0 = (fun i j => raw15224 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15224step0 raw15224; decide +kernel
      have hl : raw15224step0Labels = raw15224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15224 raw15224Labels permutation346 hz
    mixedMoment B raw15224step0 raw15224step0Labels = mixedMoment B raw15224step1 raw15224step1Labels := by
      have ha : raw15224step1 = (fun i j => raw15224step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15224step1 raw15224step0; decide +kernel
      have hl : raw15224step1Labels = raw15224step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15224step0 raw15224step0Labels permutation35 permutation2
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw15225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw15225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw15225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15225step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw15225step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15225step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw15225step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15225 raw15225Labels = mixedMoment B node5009 node5009Labels := by
  calc
    mixedMoment B raw15225 raw15225Labels = mixedMoment B raw15225step0 raw15225step0Labels := by
      have hz : ∀ j, raw15225 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15225step0 = (fun i j => raw15225 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15225step0 raw15225; decide +kernel
      have hl : raw15225step0Labels = raw15225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15225 raw15225Labels permutation346 hz
    mixedMoment B raw15225step0 raw15225step0Labels = mixedMoment B raw15225step1 raw15225step1Labels := by
      have ha : raw15225step1 = (fun i j => raw15225step0 (permutation123 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15225step1 raw15225step0; decide +kernel
      have hl : raw15225step1Labels = raw15225step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15225step0 raw15225step0Labels permutation123 permutation5
    mixedMoment B raw15225step1 raw15225step1Labels = mixedMoment B raw15225step2 raw15225step2Labels := by
      have ha : raw15225step2 = raw15225step1 := by apply Matrix.ext; unfold raw15225step2 raw15225step1; decide +kernel
      have hl : raw15225step1Labels = labelEmbedding8 ∘ raw15225step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15225step1 raw15225step1Labels raw15225step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5009 node5009Labels := by rfl

def raw15226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw15226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15226step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15226step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15226step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15226 raw15226Labels = mixedMoment B node5007 node5007Labels := by
  calc
    mixedMoment B raw15226 raw15226Labels = mixedMoment B raw15226step0 raw15226step0Labels := by
      have ha : raw15226step0 = (fun i j => raw15226 (permutation569 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15226step0 raw15226; decide +kernel
      have hl : raw15226step0Labels = raw15226Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15226 raw15226Labels permutation569 permutation5
    mixedMoment B raw15226step0 raw15226step0Labels = mixedMoment B raw15226step1 raw15226step1Labels := by
      have ha : raw15226step1 = raw15226step0 := by apply Matrix.ext; unfold raw15226step1 raw15226step0; decide +kernel
      have hl : raw15226step0Labels = labelEmbedding8 ∘ raw15226step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15226step0 raw15226step0Labels raw15226step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5007 node5007Labels := by rfl

def raw15227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 3, -2], ![2, -3, 1], ![2, -1, -1]]
def raw15227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 3, -2], ![2, -3, 1], ![2, -1, -1]]
def raw15227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw15227step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15227step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw15227step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15227 raw15227Labels = mixedMoment B node5008 node5008Labels := by
  calc
    mixedMoment B raw15227 raw15227Labels = mixedMoment B raw15227step0 raw15227step0Labels := by
      have hz : ∀ j, raw15227 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15227step0 = (fun i j => raw15227 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15227step0 raw15227; decide +kernel
      have hl : raw15227step0Labels = raw15227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15227 raw15227Labels permutation346 hz
    mixedMoment B raw15227step0 raw15227step0Labels = mixedMoment B raw15227step1 raw15227step1Labels := by
      have ha : raw15227step1 = (fun i j => raw15227step0 (permutation122 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15227step1 raw15227step0; decide +kernel
      have hl : raw15227step1Labels = raw15227step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15227step0 raw15227step0Labels permutation122 permutation5
    mixedMoment B raw15227step1 raw15227step1Labels = mixedMoment B raw15227step2 raw15227step2Labels := by
      have ha : raw15227step2 = raw15227step1 := by apply Matrix.ext; unfold raw15227step2 raw15227step1; decide +kernel
      have hl : raw15227step1Labels = labelEmbedding8 ∘ raw15227step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15227step1 raw15227step1Labels raw15227step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5008 node5008Labels := by rfl

def raw15228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw15228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw15228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15228step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15228step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15228step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15228 raw15228Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw15228 raw15228Labels = mixedMoment B raw15228step0 raw15228step0Labels := by
      have hz : ∀ j, raw15228 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15228step0 = (fun i j => raw15228 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15228step0 raw15228; decide +kernel
      have hl : raw15228step0Labels = raw15228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15228 raw15228Labels permutation346 hz
    mixedMoment B raw15228step0 raw15228step0Labels = mixedMoment B raw15228step1 raw15228step1Labels := by
      have ha : raw15228step1 = (fun i j => raw15228step0 (permutation122 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15228step1 raw15228step0; decide +kernel
      have hl : raw15228step1Labels = raw15228step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15228step0 raw15228step0Labels permutation122 permutation5
    mixedMoment B raw15228step1 raw15228step1Labels = mixedMoment B raw15228step2 raw15228step2Labels := by
      have ha : raw15228step2 = raw15228step1 := by apply Matrix.ext; unfold raw15228step2 raw15228step1; decide +kernel
      have hl : raw15228step1Labels = labelEmbedding8 ∘ raw15228step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15228step1 raw15228step1Labels raw15228step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw15229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw15229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw15229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw15229step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15229step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw15229step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15229step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw15229step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15229 raw15229Labels = mixedMoment B node5009 node5009Labels := by
  calc
    mixedMoment B raw15229 raw15229Labels = mixedMoment B raw15229step0 raw15229step0Labels := by
      have hz : ∀ j, raw15229 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15229step0 = (fun i j => raw15229 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15229step0 raw15229; decide +kernel
      have hl : raw15229step0Labels = raw15229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15229 raw15229Labels permutation346 hz
    mixedMoment B raw15229step0 raw15229step0Labels = mixedMoment B raw15229step1 raw15229step1Labels := by
      have ha : raw15229step1 = (fun i j => raw15229step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15229step1 raw15229step0; decide +kernel
      have hl : raw15229step1Labels = raw15229step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15229step0 raw15229step0Labels permutation150 permutation3
    mixedMoment B raw15229step1 raw15229step1Labels = mixedMoment B raw15229step2 raw15229step2Labels := by
      have ha : raw15229step2 = -raw15229step1 := by apply Matrix.ext; change ∀ i j, raw15229step2 i j = -(raw15229step1 i j); unfold raw15229step2 raw15229step1; decide +kernel
      have hl : raw15229step2Labels = raw15229step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15229step2 raw15229step2Labels = mixedMoment B raw15229step3 raw15229step3Labels := by
      have ha : raw15229step3 = raw15229step2 := by apply Matrix.ext; unfold raw15229step3 raw15229step2; decide +kernel
      have hl : raw15229step2Labels = labelEmbedding6 ∘ raw15229step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15229step2 raw15229step2Labels raw15229step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5009 node5009Labels := by rfl

def raw15230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw15230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15230step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15230step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15230step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15230step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15230step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15230 raw15230Labels = mixedMoment B node5007 node5007Labels := by
  calc
    mixedMoment B raw15230 raw15230Labels = mixedMoment B raw15230step0 raw15230step0Labels := by
      have ha : raw15230step0 = (fun i j => raw15230 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15230step0 raw15230; decide +kernel
      have hl : raw15230step0Labels = raw15230Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15230 raw15230Labels permutation686 permutation3
    mixedMoment B raw15230step0 raw15230step0Labels = mixedMoment B raw15230step1 raw15230step1Labels := by
      have ha : raw15230step1 = -raw15230step0 := by apply Matrix.ext; change ∀ i j, raw15230step1 i j = -(raw15230step0 i j); unfold raw15230step1 raw15230step0; decide +kernel
      have hl : raw15230step1Labels = raw15230step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15230step1 raw15230step1Labels = mixedMoment B raw15230step2 raw15230step2Labels := by
      have ha : raw15230step2 = raw15230step1 := by apply Matrix.ext; unfold raw15230step2 raw15230step1; decide +kernel
      have hl : raw15230step1Labels = labelEmbedding6 ∘ raw15230step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15230step1 raw15230step1Labels raw15230step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5007 node5007Labels := by rfl

def raw15231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def raw15231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def raw15231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw15231step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15231step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw15231step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15231step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw15231step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15231 raw15231Labels = mixedMoment B node5019 node5019Labels := by
  calc
    mixedMoment B raw15231 raw15231Labels = mixedMoment B raw15231step0 raw15231step0Labels := by
      have hz : ∀ j, raw15231 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15231step0 = (fun i j => raw15231 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15231step0 raw15231; decide +kernel
      have hl : raw15231step0Labels = raw15231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15231 raw15231Labels permutation346 hz
    mixedMoment B raw15231step0 raw15231step0Labels = mixedMoment B raw15231step1 raw15231step1Labels := by
      have ha : raw15231step1 = (fun i j => raw15231step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15231step1 raw15231step0; decide +kernel
      have hl : raw15231step1Labels = raw15231step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15231step0 raw15231step0Labels permutation149 permutation3
    mixedMoment B raw15231step1 raw15231step1Labels = mixedMoment B raw15231step2 raw15231step2Labels := by
      have ha : raw15231step2 = -raw15231step1 := by apply Matrix.ext; change ∀ i j, raw15231step2 i j = -(raw15231step1 i j); unfold raw15231step2 raw15231step1; decide +kernel
      have hl : raw15231step2Labels = raw15231step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15231step2 raw15231step2Labels = mixedMoment B raw15231step3 raw15231step3Labels := by
      have ha : raw15231step3 = raw15231step2 := by apply Matrix.ext; unfold raw15231step3 raw15231step2; decide +kernel
      have hl : raw15231step2Labels = labelEmbedding6 ∘ raw15231step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15231step2 raw15231step2Labels raw15231step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5019 node5019Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
