import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw30592 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30592Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30592step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30592step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30592step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30592step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30592 raw30592Labels = mixedMoment B node1997 node1997Labels := by
  calc
    mixedMoment B raw30592 raw30592Labels = mixedMoment B raw30592step0 raw30592step0Labels := by
      have ha : raw30592step0 = (fun i j => raw30592 (permutation201 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30592step0 raw30592; decide +kernel
      have hl : raw30592step0Labels = raw30592Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30592 raw30592Labels permutation201 permutation4
    mixedMoment B raw30592step0 raw30592step0Labels = mixedMoment B raw30592step1 raw30592step1Labels := by
      have ha : raw30592step1 = -raw30592step0 := by apply Matrix.ext; change ∀ i j, raw30592step1 i j = -(raw30592step0 i j); unfold raw30592step1 raw30592step0; decide +kernel
      have hl : raw30592step1Labels = raw30592step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1997 node1997Labels := by rfl

def raw30593 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30593Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw30593step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30593step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30593step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30593 raw30593Labels = mixedMoment B node1870 node1870Labels := by
  calc
    mixedMoment B raw30593 raw30593Labels = mixedMoment B raw30593step0 raw30593step0Labels := by
      have ha : raw30593step0 = (fun i j => raw30593 (permutation162 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30593step0 raw30593; decide +kernel
      have hl : raw30593step0Labels = raw30593Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30593 raw30593Labels permutation162 permutation4
    mixedMoment B raw30593step0 raw30593step0Labels = mixedMoment B raw30593step1 raw30593step1Labels := by
      have ha : raw30593step1 = -raw30593step0 := by apply Matrix.ext; change ∀ i j, raw30593step1 i j = -(raw30593step0 i j); unfold raw30593step1 raw30593step0; decide +kernel
      have hl : raw30593step1Labels = raw30593step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1870 node1870Labels := by rfl

def raw30594 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30594Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30594step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30594step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30594step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30594step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30594 raw30594Labels = mixedMoment B node1945 node1945Labels := by
  calc
    mixedMoment B raw30594 raw30594Labels = mixedMoment B raw30594step0 raw30594step0Labels := by
      have hz : ∀ j, raw30594 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30594step0 = (fun i j => raw30594 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30594step0 raw30594; decide +kernel
      have hl : raw30594step0Labels = raw30594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30594 raw30594Labels permutation434 hz
    mixedMoment B raw30594step0 raw30594step0Labels = mixedMoment B raw30594step1 raw30594step1Labels := by
      have ha : raw30594step1 = (fun i j => raw30594step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30594step1 raw30594step0; decide +kernel
      have hl : raw30594step1Labels = raw30594step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30594step0 raw30594step0Labels permutation33 permutation4
    mixedMoment B raw30594step1 raw30594step1Labels = mixedMoment B raw30594step2 raw30594step2Labels := by
      have ha : raw30594step2 = -raw30594step1 := by apply Matrix.ext; change ∀ i j, raw30594step2 i j = -(raw30594step1 i j); unfold raw30594step2 raw30594step1; decide +kernel
      have hl : raw30594step2Labels = raw30594step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1945 node1945Labels := by rfl

def raw30595 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw30595Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw30595step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30595step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw30595step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30595 raw30595Labels = mixedMoment B node1863 node1863Labels := by
  calc
    mixedMoment B raw30595 raw30595Labels = mixedMoment B raw30595step0 raw30595step0Labels := by
      have ha : raw30595step0 = (fun i j => raw30595 (permutation159 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30595step0 raw30595; decide +kernel
      have hl : raw30595step0Labels = raw30595Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30595 raw30595Labels permutation159 permutation4
    mixedMoment B raw30595step0 raw30595step0Labels = mixedMoment B raw30595step1 raw30595step1Labels := by
      have ha : raw30595step1 = -raw30595step0 := by apply Matrix.ext; change ∀ i j, raw30595step1 i j = -(raw30595step0 i j); unfold raw30595step1 raw30595step0; decide +kernel
      have hl : raw30595step1Labels = raw30595step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1863 node1863Labels := by rfl

def raw30596 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30596Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw30596step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30596step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30596step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30596 raw30596Labels = mixedMoment B node1865 node1865Labels := by
  calc
    mixedMoment B raw30596 raw30596Labels = mixedMoment B raw30596step0 raw30596step0Labels := by
      have ha : raw30596step0 = (fun i j => raw30596 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30596step0 raw30596; decide +kernel
      have hl : raw30596step0Labels = raw30596Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30596 raw30596Labels permutation158 permutation4
    mixedMoment B raw30596step0 raw30596step0Labels = mixedMoment B raw30596step1 raw30596step1Labels := by
      have ha : raw30596step1 = -raw30596step0 := by apply Matrix.ext; change ∀ i j, raw30596step1 i j = -(raw30596step0 i j); unfold raw30596step1 raw30596step0; decide +kernel
      have hl : raw30596step1Labels = raw30596step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1865 node1865Labels := by rfl

def raw30597 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30597Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw30597step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30597step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30597step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30597 raw30597Labels = mixedMoment B node3332 node3332Labels := by
  calc
    mixedMoment B raw30597 raw30597Labels = mixedMoment B raw30597step0 raw30597step0Labels := by
      have ha : raw30597step0 = (fun i j => raw30597 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30597step0 raw30597; decide +kernel
      have hl : raw30597step0Labels = raw30597Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30597 raw30597Labels permutation158 permutation4
    mixedMoment B raw30597step0 raw30597step0Labels = mixedMoment B raw30597step1 raw30597step1Labels := by
      have ha : raw30597step1 = -raw30597step0 := by apply Matrix.ext; change ∀ i j, raw30597step1 i j = -(raw30597step0 i j); unfold raw30597step1 raw30597step0; decide +kernel
      have hl : raw30597step1Labels = raw30597step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3332 node3332Labels := by rfl

def raw30598 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30598Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30598step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw30598step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30598step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30598 raw30598Labels = mixedMoment B node3439 node3439Labels := by
  calc
    mixedMoment B raw30598 raw30598Labels = mixedMoment B raw30598step0 raw30598step0Labels := by
      have hz : ∀ j, raw30598 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30598step0 = (fun i j => raw30598 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30598step0 raw30598; decide +kernel
      have hl : raw30598step0Labels = raw30598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30598 raw30598Labels permutation346 hz
    mixedMoment B raw30598step0 raw30598step0Labels = mixedMoment B raw30598step1 raw30598step1Labels := by
      have ha : raw30598step1 = (fun i j => raw30598step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30598step1 raw30598step0; decide +kernel
      have hl : raw30598step1Labels = raw30598step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30598step0 raw30598step0Labels permutation32 permutation4
    mixedMoment B raw30598step1 raw30598step1Labels = mixedMoment B raw30598step2 raw30598step2Labels := by
      have ha : raw30598step2 = -raw30598step1 := by apply Matrix.ext; change ∀ i j, raw30598step2 i j = -(raw30598step1 i j); unfold raw30598step2 raw30598step1; decide +kernel
      have hl : raw30598step2Labels = raw30598step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3439 node3439Labels := by rfl

def raw30599 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30599Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw30599step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30599step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30599step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30599 raw30599Labels = mixedMoment B node3362 node3362Labels := by
  calc
    mixedMoment B raw30599 raw30599Labels = mixedMoment B raw30599step0 raw30599step0Labels := by
      have ha : raw30599step0 = (fun i j => raw30599 (permutation200 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30599step0 raw30599; decide +kernel
      have hl : raw30599step0Labels = raw30599Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30599 raw30599Labels permutation200 permutation4
    mixedMoment B raw30599step0 raw30599step0Labels = mixedMoment B raw30599step1 raw30599step1Labels := by
      have ha : raw30599step1 = -raw30599step0 := by apply Matrix.ext; change ∀ i j, raw30599step1 i j = -(raw30599step0 i j); unfold raw30599step1 raw30599step0; decide +kernel
      have hl : raw30599step1Labels = raw30599step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3362 node3362Labels := by rfl

def raw30600 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw30600Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30600step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30600step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30600step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30600 raw30600Labels = mixedMoment B node3433 node3433Labels := by
  calc
    mixedMoment B raw30600 raw30600Labels = mixedMoment B raw30600step0 raw30600step0Labels := by
      have ha : raw30600step0 = (fun i j => raw30600 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30600step0 raw30600; decide +kernel
      have hl : raw30600step0Labels = raw30600Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30600 raw30600Labels permutation158 permutation4
    mixedMoment B raw30600step0 raw30600step0Labels = mixedMoment B raw30600step1 raw30600step1Labels := by
      have ha : raw30600step1 = -raw30600step0 := by apply Matrix.ext; change ∀ i j, raw30600step1 i j = -(raw30600step0 i j); unfold raw30600step1 raw30600step0; decide +kernel
      have hl : raw30600step1Labels = raw30600step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3433 node3433Labels := by rfl

def raw30601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30601step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw30601step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30601step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30601step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30601step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30601step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30601 raw30601Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw30601 raw30601Labels = mixedMoment B raw30601step0 raw30601step0Labels := by
      have hz : ∀ j, raw30601 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30601step0 = (fun i j => raw30601 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30601step0 raw30601; decide +kernel
      have hl : raw30601step0Labels = raw30601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30601 raw30601Labels permutation434 hz
    mixedMoment B raw30601step0 raw30601step0Labels = mixedMoment B raw30601step1 raw30601step1Labels := by
      have hz : ∀ j, raw30601step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30601step1 = (fun i j => raw30601step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30601step1 raw30601step0; decide +kernel
      have hl : raw30601step1Labels = raw30601step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30601step0 raw30601step0Labels permutation80 hz
    mixedMoment B raw30601step1 raw30601step1Labels = mixedMoment B raw30601step2 raw30601step2Labels := by
      have ha : raw30601step2 = (fun i j => raw30601step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30601step2 raw30601step1; decide +kernel
      have hl : raw30601step2Labels = raw30601step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30601step1 raw30601step1Labels permutation25 permutation7
    mixedMoment B raw30601step2 raw30601step2Labels = mixedMoment B raw30601step3 raw30601step3Labels := by
      have ha : raw30601step3 = raw30601step2 := by apply Matrix.ext; unfold raw30601step3 raw30601step2; decide +kernel
      have hl : raw30601step2Labels = labelEmbedding10 ∘ raw30601step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30601step2 raw30601step2Labels raw30601step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

def raw30602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30602step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30602step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30602step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30602 raw30602Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw30602 raw30602Labels = mixedMoment B raw30602step0 raw30602step0Labels := by
      have hz : ∀ j, raw30602 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30602step0 = (fun i j => raw30602 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30602step0 raw30602; decide +kernel
      have hl : raw30602step0Labels = raw30602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30602 raw30602Labels permutation434 hz
    mixedMoment B raw30602step0 raw30602step0Labels = mixedMoment B raw30602step1 raw30602step1Labels := by
      have ha : raw30602step1 = (fun i j => raw30602step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30602step1 raw30602step0; decide +kernel
      have hl : raw30602step1Labels = raw30602step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30602step0 raw30602step0Labels permutation127 permutation7
    mixedMoment B raw30602step1 raw30602step1Labels = mixedMoment B raw30602step2 raw30602step2Labels := by
      have ha : raw30602step2 = raw30602step1 := by apply Matrix.ext; unfold raw30602step2 raw30602step1; decide +kernel
      have hl : raw30602step1Labels = labelEmbedding10 ∘ raw30602step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30602step1 raw30602step1Labels raw30602step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw30603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30603step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30603step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30603step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30603step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30603 raw30603Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw30603 raw30603Labels = mixedMoment B raw30603step0 raw30603step0Labels := by
      have hz : ∀ j, raw30603 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30603step0 = (fun i j => raw30603 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30603step0 raw30603; decide +kernel
      have hl : raw30603step0Labels = raw30603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30603 raw30603Labels permutation346 hz
    mixedMoment B raw30603step0 raw30603step0Labels = mixedMoment B raw30603step1 raw30603step1Labels := by
      have ha : raw30603step1 = (fun i j => raw30603step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30603step1 raw30603step0; decide +kernel
      have hl : raw30603step1Labels = raw30603step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30603step0 raw30603step0Labels permutation127 permutation7
    mixedMoment B raw30603step1 raw30603step1Labels = mixedMoment B raw30603step2 raw30603step2Labels := by
      have ha : raw30603step2 = raw30603step1 := by apply Matrix.ext; unfold raw30603step2 raw30603step1; decide +kernel
      have hl : raw30603step1Labels = labelEmbedding10 ∘ raw30603step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30603step1 raw30603step1Labels raw30603step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw30604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw30604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw30604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30604step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![2, 1, -3], ![1, -1, 0]]
def raw30604step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30604step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30604step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30604step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30604step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30604 raw30604Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw30604 raw30604Labels = mixedMoment B raw30604step0 raw30604step0Labels := by
      have hz : ∀ j, raw30604 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30604step0 = (fun i j => raw30604 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30604step0 raw30604; decide +kernel
      have hl : raw30604step0Labels = raw30604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30604 raw30604Labels permutation434 hz
    mixedMoment B raw30604step0 raw30604step0Labels = mixedMoment B raw30604step1 raw30604step1Labels := by
      have hz : ∀ j, raw30604step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30604step1 = (fun i j => raw30604step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30604step1 raw30604step0; decide +kernel
      have hl : raw30604step1Labels = raw30604step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30604step0 raw30604step0Labels permutation80 hz
    mixedMoment B raw30604step1 raw30604step1Labels = mixedMoment B raw30604step2 raw30604step2Labels := by
      have ha : raw30604step2 = (fun i j => raw30604step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30604step2 raw30604step1; decide +kernel
      have hl : raw30604step2Labels = raw30604step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30604step1 raw30604step1Labels permutation25 permutation7
    mixedMoment B raw30604step2 raw30604step2Labels = mixedMoment B raw30604step3 raw30604step3Labels := by
      have ha : raw30604step3 = raw30604step2 := by apply Matrix.ext; unfold raw30604step3 raw30604step2; decide +kernel
      have hl : raw30604step2Labels = labelEmbedding10 ∘ raw30604step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30604step2 raw30604step2Labels raw30604step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw30605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw30605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw30605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw30605step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30605 raw30605Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw30605 raw30605Labels = mixedMoment B raw30605step0 raw30605step0Labels := by
      have hz : ∀ j, raw30605 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30605step0 = (fun i j => raw30605 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30605step0 raw30605; decide +kernel
      have hl : raw30605step0Labels = raw30605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30605 raw30605Labels permutation434 hz
    mixedMoment B raw30605step0 raw30605step0Labels = mixedMoment B raw30605step1 raw30605step1Labels := by
      have hz : ∀ j, raw30605step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30605step1 = (fun i j => raw30605step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30605step1 raw30605step0; decide +kernel
      have hl : raw30605step1Labels = raw30605step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30605step0 raw30605step0Labels permutation80 hz
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw30606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw30606step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30606 raw30606Labels = mixedMoment B node4548 node4548Labels := by
  calc
    mixedMoment B raw30606 raw30606Labels = mixedMoment B raw30606step0 raw30606step0Labels := by
      have hz : ∀ j, raw30606 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30606step0 = (fun i j => raw30606 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30606step0 raw30606; decide +kernel
      have hl : raw30606step0Labels = raw30606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30606 raw30606Labels permutation434 hz
    mixedMoment B raw30606step0 raw30606step0Labels = mixedMoment B raw30606step1 raw30606step1Labels := by
      have ha : raw30606step1 = (fun i j => raw30606step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30606step1 raw30606step0; decide +kernel
      have hl : raw30606step1Labels = raw30606step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30606step0 raw30606step0Labels permutation33 permutation2
    _ = mixedMoment B node4548 node4548Labels := by rfl

def raw30607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw30607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30607 raw30607Labels = mixedMoment B node4945 node4945Labels := by
  calc
    mixedMoment B raw30607 raw30607Labels = mixedMoment B raw30607step0 raw30607step0Labels := by
      have hz : ∀ j, raw30607 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30607step0 = (fun i j => raw30607 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30607step0 raw30607; decide +kernel
      have hl : raw30607step0Labels = raw30607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30607 raw30607Labels permutation434 hz
    mixedMoment B raw30607step0 raw30607step0Labels = mixedMoment B raw30607step1 raw30607step1Labels := by
      have ha : raw30607step1 = (fun i j => raw30607step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30607step1 raw30607step0; decide +kernel
      have hl : raw30607step1Labels = raw30607step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30607step0 raw30607step0Labels permutation33 permutation2
    _ = mixedMoment B node4945 node4945Labels := by rfl

def raw30608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw30608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30608 raw30608Labels = mixedMoment B node5035 node5035Labels := by
  calc
    mixedMoment B raw30608 raw30608Labels = mixedMoment B raw30608step0 raw30608step0Labels := by
      have ha : raw30608step0 = (fun i j => raw30608 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30608step0 raw30608; decide +kernel
      have hl : raw30608step0Labels = raw30608Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30608 raw30608Labels permutation159 permutation2
    _ = mixedMoment B node5035 node5035Labels := by rfl

def raw30609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw30609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw30609step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw30609step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30609 raw30609Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw30609 raw30609Labels = mixedMoment B raw30609step0 raw30609step0Labels := by
      have hz : ∀ j, raw30609 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30609step0 = (fun i j => raw30609 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30609step0 raw30609; decide +kernel
      have hl : raw30609step0Labels = raw30609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30609 raw30609Labels permutation434 hz
    mixedMoment B raw30609step0 raw30609step0Labels = mixedMoment B raw30609step1 raw30609step1Labels := by
      have ha : raw30609step1 = (fun i j => raw30609step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30609step1 raw30609step0; decide +kernel
      have hl : raw30609step1Labels = raw30609step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30609step0 raw30609step0Labels permutation33 permutation2
    _ = mixedMoment B node5099 node5099Labels := by rfl

def raw30610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30610step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw30610step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30610 raw30610Labels = mixedMoment B node4548 node4548Labels := by
  calc
    mixedMoment B raw30610 raw30610Labels = mixedMoment B raw30610step0 raw30610step0Labels := by
      have hz : ∀ j, raw30610 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30610step0 = (fun i j => raw30610 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30610step0 raw30610; decide +kernel
      have hl : raw30610step0Labels = raw30610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30610 raw30610Labels permutation346 hz
    mixedMoment B raw30610step0 raw30610step0Labels = mixedMoment B raw30610step1 raw30610step1Labels := by
      have ha : raw30610step1 = (fun i j => raw30610step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30610step1 raw30610step0; decide +kernel
      have hl : raw30610step1Labels = raw30610step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30610step0 raw30610step0Labels permutation33 permutation2
    _ = mixedMoment B node4548 node4548Labels := by rfl

def raw30611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw30611step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30611 raw30611Labels = mixedMoment B node4945 node4945Labels := by
  calc
    mixedMoment B raw30611 raw30611Labels = mixedMoment B raw30611step0 raw30611step0Labels := by
      have hz : ∀ j, raw30611 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30611step0 = (fun i j => raw30611 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30611step0 raw30611; decide +kernel
      have hl : raw30611step0Labels = raw30611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30611 raw30611Labels permutation346 hz
    mixedMoment B raw30611step0 raw30611step0Labels = mixedMoment B raw30611step1 raw30611step1Labels := by
      have ha : raw30611step1 = (fun i j => raw30611step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30611step1 raw30611step0; decide +kernel
      have hl : raw30611step1Labels = raw30611step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30611step0 raw30611step0Labels permutation33 permutation2
    _ = mixedMoment B node4945 node4945Labels := by rfl

def raw30612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw30612step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30612 raw30612Labels = mixedMoment B node5035 node5035Labels := by
  calc
    mixedMoment B raw30612 raw30612Labels = mixedMoment B raw30612step0 raw30612step0Labels := by
      have ha : raw30612step0 = (fun i j => raw30612 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30612step0 raw30612; decide +kernel
      have hl : raw30612step0Labels = raw30612Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30612 raw30612Labels permutation153 permutation2
    _ = mixedMoment B node5035 node5035Labels := by rfl

def raw30613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw30613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw30613step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw30613step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30613 raw30613Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw30613 raw30613Labels = mixedMoment B raw30613step0 raw30613step0Labels := by
      have hz : ∀ j, raw30613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30613step0 = (fun i j => raw30613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30613step0 raw30613; decide +kernel
      have hl : raw30613step0Labels = raw30613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30613 raw30613Labels permutation346 hz
    mixedMoment B raw30613step0 raw30613step0Labels = mixedMoment B raw30613step1 raw30613step1Labels := by
      have ha : raw30613step1 = (fun i j => raw30613step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30613step1 raw30613step0; decide +kernel
      have hl : raw30613step1Labels = raw30613step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30613step0 raw30613step0Labels permutation33 permutation2
    _ = mixedMoment B node5099 node5099Labels := by rfl

def raw30614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30614step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30614step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![3, 0, -3], ![2, -2, 0]]
def raw30614step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30614step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw30614step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30614 raw30614Labels = mixedMoment B node4557 node4557Labels := by
  calc
    mixedMoment B raw30614 raw30614Labels = mixedMoment B raw30614step0 raw30614step0Labels := by
      have hz : ∀ j, raw30614 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30614step0 = (fun i j => raw30614 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30614step0 raw30614; decide +kernel
      have hl : raw30614step0Labels = raw30614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30614 raw30614Labels permutation434 hz
    mixedMoment B raw30614step0 raw30614step0Labels = mixedMoment B raw30614step1 raw30614step1Labels := by
      have hz : ∀ j, raw30614step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30614step1 = (fun i j => raw30614step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30614step1 raw30614step0; decide +kernel
      have hl : raw30614step1Labels = raw30614step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30614step0 raw30614step0Labels permutation80 hz
    mixedMoment B raw30614step1 raw30614step1Labels = mixedMoment B raw30614step2 raw30614step2Labels := by
      have ha : raw30614step2 = (fun i j => raw30614step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30614step2 raw30614step1; decide +kernel
      have hl : raw30614step2Labels = raw30614step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30614step1 raw30614step1Labels permutation9 permutation2
    _ = mixedMoment B node4557 node4557Labels := by rfl

def raw30615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![3, 0, -3], ![2, -2, 0]]
def raw30615step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30615step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw30615step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30615step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw30615step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30615 raw30615Labels = mixedMoment B node4692 node4692Labels := by
  calc
    mixedMoment B raw30615 raw30615Labels = mixedMoment B raw30615step0 raw30615step0Labels := by
      have hz : ∀ j, raw30615 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30615step0 = (fun i j => raw30615 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30615step0 raw30615; decide +kernel
      have hl : raw30615step0Labels = raw30615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30615 raw30615Labels permutation434 hz
    mixedMoment B raw30615step0 raw30615step0Labels = mixedMoment B raw30615step1 raw30615step1Labels := by
      have hz : ∀ j, raw30615step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30615step1 = (fun i j => raw30615step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30615step1 raw30615step0; decide +kernel
      have hl : raw30615step1Labels = raw30615step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30615step0 raw30615step0Labels permutation80 hz
    mixedMoment B raw30615step1 raw30615step1Labels = mixedMoment B raw30615step2 raw30615step2Labels := by
      have ha : raw30615step2 = (fun i j => raw30615step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30615step2 raw30615step1; decide +kernel
      have hl : raw30615step2Labels = raw30615step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30615step1 raw30615step1Labels permutation25 permutation2
    mixedMoment B raw30615step2 raw30615step2Labels = mixedMoment B raw30615step3 raw30615step3Labels := by
      have ha : raw30615step3 = -raw30615step2 := by apply Matrix.ext; change ∀ i j, raw30615step3 i j = -(raw30615step2 i j); unfold raw30615step3 raw30615step2; decide +kernel
      have hl : raw30615step3Labels = raw30615step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4692 node4692Labels := by rfl

def raw30616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30616step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30616step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30616step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30616step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30616 raw30616Labels = mixedMoment B node4681 node4681Labels := by
  calc
    mixedMoment B raw30616 raw30616Labels = mixedMoment B raw30616step0 raw30616step0Labels := by
      have hz : ∀ j, raw30616 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30616step0 = (fun i j => raw30616 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30616step0 raw30616; decide +kernel
      have hl : raw30616step0Labels = raw30616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30616 raw30616Labels permutation434 hz
    mixedMoment B raw30616step0 raw30616step0Labels = mixedMoment B raw30616step1 raw30616step1Labels := by
      have ha : raw30616step1 = (fun i j => raw30616step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30616step1 raw30616step0; decide +kernel
      have hl : raw30616step1Labels = raw30616step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30616step0 raw30616step0Labels permutation127 permutation2
    mixedMoment B raw30616step1 raw30616step1Labels = mixedMoment B raw30616step2 raw30616step2Labels := by
      have ha : raw30616step2 = -raw30616step1 := by apply Matrix.ext; change ∀ i j, raw30616step2 i j = -(raw30616step1 i j); unfold raw30616step2 raw30616step1; decide +kernel
      have hl : raw30616step2Labels = raw30616step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4681 node4681Labels := by rfl

def raw30617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30617step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30617step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30617step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30617 raw30617Labels = mixedMoment B node4681 node4681Labels := by
  calc
    mixedMoment B raw30617 raw30617Labels = mixedMoment B raw30617step0 raw30617step0Labels := by
      have hz : ∀ j, raw30617 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30617step0 = (fun i j => raw30617 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30617step0 raw30617; decide +kernel
      have hl : raw30617step0Labels = raw30617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30617 raw30617Labels permutation346 hz
    mixedMoment B raw30617step0 raw30617step0Labels = mixedMoment B raw30617step1 raw30617step1Labels := by
      have ha : raw30617step1 = (fun i j => raw30617step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30617step1 raw30617step0; decide +kernel
      have hl : raw30617step1Labels = raw30617step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30617step0 raw30617step0Labels permutation127 permutation2
    mixedMoment B raw30617step1 raw30617step1Labels = mixedMoment B raw30617step2 raw30617step2Labels := by
      have ha : raw30617step2 = -raw30617step1 := by apply Matrix.ext; change ∀ i j, raw30617step2 i j = -(raw30617step1 i j); unfold raw30617step2 raw30617step1; decide +kernel
      have hl : raw30617step2Labels = raw30617step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4681 node4681Labels := by rfl

def raw30618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw30618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw30618step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![3, 0, -3], ![1, -1, 0]]
def raw30618step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30618step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30618step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30618step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30618step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30618 raw30618Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw30618 raw30618Labels = mixedMoment B raw30618step0 raw30618step0Labels := by
      have hz : ∀ j, raw30618 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30618step0 = (fun i j => raw30618 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30618step0 raw30618; decide +kernel
      have hl : raw30618step0Labels = raw30618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30618 raw30618Labels permutation434 hz
    mixedMoment B raw30618step0 raw30618step0Labels = mixedMoment B raw30618step1 raw30618step1Labels := by
      have hz : ∀ j, raw30618step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30618step1 = (fun i j => raw30618step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30618step1 raw30618step0; decide +kernel
      have hl : raw30618step1Labels = raw30618step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30618step0 raw30618step0Labels permutation80 hz
    mixedMoment B raw30618step1 raw30618step1Labels = mixedMoment B raw30618step2 raw30618step2Labels := by
      have ha : raw30618step2 = (fun i j => raw30618step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30618step2 raw30618step1; decide +kernel
      have hl : raw30618step2Labels = raw30618step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30618step1 raw30618step1Labels permutation25 permutation2
    mixedMoment B raw30618step2 raw30618step2Labels = mixedMoment B raw30618step3 raw30618step3Labels := by
      have ha : raw30618step3 = -raw30618step2 := by apply Matrix.ext; change ∀ i j, raw30618step3 i j = -(raw30618step2 i j); unfold raw30618step3 raw30618step2; decide +kernel
      have hl : raw30618step3Labels = raw30618step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4841 node4841Labels := by rfl

def raw30619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30619step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw30619step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30619 raw30619Labels = mixedMoment B node4560 node4560Labels := by
  calc
    mixedMoment B raw30619 raw30619Labels = mixedMoment B raw30619step0 raw30619step0Labels := by
      have hz : ∀ j, raw30619 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30619step0 = (fun i j => raw30619 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30619step0 raw30619; decide +kernel
      have hl : raw30619step0Labels = raw30619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30619 raw30619Labels permutation434 hz
    mixedMoment B raw30619step0 raw30619step0Labels = mixedMoment B raw30619step1 raw30619step1Labels := by
      have hz : ∀ j, raw30619step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30619step1 = (fun i j => raw30619step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30619step1 raw30619step0; decide +kernel
      have hl : raw30619step1Labels = raw30619step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30619step0 raw30619step0Labels permutation80 hz
    _ = mixedMoment B node4560 node4560Labels := by rfl

def raw30620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30620step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 1, -3], ![3, -3, 0]]
def raw30620step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30620step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw30620step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30620step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30620step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30620step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30620step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30620 raw30620Labels = mixedMoment B node4705 node4705Labels := by
  calc
    mixedMoment B raw30620 raw30620Labels = mixedMoment B raw30620step0 raw30620step0Labels := by
      have hz : ∀ j, raw30620 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30620step0 = (fun i j => raw30620 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30620step0 raw30620; decide +kernel
      have hl : raw30620step0Labels = raw30620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30620 raw30620Labels permutation434 hz
    mixedMoment B raw30620step0 raw30620step0Labels = mixedMoment B raw30620step1 raw30620step1Labels := by
      have hz : ∀ j, raw30620step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30620step1 = (fun i j => raw30620step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30620step1 raw30620step0; decide +kernel
      have hl : raw30620step1Labels = raw30620step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30620step0 raw30620step0Labels permutation80 hz
    mixedMoment B raw30620step1 raw30620step1Labels = mixedMoment B raw30620step2 raw30620step2Labels := by
      have ha : raw30620step2 = (fun i j => raw30620step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30620step2 raw30620step1; decide +kernel
      have hl : raw30620step2Labels = raw30620step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30620step1 raw30620step1Labels permutation31 permutation3
    mixedMoment B raw30620step2 raw30620step2Labels = mixedMoment B raw30620step3 raw30620step3Labels := by
      have ha : raw30620step3 = -raw30620step2 := by apply Matrix.ext; change ∀ i j, raw30620step3 i j = -(raw30620step2 i j); unfold raw30620step3 raw30620step2; decide +kernel
      have hl : raw30620step3Labels = raw30620step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30620step3 raw30620step3Labels = mixedMoment B raw30620step4 raw30620step4Labels := by
      have ha : raw30620step4 = raw30620step3 := by apply Matrix.ext; unfold raw30620step4 raw30620step3; decide +kernel
      have hl : raw30620step3Labels = labelEmbedding6 ∘ raw30620step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30620step3 raw30620step3Labels raw30620step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4705 node4705Labels := by rfl

def raw30621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw30621step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30621step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30621step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30621step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30621 raw30621Labels = mixedMoment B node4699 node4699Labels := by
  calc
    mixedMoment B raw30621 raw30621Labels = mixedMoment B raw30621step0 raw30621step0Labels := by
      have hz : ∀ j, raw30621 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30621step0 = (fun i j => raw30621 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30621step0 raw30621; decide +kernel
      have hl : raw30621step0Labels = raw30621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30621 raw30621Labels permutation434 hz
    mixedMoment B raw30621step0 raw30621step0Labels = mixedMoment B raw30621step1 raw30621step1Labels := by
      have ha : raw30621step1 = (fun i j => raw30621step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30621step1 raw30621step0; decide +kernel
      have hl : raw30621step1Labels = raw30621step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30621step0 raw30621step0Labels permutation149 permutation3
    mixedMoment B raw30621step1 raw30621step1Labels = mixedMoment B raw30621step2 raw30621step2Labels := by
      have ha : raw30621step2 = -raw30621step1 := by apply Matrix.ext; change ∀ i j, raw30621step2 i j = -(raw30621step1 i j); unfold raw30621step2 raw30621step1; decide +kernel
      have hl : raw30621step2Labels = raw30621step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30621step2 raw30621step2Labels = mixedMoment B raw30621step3 raw30621step3Labels := by
      have ha : raw30621step3 = raw30621step2 := by apply Matrix.ext; unfold raw30621step3 raw30621step2; decide +kernel
      have hl : raw30621step2Labels = labelEmbedding6 ∘ raw30621step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30621step2 raw30621step2Labels raw30621step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4699 node4699Labels := by rfl

def raw30622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30622step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw30622step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30622step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30622step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30622step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30622 raw30622Labels = mixedMoment B node4699 node4699Labels := by
  calc
    mixedMoment B raw30622 raw30622Labels = mixedMoment B raw30622step0 raw30622step0Labels := by
      have hz : ∀ j, raw30622 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30622step0 = (fun i j => raw30622 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30622step0 raw30622; decide +kernel
      have hl : raw30622step0Labels = raw30622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30622 raw30622Labels permutation346 hz
    mixedMoment B raw30622step0 raw30622step0Labels = mixedMoment B raw30622step1 raw30622step1Labels := by
      have ha : raw30622step1 = (fun i j => raw30622step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30622step1 raw30622step0; decide +kernel
      have hl : raw30622step1Labels = raw30622step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30622step0 raw30622step0Labels permutation149 permutation3
    mixedMoment B raw30622step1 raw30622step1Labels = mixedMoment B raw30622step2 raw30622step2Labels := by
      have ha : raw30622step2 = -raw30622step1 := by apply Matrix.ext; change ∀ i j, raw30622step2 i j = -(raw30622step1 i j); unfold raw30622step2 raw30622step1; decide +kernel
      have hl : raw30622step2Labels = raw30622step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30622step2 raw30622step2Labels = mixedMoment B raw30622step3 raw30622step3Labels := by
      have ha : raw30622step3 = raw30622step2 := by apply Matrix.ext; unfold raw30622step3 raw30622step2; decide +kernel
      have hl : raw30622step2Labels = labelEmbedding6 ∘ raw30622step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30622step2 raw30622step2Labels raw30622step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4699 node4699Labels := by rfl

def raw30623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30623Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30623step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30623step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw30623step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30623step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30623step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30623step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30623step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30623 raw30623Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw30623 raw30623Labels = mixedMoment B raw30623step0 raw30623step0Labels := by
      have hz : ∀ j, raw30623 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30623step0 = (fun i j => raw30623 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30623step0 raw30623; decide +kernel
      have hl : raw30623step0Labels = raw30623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30623 raw30623Labels permutation434 hz
    mixedMoment B raw30623step0 raw30623step0Labels = mixedMoment B raw30623step1 raw30623step1Labels := by
      have hz : ∀ j, raw30623step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30623step1 = (fun i j => raw30623step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30623step1 raw30623step0; decide +kernel
      have hl : raw30623step1Labels = raw30623step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30623step0 raw30623step0Labels permutation80 hz
    mixedMoment B raw30623step1 raw30623step1Labels = mixedMoment B raw30623step2 raw30623step2Labels := by
      have ha : raw30623step2 = (fun i j => raw30623step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30623step2 raw30623step1; decide +kernel
      have hl : raw30623step2Labels = raw30623step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30623step1 raw30623step1Labels permutation25 permutation7
    mixedMoment B raw30623step2 raw30623step2Labels = mixedMoment B raw30623step3 raw30623step3Labels := by
      have ha : raw30623step3 = raw30623step2 := by apply Matrix.ext; unfold raw30623step3 raw30623step2; decide +kernel
      have hl : raw30623step2Labels = labelEmbedding1 ∘ raw30623step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30623step2 raw30623step2Labels raw30623step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2686 node2686Labels := by rfl

def raw30624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30624step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30624step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30624step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30624 raw30624Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw30624 raw30624Labels = mixedMoment B raw30624step0 raw30624step0Labels := by
      have hz : ∀ j, raw30624 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30624step0 = (fun i j => raw30624 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30624step0 raw30624; decide +kernel
      have hl : raw30624step0Labels = raw30624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30624 raw30624Labels permutation434 hz
    mixedMoment B raw30624step0 raw30624step0Labels = mixedMoment B raw30624step1 raw30624step1Labels := by
      have ha : raw30624step1 = (fun i j => raw30624step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30624step1 raw30624step0; decide +kernel
      have hl : raw30624step1Labels = raw30624step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30624step0 raw30624step0Labels permutation127 permutation7
    mixedMoment B raw30624step1 raw30624step1Labels = mixedMoment B raw30624step2 raw30624step2Labels := by
      have ha : raw30624step2 = raw30624step1 := by apply Matrix.ext; unfold raw30624step2 raw30624step1; decide +kernel
      have hl : raw30624step1Labels = labelEmbedding1 ∘ raw30624step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30624step1 raw30624step1Labels raw30624step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2672 node2672Labels := by rfl

def raw30625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30625Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30625step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30625step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30625 raw30625Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw30625 raw30625Labels = mixedMoment B raw30625step0 raw30625step0Labels := by
      have hz : ∀ j, raw30625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30625step0 = (fun i j => raw30625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30625step0 raw30625; decide +kernel
      have hl : raw30625step0Labels = raw30625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30625 raw30625Labels permutation346 hz
    mixedMoment B raw30625step0 raw30625step0Labels = mixedMoment B raw30625step1 raw30625step1Labels := by
      have ha : raw30625step1 = (fun i j => raw30625step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30625step1 raw30625step0; decide +kernel
      have hl : raw30625step1Labels = raw30625step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30625step0 raw30625step0Labels permutation127 permutation7
    mixedMoment B raw30625step1 raw30625step1Labels = mixedMoment B raw30625step2 raw30625step2Labels := by
      have ha : raw30625step2 = raw30625step1 := by apply Matrix.ext; unfold raw30625step2 raw30625step1; decide +kernel
      have hl : raw30625step1Labels = labelEmbedding1 ∘ raw30625step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30625step1 raw30625step1Labels raw30625step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2672 node2672Labels := by rfl

def raw30626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw30626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw30626step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30626step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![2, 1, -3], ![1, -1, 0]]
def raw30626step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30626step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30626step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30626step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30626step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30626 raw30626Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw30626 raw30626Labels = mixedMoment B raw30626step0 raw30626step0Labels := by
      have hz : ∀ j, raw30626 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30626step0 = (fun i j => raw30626 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30626step0 raw30626; decide +kernel
      have hl : raw30626step0Labels = raw30626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30626 raw30626Labels permutation434 hz
    mixedMoment B raw30626step0 raw30626step0Labels = mixedMoment B raw30626step1 raw30626step1Labels := by
      have hz : ∀ j, raw30626step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30626step1 = (fun i j => raw30626step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30626step1 raw30626step0; decide +kernel
      have hl : raw30626step1Labels = raw30626step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30626step0 raw30626step0Labels permutation80 hz
    mixedMoment B raw30626step1 raw30626step1Labels = mixedMoment B raw30626step2 raw30626step2Labels := by
      have ha : raw30626step2 = (fun i j => raw30626step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30626step2 raw30626step1; decide +kernel
      have hl : raw30626step2Labels = raw30626step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30626step1 raw30626step1Labels permutation25 permutation7
    mixedMoment B raw30626step2 raw30626step2Labels = mixedMoment B raw30626step3 raw30626step3Labels := by
      have ha : raw30626step3 = raw30626step2 := by apply Matrix.ext; unfold raw30626step3 raw30626step2; decide +kernel
      have hl : raw30626step2Labels = labelEmbedding1 ∘ raw30626step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30626step2 raw30626step2Labels raw30626step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2742 node2742Labels := by rfl

def raw30627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw30627Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw30627step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30627step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw30627step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30627step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw30627step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30627step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw30627step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30627 raw30627Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw30627 raw30627Labels = mixedMoment B raw30627step0 raw30627step0Labels := by
      have hz : ∀ j, raw30627 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30627step0 = (fun i j => raw30627 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30627step0 raw30627; decide +kernel
      have hl : raw30627step0Labels = raw30627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30627 raw30627Labels permutation434 hz
    mixedMoment B raw30627step0 raw30627step0Labels = mixedMoment B raw30627step1 raw30627step1Labels := by
      have hz : ∀ j, raw30627step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30627step1 = (fun i j => raw30627step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30627step1 raw30627step0; decide +kernel
      have hl : raw30627step1Labels = raw30627step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30627step0 raw30627step0Labels permutation80 hz
    mixedMoment B raw30627step1 raw30627step1Labels = mixedMoment B raw30627step2 raw30627step2Labels := by
      have ha : raw30627step2 = (fun i j => raw30627step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30627step2 raw30627step1; decide +kernel
      have hl : raw30627step2Labels = raw30627step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30627step1 raw30627step1Labels permutation25 permutation7
    mixedMoment B raw30627step2 raw30627step2Labels = mixedMoment B raw30627step3 raw30627step3Labels := by
      have ha : raw30627step3 = raw30627step2 := by apply Matrix.ext; unfold raw30627step3 raw30627step2; decide +kernel
      have hl : raw30627step2Labels = labelEmbedding1 ∘ raw30627step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30627step2 raw30627step2Labels raw30627step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3052 node3052Labels := by rfl

def raw30628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30628Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30628step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30628step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw30628step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30628step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw30628step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30628 raw30628Labels = mixedMoment B node2657 node2657Labels := by
  calc
    mixedMoment B raw30628 raw30628Labels = mixedMoment B raw30628step0 raw30628step0Labels := by
      have hz : ∀ j, raw30628 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30628step0 = (fun i j => raw30628 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30628step0 raw30628; decide +kernel
      have hl : raw30628step0Labels = raw30628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30628 raw30628Labels permutation434 hz
    mixedMoment B raw30628step0 raw30628step0Labels = mixedMoment B raw30628step1 raw30628step1Labels := by
      have ha : raw30628step1 = (fun i j => raw30628step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30628step1 raw30628step0; decide +kernel
      have hl : raw30628step1Labels = raw30628step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30628step0 raw30628step0Labels permutation127 permutation7
    mixedMoment B raw30628step1 raw30628step1Labels = mixedMoment B raw30628step2 raw30628step2Labels := by
      have ha : raw30628step2 = raw30628step1 := by apply Matrix.ext; unfold raw30628step2 raw30628step1; decide +kernel
      have hl : raw30628step1Labels = labelEmbedding1 ∘ raw30628step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30628step1 raw30628step1Labels raw30628step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2657 node2657Labels := by rfl

def raw30629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30629Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30629step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw30629step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30629step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw30629step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30629 raw30629Labels = mixedMoment B node2658 node2658Labels := by
  calc
    mixedMoment B raw30629 raw30629Labels = mixedMoment B raw30629step0 raw30629step0Labels := by
      have hz : ∀ j, raw30629 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30629step0 = (fun i j => raw30629 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30629step0 raw30629; decide +kernel
      have hl : raw30629step0Labels = raw30629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30629 raw30629Labels permutation434 hz
    mixedMoment B raw30629step0 raw30629step0Labels = mixedMoment B raw30629step1 raw30629step1Labels := by
      have ha : raw30629step1 = (fun i j => raw30629step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30629step1 raw30629step0; decide +kernel
      have hl : raw30629step1Labels = raw30629step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30629step0 raw30629step0Labels permutation127 permutation7
    mixedMoment B raw30629step1 raw30629step1Labels = mixedMoment B raw30629step2 raw30629step2Labels := by
      have ha : raw30629step2 = raw30629step1 := by apply Matrix.ext; unfold raw30629step2 raw30629step1; decide +kernel
      have hl : raw30629step1Labels = labelEmbedding1 ∘ raw30629step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30629step1 raw30629step1Labels raw30629step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2658 node2658Labels := by rfl

def raw30630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30630Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30630step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30630step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30630 raw30630Labels = mixedMoment B node2652 node2652Labels := by
  calc
    mixedMoment B raw30630 raw30630Labels = mixedMoment B raw30630step0 raw30630step0Labels := by
      have ha : raw30630step0 = (fun i j => raw30630 (permutation584 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30630step0 raw30630; decide +kernel
      have hl : raw30630step0Labels = raw30630Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30630 raw30630Labels permutation584 permutation7
    mixedMoment B raw30630step0 raw30630step0Labels = mixedMoment B raw30630step1 raw30630step1Labels := by
      have ha : raw30630step1 = raw30630step0 := by apply Matrix.ext; unfold raw30630step1 raw30630step0; decide +kernel
      have hl : raw30630step0Labels = labelEmbedding1 ∘ raw30630step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30630step0 raw30630step0Labels raw30630step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2652 node2652Labels := by rfl

def raw30631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw30631Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw30631step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30631step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30631step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30631step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30631 raw30631Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw30631 raw30631Labels = mixedMoment B raw30631step0 raw30631step0Labels := by
      have hz : ∀ j, raw30631 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30631step0 = (fun i j => raw30631 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30631step0 raw30631; decide +kernel
      have hl : raw30631step0Labels = raw30631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30631 raw30631Labels permutation434 hz
    mixedMoment B raw30631step0 raw30631step0Labels = mixedMoment B raw30631step1 raw30631step1Labels := by
      have ha : raw30631step1 = (fun i j => raw30631step0 (permutation121 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30631step1 raw30631step0; decide +kernel
      have hl : raw30631step1Labels = raw30631step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30631step0 raw30631step0Labels permutation121 permutation7
    mixedMoment B raw30631step1 raw30631step1Labels = mixedMoment B raw30631step2 raw30631step2Labels := by
      have ha : raw30631step2 = raw30631step1 := by apply Matrix.ext; unfold raw30631step2 raw30631step1; decide +kernel
      have hl : raw30631step1Labels = labelEmbedding1 ∘ raw30631step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30631step1 raw30631step1Labels raw30631step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2704 node2704Labels := by rfl

def raw30632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30632Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30632step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30632step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw30632step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30632step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw30632step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30632 raw30632Labels = mixedMoment B node2657 node2657Labels := by
  calc
    mixedMoment B raw30632 raw30632Labels = mixedMoment B raw30632step0 raw30632step0Labels := by
      have hz : ∀ j, raw30632 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30632step0 = (fun i j => raw30632 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30632step0 raw30632; decide +kernel
      have hl : raw30632step0Labels = raw30632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30632 raw30632Labels permutation346 hz
    mixedMoment B raw30632step0 raw30632step0Labels = mixedMoment B raw30632step1 raw30632step1Labels := by
      have ha : raw30632step1 = (fun i j => raw30632step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30632step1 raw30632step0; decide +kernel
      have hl : raw30632step1Labels = raw30632step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30632step0 raw30632step0Labels permutation127 permutation7
    mixedMoment B raw30632step1 raw30632step1Labels = mixedMoment B raw30632step2 raw30632step2Labels := by
      have ha : raw30632step2 = raw30632step1 := by apply Matrix.ext; unfold raw30632step2 raw30632step1; decide +kernel
      have hl : raw30632step1Labels = labelEmbedding1 ∘ raw30632step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30632step1 raw30632step1Labels raw30632step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2657 node2657Labels := by rfl

def raw30633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30633Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30633step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw30633step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw30633step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30633 raw30633Labels = mixedMoment B node2658 node2658Labels := by
  calc
    mixedMoment B raw30633 raw30633Labels = mixedMoment B raw30633step0 raw30633step0Labels := by
      have hz : ∀ j, raw30633 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30633step0 = (fun i j => raw30633 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30633step0 raw30633; decide +kernel
      have hl : raw30633step0Labels = raw30633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30633 raw30633Labels permutation346 hz
    mixedMoment B raw30633step0 raw30633step0Labels = mixedMoment B raw30633step1 raw30633step1Labels := by
      have ha : raw30633step1 = (fun i j => raw30633step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30633step1 raw30633step0; decide +kernel
      have hl : raw30633step1Labels = raw30633step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30633step0 raw30633step0Labels permutation127 permutation7
    mixedMoment B raw30633step1 raw30633step1Labels = mixedMoment B raw30633step2 raw30633step2Labels := by
      have ha : raw30633step2 = raw30633step1 := by apply Matrix.ext; unfold raw30633step2 raw30633step1; decide +kernel
      have hl : raw30633step1Labels = labelEmbedding1 ∘ raw30633step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30633step1 raw30633step1Labels raw30633step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2658 node2658Labels := by rfl

def raw30634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30634Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30634step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30634step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30634 raw30634Labels = mixedMoment B node2652 node2652Labels := by
  calc
    mixedMoment B raw30634 raw30634Labels = mixedMoment B raw30634step0 raw30634step0Labels := by
      have ha : raw30634step0 = (fun i j => raw30634 (permutation589 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30634step0 raw30634; decide +kernel
      have hl : raw30634step0Labels = raw30634Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30634 raw30634Labels permutation589 permutation7
    mixedMoment B raw30634step0 raw30634step0Labels = mixedMoment B raw30634step1 raw30634step1Labels := by
      have ha : raw30634step1 = raw30634step0 := by apply Matrix.ext; unfold raw30634step1 raw30634step0; decide +kernel
      have hl : raw30634step0Labels = labelEmbedding1 ∘ raw30634step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30634step0 raw30634step0Labels raw30634step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2652 node2652Labels := by rfl

def raw30635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw30635Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3], ![1, -1, 0]]
def raw30635step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30635step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30635step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30635step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30635 raw30635Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw30635 raw30635Labels = mixedMoment B raw30635step0 raw30635step0Labels := by
      have hz : ∀ j, raw30635 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30635step0 = (fun i j => raw30635 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30635step0 raw30635; decide +kernel
      have hl : raw30635step0Labels = raw30635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30635 raw30635Labels permutation346 hz
    mixedMoment B raw30635step0 raw30635step0Labels = mixedMoment B raw30635step1 raw30635step1Labels := by
      have ha : raw30635step1 = (fun i j => raw30635step0 (permutation121 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30635step1 raw30635step0; decide +kernel
      have hl : raw30635step1Labels = raw30635step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30635step0 raw30635step0Labels permutation121 permutation7
    mixedMoment B raw30635step1 raw30635step1Labels = mixedMoment B raw30635step2 raw30635step2Labels := by
      have ha : raw30635step2 = raw30635step1 := by apply Matrix.ext; unfold raw30635step2 raw30635step1; decide +kernel
      have hl : raw30635step1Labels = labelEmbedding1 ∘ raw30635step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30635step1 raw30635step1Labels raw30635step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2704 node2704Labels := by rfl

def raw30636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30636Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30636step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![3, 0, -3], ![2, -2, 0]]
def raw30636step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw30636step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30636step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw30636step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30636 raw30636Labels = mixedMoment B node2167 node2167Labels := by
  calc
    mixedMoment B raw30636 raw30636Labels = mixedMoment B raw30636step0 raw30636step0Labels := by
      have hz : ∀ j, raw30636 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30636step0 = (fun i j => raw30636 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30636step0 raw30636; decide +kernel
      have hl : raw30636step0Labels = raw30636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30636 raw30636Labels permutation434 hz
    mixedMoment B raw30636step0 raw30636step0Labels = mixedMoment B raw30636step1 raw30636step1Labels := by
      have hz : ∀ j, raw30636step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30636step1 = (fun i j => raw30636step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30636step1 raw30636step0; decide +kernel
      have hl : raw30636step1Labels = raw30636step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30636step0 raw30636step0Labels permutation80 hz
    mixedMoment B raw30636step1 raw30636step1Labels = mixedMoment B raw30636step2 raw30636step2Labels := by
      have ha : raw30636step2 = (fun i j => raw30636step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30636step2 raw30636step1; decide +kernel
      have hl : raw30636step2Labels = raw30636step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30636step1 raw30636step1Labels permutation25 permutation7
    mixedMoment B raw30636step2 raw30636step2Labels = mixedMoment B raw30636step3 raw30636step3Labels := by
      have ha : raw30636step3 = raw30636step2 := by apply Matrix.ext; unfold raw30636step3 raw30636step2; decide +kernel
      have hl : raw30636step2Labels = labelEmbedding1 ∘ raw30636step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30636step2 raw30636step2Labels raw30636step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2167 node2167Labels := by rfl

def raw30637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30637Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30637step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30637step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![3, 0, -3], ![2, -2, 0]]
def raw30637step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30637step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw30637step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30637step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 1, -2], ![2, 1, -3]]
def raw30637step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30637 raw30637Labels = mixedMoment B node2168 node2168Labels := by
  calc
    mixedMoment B raw30637 raw30637Labels = mixedMoment B raw30637step0 raw30637step0Labels := by
      have hz : ∀ j, raw30637 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30637step0 = (fun i j => raw30637 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30637step0 raw30637; decide +kernel
      have hl : raw30637step0Labels = raw30637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30637 raw30637Labels permutation434 hz
    mixedMoment B raw30637step0 raw30637step0Labels = mixedMoment B raw30637step1 raw30637step1Labels := by
      have hz : ∀ j, raw30637step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30637step1 = (fun i j => raw30637step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30637step1 raw30637step0; decide +kernel
      have hl : raw30637step1Labels = raw30637step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30637step0 raw30637step0Labels permutation80 hz
    mixedMoment B raw30637step1 raw30637step1Labels = mixedMoment B raw30637step2 raw30637step2Labels := by
      have ha : raw30637step2 = (fun i j => raw30637step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30637step2 raw30637step1; decide +kernel
      have hl : raw30637step2Labels = raw30637step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30637step1 raw30637step1Labels permutation25 permutation7
    mixedMoment B raw30637step2 raw30637step2Labels = mixedMoment B raw30637step3 raw30637step3Labels := by
      have ha : raw30637step3 = raw30637step2 := by apply Matrix.ext; unfold raw30637step3 raw30637step2; decide +kernel
      have hl : raw30637step2Labels = labelEmbedding1 ∘ raw30637step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30637step2 raw30637step2Labels raw30637step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2168 node2168Labels := by rfl

def raw30638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30638Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30638step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30638step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30638step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30638step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30638 raw30638Labels = mixedMoment B node2151 node2151Labels := by
  calc
    mixedMoment B raw30638 raw30638Labels = mixedMoment B raw30638step0 raw30638step0Labels := by
      have hz : ∀ j, raw30638 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30638step0 = (fun i j => raw30638 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30638step0 raw30638; decide +kernel
      have hl : raw30638step0Labels = raw30638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30638 raw30638Labels permutation434 hz
    mixedMoment B raw30638step0 raw30638step0Labels = mixedMoment B raw30638step1 raw30638step1Labels := by
      have ha : raw30638step1 = (fun i j => raw30638step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30638step1 raw30638step0; decide +kernel
      have hl : raw30638step1Labels = raw30638step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30638step0 raw30638step0Labels permutation127 permutation7
    mixedMoment B raw30638step1 raw30638step1Labels = mixedMoment B raw30638step2 raw30638step2Labels := by
      have ha : raw30638step2 = raw30638step1 := by apply Matrix.ext; unfold raw30638step2 raw30638step1; decide +kernel
      have hl : raw30638step1Labels = labelEmbedding1 ∘ raw30638step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30638step1 raw30638step1Labels raw30638step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2151 node2151Labels := by rfl

def raw30639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30639Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30639step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30639step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30639step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30639 raw30639Labels = mixedMoment B node2151 node2151Labels := by
  calc
    mixedMoment B raw30639 raw30639Labels = mixedMoment B raw30639step0 raw30639step0Labels := by
      have hz : ∀ j, raw30639 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30639step0 = (fun i j => raw30639 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30639step0 raw30639; decide +kernel
      have hl : raw30639step0Labels = raw30639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30639 raw30639Labels permutation346 hz
    mixedMoment B raw30639step0 raw30639step0Labels = mixedMoment B raw30639step1 raw30639step1Labels := by
      have ha : raw30639step1 = (fun i j => raw30639step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30639step1 raw30639step0; decide +kernel
      have hl : raw30639step1Labels = raw30639step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30639step0 raw30639step0Labels permutation127 permutation7
    mixedMoment B raw30639step1 raw30639step1Labels = mixedMoment B raw30639step2 raw30639step2Labels := by
      have ha : raw30639step2 = raw30639step1 := by apply Matrix.ext; unfold raw30639step2 raw30639step1; decide +kernel
      have hl : raw30639step1Labels = labelEmbedding1 ∘ raw30639step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30639step1 raw30639step1Labels raw30639step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2151 node2151Labels := by rfl

def raw30640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw30640Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![3, 0, -3], ![1, -1, 0]]
def raw30640step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![3, 0, -3], ![1, -1, 0]]
def raw30640step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30640step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30640step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30640step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30640 raw30640Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw30640 raw30640Labels = mixedMoment B raw30640step0 raw30640step0Labels := by
      have hz : ∀ j, raw30640 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30640step0 = (fun i j => raw30640 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30640step0 raw30640; decide +kernel
      have hl : raw30640step0Labels = raw30640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30640 raw30640Labels permutation434 hz
    mixedMoment B raw30640step0 raw30640step0Labels = mixedMoment B raw30640step1 raw30640step1Labels := by
      have hz : ∀ j, raw30640step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30640step1 = (fun i j => raw30640step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30640step1 raw30640step0; decide +kernel
      have hl : raw30640step1Labels = raw30640step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30640step0 raw30640step0Labels permutation80 hz
    mixedMoment B raw30640step1 raw30640step1Labels = mixedMoment B raw30640step2 raw30640step2Labels := by
      have ha : raw30640step2 = (fun i j => raw30640step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30640step2 raw30640step1; decide +kernel
      have hl : raw30640step2Labels = raw30640step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30640step1 raw30640step1Labels permutation25 permutation7
    mixedMoment B raw30640step2 raw30640step2Labels = mixedMoment B raw30640step3 raw30640step3Labels := by
      have ha : raw30640step3 = raw30640step2 := by apply Matrix.ext; unfold raw30640step3 raw30640step2; decide +kernel
      have hl : raw30640step2Labels = labelEmbedding1 ∘ raw30640step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30640step2 raw30640step2Labels raw30640step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

def raw30641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30641Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30641step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw30641step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30641step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw30641step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30641step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw30641step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30641 raw30641Labels = mixedMoment B node2258 node2258Labels := by
  calc
    mixedMoment B raw30641 raw30641Labels = mixedMoment B raw30641step0 raw30641step0Labels := by
      have hz : ∀ j, raw30641 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30641step0 = (fun i j => raw30641 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30641step0 raw30641; decide +kernel
      have hl : raw30641step0Labels = raw30641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30641 raw30641Labels permutation434 hz
    mixedMoment B raw30641step0 raw30641step0Labels = mixedMoment B raw30641step1 raw30641step1Labels := by
      have hz : ∀ j, raw30641step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30641step1 = (fun i j => raw30641step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30641step1 raw30641step0; decide +kernel
      have hl : raw30641step1Labels = raw30641step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30641step0 raw30641step0Labels permutation80 hz
    mixedMoment B raw30641step1 raw30641step1Labels = mixedMoment B raw30641step2 raw30641step2Labels := by
      have ha : raw30641step2 = (fun i j => raw30641step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30641step2 raw30641step1; decide +kernel
      have hl : raw30641step2Labels = raw30641step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30641step1 raw30641step1Labels permutation29 permutation5
    mixedMoment B raw30641step2 raw30641step2Labels = mixedMoment B raw30641step3 raw30641step3Labels := by
      have ha : raw30641step3 = raw30641step2 := by apply Matrix.ext; unfold raw30641step3 raw30641step2; decide +kernel
      have hl : raw30641step2Labels = labelEmbedding1 ∘ raw30641step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30641step2 raw30641step2Labels raw30641step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2258 node2258Labels := by rfl

def raw30642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30642Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30642step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30642step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 1, -3], ![3, -3, 0]]
def raw30642step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30642step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw30642step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30642step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -3, 2], ![1, 1, -2], ![1, 2, -3]]
def raw30642step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30642 raw30642Labels = mixedMoment B node2286 node2286Labels := by
  calc
    mixedMoment B raw30642 raw30642Labels = mixedMoment B raw30642step0 raw30642step0Labels := by
      have hz : ∀ j, raw30642 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30642step0 = (fun i j => raw30642 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30642step0 raw30642; decide +kernel
      have hl : raw30642step0Labels = raw30642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30642 raw30642Labels permutation434 hz
    mixedMoment B raw30642step0 raw30642step0Labels = mixedMoment B raw30642step1 raw30642step1Labels := by
      have hz : ∀ j, raw30642step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30642step1 = (fun i j => raw30642step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30642step1 raw30642step0; decide +kernel
      have hl : raw30642step1Labels = raw30642step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30642step0 raw30642step0Labels permutation80 hz
    mixedMoment B raw30642step1 raw30642step1Labels = mixedMoment B raw30642step2 raw30642step2Labels := by
      have ha : raw30642step2 = (fun i j => raw30642step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30642step2 raw30642step1; decide +kernel
      have hl : raw30642step2Labels = raw30642step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30642step1 raw30642step1Labels permutation31 permutation5
    mixedMoment B raw30642step2 raw30642step2Labels = mixedMoment B raw30642step3 raw30642step3Labels := by
      have ha : raw30642step3 = raw30642step2 := by apply Matrix.ext; unfold raw30642step3 raw30642step2; decide +kernel
      have hl : raw30642step2Labels = labelEmbedding1 ∘ raw30642step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30642step2 raw30642step2Labels raw30642step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2286 node2286Labels := by rfl

def raw30643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30643Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30643step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw30643step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30643step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw30643step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30643 raw30643Labels = mixedMoment B node2256 node2256Labels := by
  calc
    mixedMoment B raw30643 raw30643Labels = mixedMoment B raw30643step0 raw30643step0Labels := by
      have hz : ∀ j, raw30643 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30643step0 = (fun i j => raw30643 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30643step0 raw30643; decide +kernel
      have hl : raw30643step0Labels = raw30643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30643 raw30643Labels permutation434 hz
    mixedMoment B raw30643step0 raw30643step0Labels = mixedMoment B raw30643step1 raw30643step1Labels := by
      have ha : raw30643step1 = (fun i j => raw30643step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30643step1 raw30643step0; decide +kernel
      have hl : raw30643step1Labels = raw30643step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30643step0 raw30643step0Labels permutation139 permutation5
    mixedMoment B raw30643step1 raw30643step1Labels = mixedMoment B raw30643step2 raw30643step2Labels := by
      have ha : raw30643step2 = raw30643step1 := by apply Matrix.ext; unfold raw30643step2 raw30643step1; decide +kernel
      have hl : raw30643step1Labels = labelEmbedding1 ∘ raw30643step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30643step1 raw30643step1Labels raw30643step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2256 node2256Labels := by rfl

def raw30644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30644Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30644step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30644step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw30644step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30644step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 2, -3]]
def raw30644step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30644 raw30644Labels = mixedMoment B node2256 node2256Labels := by
  calc
    mixedMoment B raw30644 raw30644Labels = mixedMoment B raw30644step0 raw30644step0Labels := by
      have hz : ∀ j, raw30644 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30644step0 = (fun i j => raw30644 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30644step0 raw30644; decide +kernel
      have hl : raw30644step0Labels = raw30644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30644 raw30644Labels permutation346 hz
    mixedMoment B raw30644step0 raw30644step0Labels = mixedMoment B raw30644step1 raw30644step1Labels := by
      have ha : raw30644step1 = (fun i j => raw30644step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30644step1 raw30644step0; decide +kernel
      have hl : raw30644step1Labels = raw30644step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30644step0 raw30644step0Labels permutation139 permutation5
    mixedMoment B raw30644step1 raw30644step1Labels = mixedMoment B raw30644step2 raw30644step2Labels := by
      have ha : raw30644step2 = raw30644step1 := by apply Matrix.ext; unfold raw30644step2 raw30644step1; decide +kernel
      have hl : raw30644step1Labels = labelEmbedding1 ∘ raw30644step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30644step1 raw30644step1Labels raw30644step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2256 node2256Labels := by rfl

def raw30645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30645Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30645step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30645step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, 1, -3], ![2, -2, 0]]
def raw30645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30645step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw30645step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30645step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30645step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30645 raw30645Labels = mixedMoment B node3397 node3397Labels := by
  calc
    mixedMoment B raw30645 raw30645Labels = mixedMoment B raw30645step0 raw30645step0Labels := by
      have hz : ∀ j, raw30645 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30645step0 = (fun i j => raw30645 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30645step0 raw30645; decide +kernel
      have hl : raw30645step0Labels = raw30645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30645 raw30645Labels permutation434 hz
    mixedMoment B raw30645step0 raw30645step0Labels = mixedMoment B raw30645step1 raw30645step1Labels := by
      have hz : ∀ j, raw30645step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30645step1 = (fun i j => raw30645step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30645step1 raw30645step0; decide +kernel
      have hl : raw30645step1Labels = raw30645step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30645step0 raw30645step0Labels permutation80 hz
    mixedMoment B raw30645step1 raw30645step1Labels = mixedMoment B raw30645step2 raw30645step2Labels := by
      have ha : raw30645step2 = (fun i j => raw30645step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30645step2 raw30645step1; decide +kernel
      have hl : raw30645step2Labels = raw30645step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30645step1 raw30645step1Labels permutation25 permutation2
    mixedMoment B raw30645step2 raw30645step2Labels = mixedMoment B raw30645step3 raw30645step3Labels := by
      have ha : raw30645step3 = -raw30645step2 := by apply Matrix.ext; change ∀ i j, raw30645step3 i j = -(raw30645step2 i j); unfold raw30645step3 raw30645step2; decide +kernel
      have hl : raw30645step3Labels = raw30645step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3397 node3397Labels := by rfl

def raw30646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30646Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30646step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw30646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30646 raw30646Labels = mixedMoment B node2336 node2336Labels := by
  calc
    mixedMoment B raw30646 raw30646Labels = mixedMoment B raw30646step0 raw30646step0Labels := by
      have hz : ∀ j, raw30646 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30646step0 = (fun i j => raw30646 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30646step0 raw30646; decide +kernel
      have hl : raw30646step0Labels = raw30646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30646 raw30646Labels permutation434 hz
    mixedMoment B raw30646step0 raw30646step0Labels = mixedMoment B raw30646step1 raw30646step1Labels := by
      have ha : raw30646step1 = (fun i j => raw30646step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30646step1 raw30646step0; decide +kernel
      have hl : raw30646step1Labels = raw30646step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30646step0 raw30646step0Labels permutation33 permutation2
    _ = mixedMoment B node2336 node2336Labels := by rfl

def raw30647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30647Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw30647step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw30647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30647 raw30647Labels = mixedMoment B node2336 node2336Labels := by
  calc
    mixedMoment B raw30647 raw30647Labels = mixedMoment B raw30647step0 raw30647step0Labels := by
      have hz : ∀ j, raw30647 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30647step0 = (fun i j => raw30647 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30647step0 raw30647; decide +kernel
      have hl : raw30647step0Labels = raw30647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30647 raw30647Labels permutation346 hz
    mixedMoment B raw30647step0 raw30647step0Labels = mixedMoment B raw30647step1 raw30647step1Labels := by
      have ha : raw30647step1 = (fun i j => raw30647step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30647step1 raw30647step0; decide +kernel
      have hl : raw30647step1Labels = raw30647step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30647step0 raw30647step0Labels permutation33 permutation2
    _ = mixedMoment B node2336 node2336Labels := by rfl

def raw30648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30648Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![3, 0, -3], ![2, -2, 0]]
def raw30648step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30648step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![3, 0, -3], ![2, -2, 0]]
def raw30648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30648step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw30648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30648step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw30648step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30648 raw30648Labels = mixedMoment B node1818 node1818Labels := by
  calc
    mixedMoment B raw30648 raw30648Labels = mixedMoment B raw30648step0 raw30648step0Labels := by
      have hz : ∀ j, raw30648 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30648step0 = (fun i j => raw30648 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30648step0 raw30648; decide +kernel
      have hl : raw30648step0Labels = raw30648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30648 raw30648Labels permutation434 hz
    mixedMoment B raw30648step0 raw30648step0Labels = mixedMoment B raw30648step1 raw30648step1Labels := by
      have hz : ∀ j, raw30648step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30648step1 = (fun i j => raw30648step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30648step1 raw30648step0; decide +kernel
      have hl : raw30648step1Labels = raw30648step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30648step0 raw30648step0Labels permutation80 hz
    mixedMoment B raw30648step1 raw30648step1Labels = mixedMoment B raw30648step2 raw30648step2Labels := by
      have ha : raw30648step2 = (fun i j => raw30648step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30648step2 raw30648step1; decide +kernel
      have hl : raw30648step2Labels = raw30648step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30648step1 raw30648step1Labels permutation25 permutation2
    mixedMoment B raw30648step2 raw30648step2Labels = mixedMoment B raw30648step3 raw30648step3Labels := by
      have ha : raw30648step3 = -raw30648step2 := by apply Matrix.ext; change ∀ i j, raw30648step3 i j = -(raw30648step2 i j); unfold raw30648step3 raw30648step2; decide +kernel
      have hl : raw30648step3Labels = raw30648step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1818 node1818Labels := by rfl

def raw30649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30649Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30649step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 1, -3], ![3, -3, 0]]
def raw30649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30649 raw30649Labels = mixedMoment B node2346 node2346Labels := by
  calc
    mixedMoment B raw30649 raw30649Labels = mixedMoment B raw30649step0 raw30649step0Labels := by
      have hz : ∀ j, raw30649 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30649step0 = (fun i j => raw30649 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30649step0 raw30649; decide +kernel
      have hl : raw30649step0Labels = raw30649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30649 raw30649Labels permutation434 hz
    mixedMoment B raw30649step0 raw30649step0Labels = mixedMoment B raw30649step1 raw30649step1Labels := by
      have hz : ∀ j, raw30649step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30649step1 = (fun i j => raw30649step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30649step1 raw30649step0; decide +kernel
      have hl : raw30649step1Labels = raw30649step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30649step0 raw30649step0Labels permutation80 hz
    _ = mixedMoment B node2346 node2346Labels := by rfl

def raw30650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30650step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30650step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30650step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30650step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw30650step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30650step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30650 raw30650Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw30650 raw30650Labels = mixedMoment B raw30650step0 raw30650step0Labels := by
      have hz : ∀ j, raw30650 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30650step0 = (fun i j => raw30650 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30650step0 raw30650; decide +kernel
      have hl : raw30650step0Labels = raw30650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30650 raw30650Labels permutation434 hz
    mixedMoment B raw30650step0 raw30650step0Labels = mixedMoment B raw30650step1 raw30650step1Labels := by
      have hz : ∀ j, raw30650step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30650step1 = (fun i j => raw30650step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30650step1 raw30650step0; decide +kernel
      have hl : raw30650step1Labels = raw30650step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30650step0 raw30650step0Labels permutation80 hz
    mixedMoment B raw30650step1 raw30650step1Labels = mixedMoment B raw30650step2 raw30650step2Labels := by
      have ha : raw30650step2 = (fun i j => raw30650step1 (permutation24 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30650step2 raw30650step1; decide +kernel
      have hl : raw30650step2Labels = raw30650step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30650step1 raw30650step1Labels permutation24 permutation5
    mixedMoment B raw30650step2 raw30650step2Labels = mixedMoment B raw30650step3 raw30650step3Labels := by
      have ha : raw30650step3 = raw30650step2 := by apply Matrix.ext; unfold raw30650step3 raw30650step2; decide +kernel
      have hl : raw30650step2Labels = labelEmbedding8 ∘ raw30650step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30650step2 raw30650step2Labels raw30650step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

def raw30651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw30651step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw30651step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw30651step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30651 raw30651Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw30651 raw30651Labels = mixedMoment B raw30651step0 raw30651step0Labels := by
      have hz : ∀ j, raw30651 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30651step0 = (fun i j => raw30651 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30651step0 raw30651; decide +kernel
      have hl : raw30651step0Labels = raw30651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30651 raw30651Labels permutation434 hz
    mixedMoment B raw30651step0 raw30651step0Labels = mixedMoment B raw30651step1 raw30651step1Labels := by
      have ha : raw30651step1 = (fun i j => raw30651step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30651step1 raw30651step0; decide +kernel
      have hl : raw30651step1Labels = raw30651step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30651step0 raw30651step0Labels permutation125 permutation5
    mixedMoment B raw30651step1 raw30651step1Labels = mixedMoment B raw30651step2 raw30651step2Labels := by
      have ha : raw30651step2 = raw30651step1 := by apply Matrix.ext; unfold raw30651step2 raw30651step1; decide +kernel
      have hl : raw30651step1Labels = labelEmbedding8 ∘ raw30651step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30651step1 raw30651step1Labels raw30651step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

def raw30652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw30652step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw30652step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw30652step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30652 raw30652Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw30652 raw30652Labels = mixedMoment B raw30652step0 raw30652step0Labels := by
      have hz : ∀ j, raw30652 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30652step0 = (fun i j => raw30652 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30652step0 raw30652; decide +kernel
      have hl : raw30652step0Labels = raw30652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30652 raw30652Labels permutation346 hz
    mixedMoment B raw30652step0 raw30652step0Labels = mixedMoment B raw30652step1 raw30652step1Labels := by
      have ha : raw30652step1 = (fun i j => raw30652step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30652step1 raw30652step0; decide +kernel
      have hl : raw30652step1Labels = raw30652step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30652step0 raw30652step0Labels permutation125 permutation5
    mixedMoment B raw30652step1 raw30652step1Labels = mixedMoment B raw30652step2 raw30652step2Labels := by
      have ha : raw30652step2 = raw30652step1 := by apply Matrix.ext; unfold raw30652step2 raw30652step1; decide +kernel
      have hl : raw30652step1Labels = labelEmbedding8 ∘ raw30652step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30652step1 raw30652step1Labels raw30652step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

def raw30653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30653step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30653step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30653step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30653 raw30653Labels = mixedMoment B node4920 node4920Labels := by
  calc
    mixedMoment B raw30653 raw30653Labels = mixedMoment B raw30653step0 raw30653step0Labels := by
      have hz : ∀ j, raw30653 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30653step0 = (fun i j => raw30653 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30653step0 raw30653; decide +kernel
      have hl : raw30653step0Labels = raw30653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30653 raw30653Labels permutation434 hz
    mixedMoment B raw30653step0 raw30653step0Labels = mixedMoment B raw30653step1 raw30653step1Labels := by
      have ha : raw30653step1 = (fun i j => raw30653step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30653step1 raw30653step0; decide +kernel
      have hl : raw30653step1Labels = raw30653step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30653step0 raw30653step0Labels permutation33 permutation3
    mixedMoment B raw30653step1 raw30653step1Labels = mixedMoment B raw30653step2 raw30653step2Labels := by
      have ha : raw30653step2 = raw30653step1 := by apply Matrix.ext; unfold raw30653step2 raw30653step1; decide +kernel
      have hl : raw30653step1Labels = labelEmbedding6 ∘ raw30653step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30653step1 raw30653step1Labels raw30653step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4920 node4920Labels := by rfl

def raw30654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30654step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30654step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30654 raw30654Labels = mixedMoment B node5028 node5028Labels := by
  calc
    mixedMoment B raw30654 raw30654Labels = mixedMoment B raw30654step0 raw30654step0Labels := by
      have ha : raw30654step0 = (fun i j => raw30654 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30654step0 raw30654; decide +kernel
      have hl : raw30654step0Labels = raw30654Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30654 raw30654Labels permutation159 permutation3
    mixedMoment B raw30654step0 raw30654step0Labels = mixedMoment B raw30654step1 raw30654step1Labels := by
      have ha : raw30654step1 = raw30654step0 := by apply Matrix.ext; unfold raw30654step1 raw30654step0; decide +kernel
      have hl : raw30654step0Labels = labelEmbedding6 ∘ raw30654step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30654step0 raw30654step0Labels raw30654step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5028 node5028Labels := by rfl

def raw30655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw30655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw30655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30655step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30655step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30655step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30655step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30655 raw30655Labels = mixedMoment B node5094 node5094Labels := by
  calc
    mixedMoment B raw30655 raw30655Labels = mixedMoment B raw30655step0 raw30655step0Labels := by
      have hz : ∀ j, raw30655 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30655step0 = (fun i j => raw30655 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30655step0 raw30655; decide +kernel
      have hl : raw30655step0Labels = raw30655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30655 raw30655Labels permutation434 hz
    mixedMoment B raw30655step0 raw30655step0Labels = mixedMoment B raw30655step1 raw30655step1Labels := by
      have ha : raw30655step1 = (fun i j => raw30655step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30655step1 raw30655step0; decide +kernel
      have hl : raw30655step1Labels = raw30655step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30655step0 raw30655step0Labels permutation36 permutation3
    mixedMoment B raw30655step1 raw30655step1Labels = mixedMoment B raw30655step2 raw30655step2Labels := by
      have ha : raw30655step2 = raw30655step1 := by apply Matrix.ext; unfold raw30655step2 raw30655step1; decide +kernel
      have hl : raw30655step1Labels = labelEmbedding6 ∘ raw30655step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30655step1 raw30655step1Labels raw30655step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5094 node5094Labels := by rfl

def raw30656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30656step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30656step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30656step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30656 raw30656Labels = mixedMoment B node4920 node4920Labels := by
  calc
    mixedMoment B raw30656 raw30656Labels = mixedMoment B raw30656step0 raw30656step0Labels := by
      have hz : ∀ j, raw30656 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30656step0 = (fun i j => raw30656 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30656step0 raw30656; decide +kernel
      have hl : raw30656step0Labels = raw30656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30656 raw30656Labels permutation346 hz
    mixedMoment B raw30656step0 raw30656step0Labels = mixedMoment B raw30656step1 raw30656step1Labels := by
      have ha : raw30656step1 = (fun i j => raw30656step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30656step1 raw30656step0; decide +kernel
      have hl : raw30656step1Labels = raw30656step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30656step0 raw30656step0Labels permutation33 permutation3
    mixedMoment B raw30656step1 raw30656step1Labels = mixedMoment B raw30656step2 raw30656step2Labels := by
      have ha : raw30656step2 = raw30656step1 := by apply Matrix.ext; unfold raw30656step2 raw30656step1; decide +kernel
      have hl : raw30656step1Labels = labelEmbedding6 ∘ raw30656step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30656step1 raw30656step1Labels raw30656step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4920 node4920Labels := by rfl

def raw30657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30657step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30657step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30657step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30657 raw30657Labels = mixedMoment B node5028 node5028Labels := by
  calc
    mixedMoment B raw30657 raw30657Labels = mixedMoment B raw30657step0 raw30657step0Labels := by
      have ha : raw30657step0 = (fun i j => raw30657 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30657step0 raw30657; decide +kernel
      have hl : raw30657step0Labels = raw30657Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30657 raw30657Labels permutation153 permutation3
    mixedMoment B raw30657step0 raw30657step0Labels = mixedMoment B raw30657step1 raw30657step1Labels := by
      have ha : raw30657step1 = raw30657step0 := by apply Matrix.ext; unfold raw30657step1 raw30657step0; decide +kernel
      have hl : raw30657step0Labels = labelEmbedding6 ∘ raw30657step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30657step0 raw30657step0Labels raw30657step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5028 node5028Labels := by rfl

def raw30658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw30658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw30658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30658step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30658step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30658step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30658 raw30658Labels = mixedMoment B node5094 node5094Labels := by
  calc
    mixedMoment B raw30658 raw30658Labels = mixedMoment B raw30658step0 raw30658step0Labels := by
      have hz : ∀ j, raw30658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30658step0 = (fun i j => raw30658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30658step0 raw30658; decide +kernel
      have hl : raw30658step0Labels = raw30658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30658 raw30658Labels permutation346 hz
    mixedMoment B raw30658step0 raw30658step0Labels = mixedMoment B raw30658step1 raw30658step1Labels := by
      have ha : raw30658step1 = (fun i j => raw30658step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30658step1 raw30658step0; decide +kernel
      have hl : raw30658step1Labels = raw30658step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30658step0 raw30658step0Labels permutation36 permutation3
    mixedMoment B raw30658step1 raw30658step1Labels = mixedMoment B raw30658step2 raw30658step2Labels := by
      have ha : raw30658step2 = raw30658step1 := by apply Matrix.ext; unfold raw30658step2 raw30658step1; decide +kernel
      have hl : raw30658step1Labels = labelEmbedding6 ∘ raw30658step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30658step1 raw30658step1Labels raw30658step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5094 node5094Labels := by rfl

def raw30659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![2, 0, -2]]
def raw30659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![3, -4, 1], ![2, 0, -2]]
def raw30659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![3, -4, 1], ![2, 0, -2]]
def raw30659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30659step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw30659step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw30659step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![2, 0, -2], ![2, 1, -3]]
def raw30659step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30659 raw30659Labels = mixedMoment B node4383 node4383Labels := by
  calc
    mixedMoment B raw30659 raw30659Labels = mixedMoment B raw30659step0 raw30659step0Labels := by
      have hz : ∀ j, raw30659 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30659step0 = (fun i j => raw30659 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30659step0 raw30659; decide +kernel
      have hl : raw30659step0Labels = raw30659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30659 raw30659Labels permutation434 hz
    mixedMoment B raw30659step0 raw30659step0Labels = mixedMoment B raw30659step1 raw30659step1Labels := by
      have hz : ∀ j, raw30659step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30659step1 = (fun i j => raw30659step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30659step1 raw30659step0; decide +kernel
      have hl : raw30659step1Labels = raw30659step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30659step0 raw30659step0Labels permutation80 hz
    mixedMoment B raw30659step1 raw30659step1Labels = mixedMoment B raw30659step2 raw30659step2Labels := by
      have ha : raw30659step2 = (fun i j => raw30659step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30659step2 raw30659step1; decide +kernel
      have hl : raw30659step2Labels = raw30659step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30659step1 raw30659step1Labels permutation25 permutation5
    mixedMoment B raw30659step2 raw30659step2Labels = mixedMoment B raw30659step3 raw30659step3Labels := by
      have ha : raw30659step3 = raw30659step2 := by apply Matrix.ext; unfold raw30659step3 raw30659step2; decide +kernel
      have hl : raw30659step2Labels = labelEmbedding8 ∘ raw30659step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30659step2 raw30659step2Labels raw30659step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4383 node4383Labels := by rfl

def raw30660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -4, 1], ![2, 0, -2]]
def raw30660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![3, -4, 1], ![2, 0, -2]]
def raw30660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30660step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw30660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30660step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30660 raw30660Labels = mixedMoment B node4380 node4380Labels := by
  calc
    mixedMoment B raw30660 raw30660Labels = mixedMoment B raw30660step0 raw30660step0Labels := by
      have hz : ∀ j, raw30660 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30660step0 = (fun i j => raw30660 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30660step0 raw30660; decide +kernel
      have hl : raw30660step0Labels = raw30660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30660 raw30660Labels permutation434 hz
    mixedMoment B raw30660step0 raw30660step0Labels = mixedMoment B raw30660step1 raw30660step1Labels := by
      have ha : raw30660step1 = (fun i j => raw30660step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30660step1 raw30660step0; decide +kernel
      have hl : raw30660step1Labels = raw30660step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30660step0 raw30660step0Labels permutation125 permutation5
    mixedMoment B raw30660step1 raw30660step1Labels = mixedMoment B raw30660step2 raw30660step2Labels := by
      have ha : raw30660step2 = raw30660step1 := by apply Matrix.ext; unfold raw30660step2 raw30660step1; decide +kernel
      have hl : raw30660step1Labels = labelEmbedding8 ∘ raw30660step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30660step1 raw30660step1Labels raw30660step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4380 node4380Labels := by rfl

def raw30661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -4, 1], ![2, 0, -2]]
def raw30661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![3, -4, 1], ![2, 0, -2]]
def raw30661step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30661step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw30661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30661step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30661 raw30661Labels = mixedMoment B node4380 node4380Labels := by
  calc
    mixedMoment B raw30661 raw30661Labels = mixedMoment B raw30661step0 raw30661step0Labels := by
      have hz : ∀ j, raw30661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30661step0 = (fun i j => raw30661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30661step0 raw30661; decide +kernel
      have hl : raw30661step0Labels = raw30661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30661 raw30661Labels permutation346 hz
    mixedMoment B raw30661step0 raw30661step0Labels = mixedMoment B raw30661step1 raw30661step1Labels := by
      have ha : raw30661step1 = (fun i j => raw30661step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30661step1 raw30661step0; decide +kernel
      have hl : raw30661step1Labels = raw30661step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30661step0 raw30661step0Labels permutation125 permutation5
    mixedMoment B raw30661step1 raw30661step1Labels = mixedMoment B raw30661step2 raw30661step2Labels := by
      have ha : raw30661step2 = raw30661step1 := by apply Matrix.ext; unfold raw30661step2 raw30661step1; decide +kernel
      have hl : raw30661step1Labels = labelEmbedding8 ∘ raw30661step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30661step1 raw30661step1Labels raw30661step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4380 node4380Labels := by rfl

def raw30662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![1, 1, -2]]
def raw30662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -4, 1], ![1, 1, -2]]
def raw30662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30662step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![3, -4, 1], ![1, 1, -2]]
def raw30662step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30662step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30662step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw30662step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30662step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30662 raw30662Labels = mixedMoment B node4490 node4490Labels := by
  calc
    mixedMoment B raw30662 raw30662Labels = mixedMoment B raw30662step0 raw30662step0Labels := by
      have hz : ∀ j, raw30662 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30662step0 = (fun i j => raw30662 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30662step0 raw30662; decide +kernel
      have hl : raw30662step0Labels = raw30662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30662 raw30662Labels permutation434 hz
    mixedMoment B raw30662step0 raw30662step0Labels = mixedMoment B raw30662step1 raw30662step1Labels := by
      have hz : ∀ j, raw30662step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30662step1 = (fun i j => raw30662step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30662step1 raw30662step0; decide +kernel
      have hl : raw30662step1Labels = raw30662step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30662step0 raw30662step0Labels permutation80 hz
    mixedMoment B raw30662step1 raw30662step1Labels = mixedMoment B raw30662step2 raw30662step2Labels := by
      have ha : raw30662step2 = (fun i j => raw30662step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30662step2 raw30662step1; decide +kernel
      have hl : raw30662step2Labels = raw30662step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30662step1 raw30662step1Labels permutation25 permutation5
    mixedMoment B raw30662step2 raw30662step2Labels = mixedMoment B raw30662step3 raw30662step3Labels := by
      have ha : raw30662step3 = raw30662step2 := by apply Matrix.ext; unfold raw30662step3 raw30662step2; decide +kernel
      have hl : raw30662step2Labels = labelEmbedding8 ∘ raw30662step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30662step2 raw30662step2Labels raw30662step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4490 node4490Labels := by rfl

def raw30663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw30663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw30663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![2, -3, 1], ![3, -1, -2]]
def raw30663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30663step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 1, -3], ![3, -2, -1]]
def raw30663step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30663step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 1, -3], ![3, -2, -1]]
def raw30663step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30663 raw30663Labels = mixedMoment B node4925 node4925Labels := by
  calc
    mixedMoment B raw30663 raw30663Labels = mixedMoment B raw30663step0 raw30663step0Labels := by
      have hz : ∀ j, raw30663 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30663step0 = (fun i j => raw30663 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30663step0 raw30663; decide +kernel
      have hl : raw30663step0Labels = raw30663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30663 raw30663Labels permutation434 hz
    mixedMoment B raw30663step0 raw30663step0Labels = mixedMoment B raw30663step1 raw30663step1Labels := by
      have hz : ∀ j, raw30663step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30663step1 = (fun i j => raw30663step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30663step1 raw30663step0; decide +kernel
      have hl : raw30663step1Labels = raw30663step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30663step0 raw30663step0Labels permutation80 hz
    mixedMoment B raw30663step1 raw30663step1Labels = mixedMoment B raw30663step2 raw30663step2Labels := by
      have ha : raw30663step2 = (fun i j => raw30663step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30663step2 raw30663step1; decide +kernel
      have hl : raw30663step2Labels = raw30663step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30663step1 raw30663step1Labels permutation8 permutation3
    mixedMoment B raw30663step2 raw30663step2Labels = mixedMoment B raw30663step3 raw30663step3Labels := by
      have ha : raw30663step3 = raw30663step2 := by apply Matrix.ext; unfold raw30663step3 raw30663step2; decide +kernel
      have hl : raw30663step2Labels = labelEmbedding6 ∘ raw30663step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30663step2 raw30663step2Labels raw30663step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4925 node4925Labels := by rfl

def raw30664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw30664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw30664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 2, 1]]
def raw30664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw30664step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30664 raw30664Labels = mixedMoment B node4982 node4982Labels := by
  calc
    mixedMoment B raw30664 raw30664Labels = mixedMoment B raw30664step0 raw30664step0Labels := by
      have hz : ∀ j, raw30664 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30664step0 = (fun i j => raw30664 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30664step0 raw30664; decide +kernel
      have hl : raw30664step0Labels = raw30664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30664 raw30664Labels permutation434 hz
    mixedMoment B raw30664step0 raw30664step0Labels = mixedMoment B raw30664step1 raw30664step1Labels := by
      have ha : raw30664step1 = (fun i j => raw30664step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30664step1 raw30664step0; decide +kernel
      have hl : raw30664step1Labels = raw30664step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30664step0 raw30664step0Labels permutation149 permutation2
    mixedMoment B raw30664step1 raw30664step1Labels = mixedMoment B raw30664step2 raw30664step2Labels := by
      have ha : raw30664step2 = -raw30664step1 := by apply Matrix.ext; change ∀ i j, raw30664step2 i j = -(raw30664step1 i j); unfold raw30664step2 raw30664step1; decide +kernel
      have hl : raw30664step2Labels = raw30664step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4982 node4982Labels := by rfl

def raw30665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw30665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw30665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 2, 1]]
def raw30665step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw30665step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30665 raw30665Labels = mixedMoment B node4982 node4982Labels := by
  calc
    mixedMoment B raw30665 raw30665Labels = mixedMoment B raw30665step0 raw30665step0Labels := by
      have hz : ∀ j, raw30665 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30665step0 = (fun i j => raw30665 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30665step0 raw30665; decide +kernel
      have hl : raw30665step0Labels = raw30665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30665 raw30665Labels permutation346 hz
    mixedMoment B raw30665step0 raw30665step0Labels = mixedMoment B raw30665step1 raw30665step1Labels := by
      have ha : raw30665step1 = (fun i j => raw30665step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30665step1 raw30665step0; decide +kernel
      have hl : raw30665step1Labels = raw30665step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30665step0 raw30665step0Labels permutation149 permutation2
    mixedMoment B raw30665step1 raw30665step1Labels = mixedMoment B raw30665step2 raw30665step2Labels := by
      have ha : raw30665step2 = -raw30665step1 := by apply Matrix.ext; change ∀ i j, raw30665step2 i j = -(raw30665step1 i j); unfold raw30665step2 raw30665step1; decide +kernel
      have hl : raw30665step2Labels = raw30665step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4982 node4982Labels := by rfl

def raw30666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30666Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30666step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30666step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30666step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30666step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw30666step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30666step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30666step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30666 raw30666Labels = mixedMoment B node3397 node3397Labels := by
  calc
    mixedMoment B raw30666 raw30666Labels = mixedMoment B raw30666step0 raw30666step0Labels := by
      have hz : ∀ j, raw30666 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30666step0 = (fun i j => raw30666 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30666step0 raw30666; decide +kernel
      have hl : raw30666step0Labels = raw30666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30666 raw30666Labels permutation434 hz
    mixedMoment B raw30666step0 raw30666step0Labels = mixedMoment B raw30666step1 raw30666step1Labels := by
      have hz : ∀ j, raw30666step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30666step1 = (fun i j => raw30666step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30666step1 raw30666step0; decide +kernel
      have hl : raw30666step1Labels = raw30666step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30666step0 raw30666step0Labels permutation80 hz
    mixedMoment B raw30666step1 raw30666step1Labels = mixedMoment B raw30666step2 raw30666step2Labels := by
      have ha : raw30666step2 = (fun i j => raw30666step1 (permutation24 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30666step2 raw30666step1; decide +kernel
      have hl : raw30666step2Labels = raw30666step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30666step1 raw30666step1Labels permutation24 permutation3
    mixedMoment B raw30666step2 raw30666step2Labels = mixedMoment B raw30666step3 raw30666step3Labels := by
      have ha : raw30666step3 = -raw30666step2 := by apply Matrix.ext; change ∀ i j, raw30666step3 i j = -(raw30666step2 i j); unfold raw30666step3 raw30666step2; decide +kernel
      have hl : raw30666step3Labels = raw30666step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3397 node3397Labels := by rfl

def raw30667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30667Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30667step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw30667step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30667step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30667step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30667 raw30667Labels = mixedMoment B node3394 node3394Labels := by
  calc
    mixedMoment B raw30667 raw30667Labels = mixedMoment B raw30667step0 raw30667step0Labels := by
      have hz : ∀ j, raw30667 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30667step0 = (fun i j => raw30667 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30667step0 raw30667; decide +kernel
      have hl : raw30667step0Labels = raw30667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30667 raw30667Labels permutation434 hz
    mixedMoment B raw30667step0 raw30667step0Labels = mixedMoment B raw30667step1 raw30667step1Labels := by
      have ha : raw30667step1 = (fun i j => raw30667step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30667step1 raw30667step0; decide +kernel
      have hl : raw30667step1Labels = raw30667step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30667step0 raw30667step0Labels permutation125 permutation3
    mixedMoment B raw30667step1 raw30667step1Labels = mixedMoment B raw30667step2 raw30667step2Labels := by
      have ha : raw30667step2 = -raw30667step1 := by apply Matrix.ext; change ∀ i j, raw30667step2 i j = -(raw30667step1 i j); unfold raw30667step2 raw30667step1; decide +kernel
      have hl : raw30667step2Labels = raw30667step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3394 node3394Labels := by rfl

def raw30668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30668Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30668step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw30668step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30668step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30668 raw30668Labels = mixedMoment B node3394 node3394Labels := by
  calc
    mixedMoment B raw30668 raw30668Labels = mixedMoment B raw30668step0 raw30668step0Labels := by
      have hz : ∀ j, raw30668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30668step0 = (fun i j => raw30668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30668step0 raw30668; decide +kernel
      have hl : raw30668step0Labels = raw30668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30668 raw30668Labels permutation346 hz
    mixedMoment B raw30668step0 raw30668step0Labels = mixedMoment B raw30668step1 raw30668step1Labels := by
      have ha : raw30668step1 = (fun i j => raw30668step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30668step1 raw30668step0; decide +kernel
      have hl : raw30668step1Labels = raw30668step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30668step0 raw30668step0Labels permutation125 permutation3
    mixedMoment B raw30668step1 raw30668step1Labels = mixedMoment B raw30668step2 raw30668step2Labels := by
      have ha : raw30668step2 = -raw30668step1 := by apply Matrix.ext; change ∀ i j, raw30668step2 i j = -(raw30668step1 i j); unfold raw30668step2 raw30668step1; decide +kernel
      have hl : raw30668step2Labels = raw30668step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3394 node3394Labels := by rfl

def raw30669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw30669Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw30669step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30669step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw30669step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30669step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw30669step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30669step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30669step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30669 raw30669Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw30669 raw30669Labels = mixedMoment B raw30669step0 raw30669step0Labels := by
      have hz : ∀ j, raw30669 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30669step0 = (fun i j => raw30669 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30669step0 raw30669; decide +kernel
      have hl : raw30669step0Labels = raw30669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30669 raw30669Labels permutation434 hz
    mixedMoment B raw30669step0 raw30669step0Labels = mixedMoment B raw30669step1 raw30669step1Labels := by
      have hz : ∀ j, raw30669step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30669step1 = (fun i j => raw30669step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30669step1 raw30669step0; decide +kernel
      have hl : raw30669step1Labels = raw30669step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30669step0 raw30669step0Labels permutation80 hz
    mixedMoment B raw30669step1 raw30669step1Labels = mixedMoment B raw30669step2 raw30669step2Labels := by
      have ha : raw30669step2 = (fun i j => raw30669step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30669step2 raw30669step1; decide +kernel
      have hl : raw30669step2Labels = raw30669step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30669step1 raw30669step1Labels permutation25 permutation3
    mixedMoment B raw30669step2 raw30669step2Labels = mixedMoment B raw30669step3 raw30669step3Labels := by
      have ha : raw30669step3 = -raw30669step2 := by apply Matrix.ext; change ∀ i j, raw30669step3 i j = -(raw30669step2 i j); unfold raw30669step3 raw30669step2; decide +kernel
      have hl : raw30669step3Labels = raw30669step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3583 node3583Labels := by rfl

def raw30670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30670Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30670step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30670step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30670 raw30670Labels = mixedMoment B node2311 node2311Labels := by
  calc
    mixedMoment B raw30670 raw30670Labels = mixedMoment B raw30670step0 raw30670step0Labels := by
      have hz : ∀ j, raw30670 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30670step0 = (fun i j => raw30670 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30670step0 raw30670; decide +kernel
      have hl : raw30670step0Labels = raw30670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30670 raw30670Labels permutation434 hz
    mixedMoment B raw30670step0 raw30670step0Labels = mixedMoment B raw30670step1 raw30670step1Labels := by
      have ha : raw30670step1 = (fun i j => raw30670step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30670step1 raw30670step0; decide +kernel
      have hl : raw30670step1Labels = raw30670step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30670step0 raw30670step0Labels permutation33 permutation3
    _ = mixedMoment B node2311 node2311Labels := by rfl

def raw30671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30671Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30671step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30671 raw30671Labels = mixedMoment B node2417 node2417Labels := by
  calc
    mixedMoment B raw30671 raw30671Labels = mixedMoment B raw30671step0 raw30671step0Labels := by
      have ha : raw30671step0 = (fun i j => raw30671 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30671step0 raw30671; decide +kernel
      have hl : raw30671step0Labels = raw30671Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30671 raw30671Labels permutation159 permutation3
    _ = mixedMoment B node2417 node2417Labels := by rfl

def raw30672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw30672Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw30672step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30672step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30672 raw30672Labels = mixedMoment B node2504 node2504Labels := by
  calc
    mixedMoment B raw30672 raw30672Labels = mixedMoment B raw30672step0 raw30672step0Labels := by
      have hz : ∀ j, raw30672 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30672step0 = (fun i j => raw30672 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30672step0 raw30672; decide +kernel
      have hl : raw30672step0Labels = raw30672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30672 raw30672Labels permutation434 hz
    mixedMoment B raw30672step0 raw30672step0Labels = mixedMoment B raw30672step1 raw30672step1Labels := by
      have ha : raw30672step1 = (fun i j => raw30672step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30672step1 raw30672step0; decide +kernel
      have hl : raw30672step1Labels = raw30672step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30672step0 raw30672step0Labels permutation36 permutation3
    _ = mixedMoment B node2504 node2504Labels := by rfl

def raw30673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30673Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30673step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30673step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30673 raw30673Labels = mixedMoment B node2311 node2311Labels := by
  calc
    mixedMoment B raw30673 raw30673Labels = mixedMoment B raw30673step0 raw30673step0Labels := by
      have hz : ∀ j, raw30673 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30673step0 = (fun i j => raw30673 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30673step0 raw30673; decide +kernel
      have hl : raw30673step0Labels = raw30673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30673 raw30673Labels permutation346 hz
    mixedMoment B raw30673step0 raw30673step0Labels = mixedMoment B raw30673step1 raw30673step1Labels := by
      have ha : raw30673step1 = (fun i j => raw30673step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30673step1 raw30673step0; decide +kernel
      have hl : raw30673step1Labels = raw30673step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30673step0 raw30673step0Labels permutation33 permutation3
    _ = mixedMoment B node2311 node2311Labels := by rfl

def raw30674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw30674Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30674step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30674 raw30674Labels = mixedMoment B node2417 node2417Labels := by
  calc
    mixedMoment B raw30674 raw30674Labels = mixedMoment B raw30674step0 raw30674step0Labels := by
      have ha : raw30674step0 = (fun i j => raw30674 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30674step0 raw30674; decide +kernel
      have hl : raw30674step0Labels = raw30674Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30674 raw30674Labels permutation153 permutation3
    _ = mixedMoment B node2417 node2417Labels := by rfl

def raw30675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw30675Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw30675step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30675step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30675 raw30675Labels = mixedMoment B node2504 node2504Labels := by
  calc
    mixedMoment B raw30675 raw30675Labels = mixedMoment B raw30675step0 raw30675step0Labels := by
      have hz : ∀ j, raw30675 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30675step0 = (fun i j => raw30675 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30675step0 raw30675; decide +kernel
      have hl : raw30675step0Labels = raw30675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30675 raw30675Labels permutation346 hz
    mixedMoment B raw30675step0 raw30675step0Labels = mixedMoment B raw30675step1 raw30675step1Labels := by
      have ha : raw30675step1 = (fun i j => raw30675step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30675step1 raw30675step0; decide +kernel
      have hl : raw30675step1Labels = raw30675step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30675step0 raw30675step0Labels permutation36 permutation3
    _ = mixedMoment B node2504 node2504Labels := by rfl

def raw30676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![2, 0, -2]]
def raw30676Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![3, -4, 1], ![2, 0, -2]]
def raw30676step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![3, -4, 1], ![2, 0, -2]]
def raw30676step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30676step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-2, 0, 2], ![-3, 1, 2]]
def raw30676step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30676step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![2, 0, -2], ![3, -1, -2]]
def raw30676step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30676 raw30676Labels = mixedMoment B node1549 node1549Labels := by
  calc
    mixedMoment B raw30676 raw30676Labels = mixedMoment B raw30676step0 raw30676step0Labels := by
      have hz : ∀ j, raw30676 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30676step0 = (fun i j => raw30676 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30676step0 raw30676; decide +kernel
      have hl : raw30676step0Labels = raw30676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30676 raw30676Labels permutation434 hz
    mixedMoment B raw30676step0 raw30676step0Labels = mixedMoment B raw30676step1 raw30676step1Labels := by
      have hz : ∀ j, raw30676step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30676step1 = (fun i j => raw30676step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30676step1 raw30676step0; decide +kernel
      have hl : raw30676step1Labels = raw30676step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30676step0 raw30676step0Labels permutation80 hz
    mixedMoment B raw30676step1 raw30676step1Labels = mixedMoment B raw30676step2 raw30676step2Labels := by
      have ha : raw30676step2 = (fun i j => raw30676step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30676step2 raw30676step1; decide +kernel
      have hl : raw30676step2Labels = raw30676step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30676step1 raw30676step1Labels permutation25 permutation3
    mixedMoment B raw30676step2 raw30676step2Labels = mixedMoment B raw30676step3 raw30676step3Labels := by
      have ha : raw30676step3 = -raw30676step2 := by apply Matrix.ext; change ∀ i j, raw30676step3 i j = -(raw30676step2 i j); unfold raw30676step3 raw30676step2; decide +kernel
      have hl : raw30676step3Labels = raw30676step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1549 node1549Labels := by rfl

def raw30677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -4, 1], ![2, 0, -2]]
def raw30677Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![3, -4, 1], ![2, 0, -2]]
def raw30677step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30677step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw30677step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30677 raw30677Labels = mixedMoment B node1546 node1546Labels := by
  calc
    mixedMoment B raw30677 raw30677Labels = mixedMoment B raw30677step0 raw30677step0Labels := by
      have hz : ∀ j, raw30677 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30677step0 = (fun i j => raw30677 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30677step0 raw30677; decide +kernel
      have hl : raw30677step0Labels = raw30677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30677 raw30677Labels permutation434 hz
    mixedMoment B raw30677step0 raw30677step0Labels = mixedMoment B raw30677step1 raw30677step1Labels := by
      have ha : raw30677step1 = (fun i j => raw30677step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30677step1 raw30677step0; decide +kernel
      have hl : raw30677step1Labels = raw30677step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30677step0 raw30677step0Labels permutation125 permutation3
    mixedMoment B raw30677step1 raw30677step1Labels = mixedMoment B raw30677step2 raw30677step2Labels := by
      have ha : raw30677step2 = -raw30677step1 := by apply Matrix.ext; change ∀ i j, raw30677step2 i j = -(raw30677step1 i j); unfold raw30677step2 raw30677step1; decide +kernel
      have hl : raw30677step2Labels = raw30677step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1546 node1546Labels := by rfl

def raw30678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -4, 1], ![2, 0, -2]]
def raw30678Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![3, -4, 1], ![2, 0, -2]]
def raw30678step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30678step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30678step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw30678step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30678 raw30678Labels = mixedMoment B node1546 node1546Labels := by
  calc
    mixedMoment B raw30678 raw30678Labels = mixedMoment B raw30678step0 raw30678step0Labels := by
      have hz : ∀ j, raw30678 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30678step0 = (fun i j => raw30678 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30678step0 raw30678; decide +kernel
      have hl : raw30678step0Labels = raw30678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30678 raw30678Labels permutation346 hz
    mixedMoment B raw30678step0 raw30678step0Labels = mixedMoment B raw30678step1 raw30678step1Labels := by
      have ha : raw30678step1 = (fun i j => raw30678step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30678step1 raw30678step0; decide +kernel
      have hl : raw30678step1Labels = raw30678step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30678step0 raw30678step0Labels permutation125 permutation3
    mixedMoment B raw30678step1 raw30678step1Labels = mixedMoment B raw30678step2 raw30678step2Labels := by
      have ha : raw30678step2 = -raw30678step1 := by apply Matrix.ext; change ∀ i j, raw30678step2 i j = -(raw30678step1 i j); unfold raw30678step2 raw30678step1; decide +kernel
      have hl : raw30678step2Labels = raw30678step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1546 node1546Labels := by rfl

def raw30679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![1, 1, -2]]
def raw30679Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -4, 1], ![1, 1, -2]]
def raw30679step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![3, -4, 1], ![1, 1, -2]]
def raw30679step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30679step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30679step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30679step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw30679step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30679 raw30679Labels = mixedMoment B node1650 node1650Labels := by
  calc
    mixedMoment B raw30679 raw30679Labels = mixedMoment B raw30679step0 raw30679step0Labels := by
      have hz : ∀ j, raw30679 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30679step0 = (fun i j => raw30679 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30679step0 raw30679; decide +kernel
      have hl : raw30679step0Labels = raw30679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30679 raw30679Labels permutation434 hz
    mixedMoment B raw30679step0 raw30679step0Labels = mixedMoment B raw30679step1 raw30679step1Labels := by
      have hz : ∀ j, raw30679step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30679step1 = (fun i j => raw30679step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30679step1 raw30679step0; decide +kernel
      have hl : raw30679step1Labels = raw30679step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30679step0 raw30679step0Labels permutation80 hz
    mixedMoment B raw30679step1 raw30679step1Labels = mixedMoment B raw30679step2 raw30679step2Labels := by
      have ha : raw30679step2 = (fun i j => raw30679step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30679step2 raw30679step1; decide +kernel
      have hl : raw30679step2Labels = raw30679step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30679step1 raw30679step1Labels permutation25 permutation3
    mixedMoment B raw30679step2 raw30679step2Labels = mixedMoment B raw30679step3 raw30679step3Labels := by
      have ha : raw30679step3 = -raw30679step2 := by apply Matrix.ext; change ∀ i j, raw30679step3 i j = -(raw30679step2 i j); unfold raw30679step3 raw30679step2; decide +kernel
      have hl : raw30679step3Labels = raw30679step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1650 node1650Labels := by rfl

def raw30680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw30680Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw30680step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30680step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![2, -3, 1], ![3, -1, -2]]
def raw30680step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30680step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 1, -3], ![3, -2, -1]]
def raw30680step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30680 raw30680Labels = mixedMoment B node2315 node2315Labels := by
  calc
    mixedMoment B raw30680 raw30680Labels = mixedMoment B raw30680step0 raw30680step0Labels := by
      have hz : ∀ j, raw30680 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30680step0 = (fun i j => raw30680 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30680step0 raw30680; decide +kernel
      have hl : raw30680step0Labels = raw30680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30680 raw30680Labels permutation434 hz
    mixedMoment B raw30680step0 raw30680step0Labels = mixedMoment B raw30680step1 raw30680step1Labels := by
      have hz : ∀ j, raw30680step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30680step1 = (fun i j => raw30680step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30680step1 raw30680step0; decide +kernel
      have hl : raw30680step1Labels = raw30680step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30680step0 raw30680step0Labels permutation80 hz
    mixedMoment B raw30680step1 raw30680step1Labels = mixedMoment B raw30680step2 raw30680step2Labels := by
      have ha : raw30680step2 = (fun i j => raw30680step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30680step2 raw30680step1; decide +kernel
      have hl : raw30680step2Labels = raw30680step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30680step1 raw30680step1Labels permutation8 permutation3
    _ = mixedMoment B node2315 node2315Labels := by rfl

def raw30681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![3, -1, -2]]
def raw30681Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw30681step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw30681step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30681 raw30681Labels = mixedMoment B node2421 node2421Labels := by
  calc
    mixedMoment B raw30681 raw30681Labels = mixedMoment B raw30681step0 raw30681step0Labels := by
      have hz : ∀ j, raw30681 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30681step0 = (fun i j => raw30681 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30681step0 raw30681; decide +kernel
      have hl : raw30681step0Labels = raw30681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30681 raw30681Labels permutation434 hz
    mixedMoment B raw30681step0 raw30681step0Labels = mixedMoment B raw30681step1 raw30681step1Labels := by
      have ha : raw30681step1 = (fun i j => raw30681step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30681step1 raw30681step0; decide +kernel
      have hl : raw30681step1Labels = raw30681step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30681step0 raw30681step0Labels permutation32 permutation3
    _ = mixedMoment B node2421 node2421Labels := by rfl

def raw30682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw30682Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![3, -1, -2]]
def raw30682step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw30682step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30682 raw30682Labels = mixedMoment B node2421 node2421Labels := by
  calc
    mixedMoment B raw30682 raw30682Labels = mixedMoment B raw30682step0 raw30682step0Labels := by
      have hz : ∀ j, raw30682 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30682step0 = (fun i j => raw30682 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30682step0 raw30682; decide +kernel
      have hl : raw30682step0Labels = raw30682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30682 raw30682Labels permutation346 hz
    mixedMoment B raw30682step0 raw30682step0Labels = mixedMoment B raw30682step1 raw30682step1Labels := by
      have ha : raw30682step1 = (fun i j => raw30682step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30682step1 raw30682step0; decide +kernel
      have hl : raw30682step1Labels = raw30682step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30682step0 raw30682step0Labels permutation32 permutation3
    _ = mixedMoment B node2421 node2421Labels := by rfl

def raw30683 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30683step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![1, -3, 2], ![-2, 0, 2]]
def raw30683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30683step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw30683step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30683step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw30683step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30683 raw30683Labels = mixedMoment B node5206 node5206Labels := by
  calc
    mixedMoment B raw30683 raw30683Labels = mixedMoment B raw30683step0 raw30683step0Labels := by
      have hz : ∀ j, raw30683 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30683step0 = (fun i j => raw30683 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30683step0 raw30683; decide +kernel
      have hl : raw30683step0Labels = raw30683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30683 raw30683Labels permutation434 hz
    mixedMoment B raw30683step0 raw30683step0Labels = mixedMoment B raw30683step1 raw30683step1Labels := by
      have hz : ∀ j, raw30683step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30683step1 = (fun i j => raw30683step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30683step1 raw30683step0; decide +kernel
      have hl : raw30683step1Labels = raw30683step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30683step0 raw30683step0Labels permutation80 hz
    mixedMoment B raw30683step1 raw30683step1Labels = mixedMoment B raw30683step2 raw30683step2Labels := by
      have ha : raw30683step2 = (fun i j => raw30683step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30683step2 raw30683step1; decide +kernel
      have hl : raw30683step2Labels = raw30683step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30683step1 raw30683step1Labels permutation8 permutation7
    mixedMoment B raw30683step2 raw30683step2Labels = mixedMoment B raw30683step3 raw30683step3Labels := by
      have ha : raw30683step3 = raw30683step2 := by apply Matrix.ext; unfold raw30683step3 raw30683step2; decide +kernel
      have hl : raw30683step2Labels = labelEmbedding10 ∘ raw30683step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30683step2 raw30683step2Labels raw30683step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5206 node5206Labels := by rfl

def raw30684 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw30684step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30684step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw30684step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30684 raw30684Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw30684 raw30684Labels = mixedMoment B raw30684step0 raw30684step0Labels := by
      have hz : ∀ j, raw30684 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30684step0 = (fun i j => raw30684 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30684step0 raw30684; decide +kernel
      have hl : raw30684step0Labels = raw30684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30684 raw30684Labels permutation434 hz
    mixedMoment B raw30684step0 raw30684step0Labels = mixedMoment B raw30684step1 raw30684step1Labels := by
      have ha : raw30684step1 = (fun i j => raw30684step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30684step1 raw30684step0; decide +kernel
      have hl : raw30684step1Labels = raw30684step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30684step0 raw30684step0Labels permutation32 permutation7
    mixedMoment B raw30684step1 raw30684step1Labels = mixedMoment B raw30684step2 raw30684step2Labels := by
      have ha : raw30684step2 = raw30684step1 := by apply Matrix.ext; unfold raw30684step2 raw30684step1; decide +kernel
      have hl : raw30684step1Labels = labelEmbedding10 ∘ raw30684step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30684step1 raw30684step1Labels raw30684step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5151 node5151Labels := by rfl

def raw30685 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw30685step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30685step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw30685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30685 raw30685Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw30685 raw30685Labels = mixedMoment B raw30685step0 raw30685step0Labels := by
      have hz : ∀ j, raw30685 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30685step0 = (fun i j => raw30685 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30685step0 raw30685; decide +kernel
      have hl : raw30685step0Labels = raw30685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30685 raw30685Labels permutation346 hz
    mixedMoment B raw30685step0 raw30685step0Labels = mixedMoment B raw30685step1 raw30685step1Labels := by
      have ha : raw30685step1 = (fun i j => raw30685step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30685step1 raw30685step0; decide +kernel
      have hl : raw30685step1Labels = raw30685step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30685step0 raw30685step0Labels permutation32 permutation7
    mixedMoment B raw30685step1 raw30685step1Labels = mixedMoment B raw30685step2 raw30685step2Labels := by
      have ha : raw30685step2 = raw30685step1 := by apply Matrix.ext; unfold raw30685step2 raw30685step1; decide +kernel
      have hl : raw30685step1Labels = labelEmbedding10 ∘ raw30685step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30685step1 raw30685step1Labels raw30685step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5151 node5151Labels := by rfl

def raw30686 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw30686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw30686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -3, 2], ![-3, 1, 2]]
def raw30686step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30686step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw30686step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30686step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw30686step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30686 raw30686Labels = mixedMoment B node5175 node5175Labels := by
  calc
    mixedMoment B raw30686 raw30686Labels = mixedMoment B raw30686step0 raw30686step0Labels := by
      have hz : ∀ j, raw30686 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30686step0 = (fun i j => raw30686 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30686step0 raw30686; decide +kernel
      have hl : raw30686step0Labels = raw30686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30686 raw30686Labels permutation434 hz
    mixedMoment B raw30686step0 raw30686step0Labels = mixedMoment B raw30686step1 raw30686step1Labels := by
      have hz : ∀ j, raw30686step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30686step1 = (fun i j => raw30686step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30686step1 raw30686step0; decide +kernel
      have hl : raw30686step1Labels = raw30686step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30686step0 raw30686step0Labels permutation80 hz
    mixedMoment B raw30686step1 raw30686step1Labels = mixedMoment B raw30686step2 raw30686step2Labels := by
      have ha : raw30686step2 = (fun i j => raw30686step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30686step2 raw30686step1; decide +kernel
      have hl : raw30686step2Labels = raw30686step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30686step1 raw30686step1Labels permutation8 permutation7
    mixedMoment B raw30686step2 raw30686step2Labels = mixedMoment B raw30686step3 raw30686step3Labels := by
      have ha : raw30686step3 = raw30686step2 := by apply Matrix.ext; unfold raw30686step3 raw30686step2; decide +kernel
      have hl : raw30686step2Labels = labelEmbedding10 ∘ raw30686step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30686step2 raw30686step2Labels raw30686step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5175 node5175Labels := by rfl

def raw30687 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30687step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -3, 2], ![-2, 0, 2]]
def raw30687step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30687step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw30687step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30687step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw30687step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30687 raw30687Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw30687 raw30687Labels = mixedMoment B raw30687step0 raw30687step0Labels := by
      have hz : ∀ j, raw30687 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30687step0 = (fun i j => raw30687 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30687step0 raw30687; decide +kernel
      have hl : raw30687step0Labels = raw30687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30687 raw30687Labels permutation434 hz
    mixedMoment B raw30687step0 raw30687step0Labels = mixedMoment B raw30687step1 raw30687step1Labels := by
      have hz : ∀ j, raw30687step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30687step1 = (fun i j => raw30687step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30687step1 raw30687step0; decide +kernel
      have hl : raw30687step1Labels = raw30687step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30687step0 raw30687step0Labels permutation80 hz
    mixedMoment B raw30687step1 raw30687step1Labels = mixedMoment B raw30687step2 raw30687step2Labels := by
      have ha : raw30687step2 = (fun i j => raw30687step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30687step2 raw30687step1; decide +kernel
      have hl : raw30687step2Labels = raw30687step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30687step1 raw30687step1Labels permutation9 permutation6
    mixedMoment B raw30687step2 raw30687step2Labels = mixedMoment B raw30687step3 raw30687step3Labels := by
      have ha : raw30687step3 = raw30687step2 := by apply Matrix.ext; unfold raw30687step3 raw30687step2; decide +kernel
      have hl : raw30687step2Labels = labelEmbedding9 ∘ raw30687step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30687step2 raw30687step2Labels raw30687step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4845 node4845Labels := by rfl

def raw30688 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw30688step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30688step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw30688step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30688 raw30688Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw30688 raw30688Labels = mixedMoment B raw30688step0 raw30688step0Labels := by
      have hz : ∀ j, raw30688 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30688step0 = (fun i j => raw30688 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30688step0 raw30688; decide +kernel
      have hl : raw30688step0Labels = raw30688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30688 raw30688Labels permutation434 hz
    mixedMoment B raw30688step0 raw30688step0Labels = mixedMoment B raw30688step1 raw30688step1Labels := by
      have ha : raw30688step1 = (fun i j => raw30688step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30688step1 raw30688step0; decide +kernel
      have hl : raw30688step1Labels = raw30688step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30688step0 raw30688step0Labels permutation33 permutation6
    mixedMoment B raw30688step1 raw30688step1Labels = mixedMoment B raw30688step2 raw30688step2Labels := by
      have ha : raw30688step2 = raw30688step1 := by apply Matrix.ext; unfold raw30688step2 raw30688step1; decide +kernel
      have hl : raw30688step1Labels = labelEmbedding9 ∘ raw30688step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30688step1 raw30688step1Labels raw30688step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5140 node5140Labels := by rfl

def raw30689 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw30689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw30689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30689step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -3, 2], ![-3, 1, 2]]
def raw30689step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30689step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw30689step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30689step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw30689step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30689 raw30689Labels = mixedMoment B node5175 node5175Labels := by
  calc
    mixedMoment B raw30689 raw30689Labels = mixedMoment B raw30689step0 raw30689step0Labels := by
      have hz : ∀ j, raw30689 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30689step0 = (fun i j => raw30689 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30689step0 raw30689; decide +kernel
      have hl : raw30689step0Labels = raw30689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30689 raw30689Labels permutation434 hz
    mixedMoment B raw30689step0 raw30689step0Labels = mixedMoment B raw30689step1 raw30689step1Labels := by
      have hz : ∀ j, raw30689step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30689step1 = (fun i j => raw30689step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30689step1 raw30689step0; decide +kernel
      have hl : raw30689step1Labels = raw30689step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30689step0 raw30689step0Labels permutation80 hz
    mixedMoment B raw30689step1 raw30689step1Labels = mixedMoment B raw30689step2 raw30689step2Labels := by
      have ha : raw30689step2 = (fun i j => raw30689step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30689step2 raw30689step1; decide +kernel
      have hl : raw30689step2Labels = raw30689step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30689step1 raw30689step1Labels permutation9 permutation6
    mixedMoment B raw30689step2 raw30689step2Labels = mixedMoment B raw30689step3 raw30689step3Labels := by
      have ha : raw30689step3 = raw30689step2 := by apply Matrix.ext; unfold raw30689step3 raw30689step2; decide +kernel
      have hl : raw30689step2Labels = labelEmbedding9 ∘ raw30689step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30689step2 raw30689step2Labels raw30689step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5175 node5175Labels := by rfl

def raw30690 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30690step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30690step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30690step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30690 raw30690Labels = mixedMoment B node4744 node4744Labels := by
  calc
    mixedMoment B raw30690 raw30690Labels = mixedMoment B raw30690step0 raw30690step0Labels := by
      have hz : ∀ j, raw30690 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30690step0 = (fun i j => raw30690 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30690step0 raw30690; decide +kernel
      have hl : raw30690step0Labels = raw30690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30690 raw30690Labels permutation346 hz
    mixedMoment B raw30690step0 raw30690step0Labels = mixedMoment B raw30690step1 raw30690step1Labels := by
      have ha : raw30690step1 = (fun i j => raw30690step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30690step1 raw30690step0; decide +kernel
      have hl : raw30690step1Labels = raw30690step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30690step0 raw30690step0Labels permutation33 permutation6
    mixedMoment B raw30690step1 raw30690step1Labels = mixedMoment B raw30690step2 raw30690step2Labels := by
      have ha : raw30690step2 = raw30690step1 := by apply Matrix.ext; unfold raw30690step2 raw30690step1; decide +kernel
      have hl : raw30690step1Labels = labelEmbedding9 ∘ raw30690step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30690step1 raw30690step1Labels raw30690step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4744 node4744Labels := by rfl

def raw30691 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30691step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30691step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30691step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30691 raw30691Labels = mixedMoment B node5002 node5002Labels := by
  calc
    mixedMoment B raw30691 raw30691Labels = mixedMoment B raw30691step0 raw30691step0Labels := by
      have hz : ∀ j, raw30691 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30691step0 = (fun i j => raw30691 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30691step0 raw30691; decide +kernel
      have hl : raw30691step0Labels = raw30691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30691 raw30691Labels permutation346 hz
    mixedMoment B raw30691step0 raw30691step0Labels = mixedMoment B raw30691step1 raw30691step1Labels := by
      have ha : raw30691step1 = (fun i j => raw30691step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30691step1 raw30691step0; decide +kernel
      have hl : raw30691step1Labels = raw30691step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30691step0 raw30691step0Labels permutation33 permutation6
    mixedMoment B raw30691step1 raw30691step1Labels = mixedMoment B raw30691step2 raw30691step2Labels := by
      have ha : raw30691step2 = raw30691step1 := by apply Matrix.ext; unfold raw30691step2 raw30691step1; decide +kernel
      have hl : raw30691step1Labels = labelEmbedding9 ∘ raw30691step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30691step1 raw30691step1Labels raw30691step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5002 node5002Labels := by rfl

def raw30692 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30692step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30692step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30692step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30692 raw30692Labels = mixedMoment B node5049 node5049Labels := by
  calc
    mixedMoment B raw30692 raw30692Labels = mixedMoment B raw30692step0 raw30692step0Labels := by
      have ha : raw30692step0 = (fun i j => raw30692 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30692step0 raw30692; decide +kernel
      have hl : raw30692step0Labels = raw30692Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30692 raw30692Labels permutation153 permutation6
    mixedMoment B raw30692step0 raw30692step0Labels = mixedMoment B raw30692step1 raw30692step1Labels := by
      have ha : raw30692step1 = raw30692step0 := by apply Matrix.ext; unfold raw30692step1 raw30692step0; decide +kernel
      have hl : raw30692step0Labels = labelEmbedding9 ∘ raw30692step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30692step0 raw30692step0Labels raw30692step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5049 node5049Labels := by rfl

def raw30693 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw30693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw30693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw30693step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30693step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw30693step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30693 raw30693Labels = mixedMoment B node5079 node5079Labels := by
  calc
    mixedMoment B raw30693 raw30693Labels = mixedMoment B raw30693step0 raw30693step0Labels := by
      have hz : ∀ j, raw30693 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30693step0 = (fun i j => raw30693 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30693step0 raw30693; decide +kernel
      have hl : raw30693step0Labels = raw30693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30693 raw30693Labels permutation346 hz
    mixedMoment B raw30693step0 raw30693step0Labels = mixedMoment B raw30693step1 raw30693step1Labels := by
      have ha : raw30693step1 = (fun i j => raw30693step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30693step1 raw30693step0; decide +kernel
      have hl : raw30693step1Labels = raw30693step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30693step0 raw30693step0Labels permutation33 permutation6
    mixedMoment B raw30693step1 raw30693step1Labels = mixedMoment B raw30693step2 raw30693step2Labels := by
      have ha : raw30693step2 = raw30693step1 := by apply Matrix.ext; unfold raw30693step2 raw30693step1; decide +kernel
      have hl : raw30693step1Labels = labelEmbedding9 ∘ raw30693step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30693step1 raw30693step1Labels raw30693step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5079 node5079Labels := by rfl

def raw30694 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw30694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw30694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30694step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -4, 2], ![-2, 0, 2]]
def raw30694step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30694step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw30694step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30694step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw30694step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30694 raw30694Labels = mixedMoment B node4572 node4572Labels := by
  calc
    mixedMoment B raw30694 raw30694Labels = mixedMoment B raw30694step0 raw30694step0Labels := by
      have hz : ∀ j, raw30694 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30694step0 = (fun i j => raw30694 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30694step0 raw30694; decide +kernel
      have hl : raw30694step0Labels = raw30694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30694 raw30694Labels permutation434 hz
    mixedMoment B raw30694step0 raw30694step0Labels = mixedMoment B raw30694step1 raw30694step1Labels := by
      have hz : ∀ j, raw30694step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30694step1 = (fun i j => raw30694step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30694step1 raw30694step0; decide +kernel
      have hl : raw30694step1Labels = raw30694step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30694step0 raw30694step0Labels permutation80 hz
    mixedMoment B raw30694step1 raw30694step1Labels = mixedMoment B raw30694step2 raw30694step2Labels := by
      have ha : raw30694step2 = (fun i j => raw30694step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30694step2 raw30694step1; decide +kernel
      have hl : raw30694step2Labels = raw30694step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30694step1 raw30694step1Labels permutation25 permutation4
    mixedMoment B raw30694step2 raw30694step2Labels = mixedMoment B raw30694step3 raw30694step3Labels := by
      have ha : raw30694step3 = raw30694step2 := by apply Matrix.ext; unfold raw30694step3 raw30694step2; decide +kernel
      have hl : raw30694step2Labels = labelEmbedding7 ∘ raw30694step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30694step2 raw30694step2Labels raw30694step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4572 node4572Labels := by rfl

def raw30695 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw30695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw30695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![2, -4, 2], ![-2, 0, 2]]
def raw30695step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30695step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw30695step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30695step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw30695step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30695 raw30695Labels = mixedMoment B node4574 node4574Labels := by
  calc
    mixedMoment B raw30695 raw30695Labels = mixedMoment B raw30695step0 raw30695step0Labels := by
      have hz : ∀ j, raw30695 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30695step0 = (fun i j => raw30695 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30695step0 raw30695; decide +kernel
      have hl : raw30695step0Labels = raw30695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30695 raw30695Labels permutation434 hz
    mixedMoment B raw30695step0 raw30695step0Labels = mixedMoment B raw30695step1 raw30695step1Labels := by
      have hz : ∀ j, raw30695step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30695step1 = (fun i j => raw30695step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30695step1 raw30695step0; decide +kernel
      have hl : raw30695step1Labels = raw30695step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30695step0 raw30695step0Labels permutation80 hz
    mixedMoment B raw30695step1 raw30695step1Labels = mixedMoment B raw30695step2 raw30695step2Labels := by
      have ha : raw30695step2 = (fun i j => raw30695step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30695step2 raw30695step1; decide +kernel
      have hl : raw30695step2Labels = raw30695step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30695step1 raw30695step1Labels permutation25 permutation4
    mixedMoment B raw30695step2 raw30695step2Labels = mixedMoment B raw30695step3 raw30695step3Labels := by
      have ha : raw30695step3 = raw30695step2 := by apply Matrix.ext; unfold raw30695step3 raw30695step2; decide +kernel
      have hl : raw30695step2Labels = labelEmbedding7 ∘ raw30695step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30695step2 raw30695step2Labels raw30695step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4574 node4574Labels := by rfl

def raw30696 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw30696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw30696step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw30696step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30696step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw30696step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30696 raw30696Labels = mixedMoment B node4567 node4567Labels := by
  calc
    mixedMoment B raw30696 raw30696Labels = mixedMoment B raw30696step0 raw30696step0Labels := by
      have hz : ∀ j, raw30696 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30696step0 = (fun i j => raw30696 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30696step0 raw30696; decide +kernel
      have hl : raw30696step0Labels = raw30696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30696 raw30696Labels permutation434 hz
    mixedMoment B raw30696step0 raw30696step0Labels = mixedMoment B raw30696step1 raw30696step1Labels := by
      have ha : raw30696step1 = (fun i j => raw30696step0 (permutation127 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30696step1 raw30696step0; decide +kernel
      have hl : raw30696step1Labels = raw30696step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30696step0 raw30696step0Labels permutation127 permutation4
    mixedMoment B raw30696step1 raw30696step1Labels = mixedMoment B raw30696step2 raw30696step2Labels := by
      have ha : raw30696step2 = raw30696step1 := by apply Matrix.ext; unfold raw30696step2 raw30696step1; decide +kernel
      have hl : raw30696step1Labels = labelEmbedding7 ∘ raw30696step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30696step1 raw30696step1Labels raw30696step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4567 node4567Labels := by rfl

def raw30697 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw30697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![2, -4, 2], ![-2, 0, 2]]
def raw30697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw30697step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw30697step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30697 raw30697Labels = mixedMoment B node4567 node4567Labels := by
  calc
    mixedMoment B raw30697 raw30697Labels = mixedMoment B raw30697step0 raw30697step0Labels := by
      have hz : ∀ j, raw30697 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30697step0 = (fun i j => raw30697 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30697step0 raw30697; decide +kernel
      have hl : raw30697step0Labels = raw30697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30697 raw30697Labels permutation346 hz
    mixedMoment B raw30697step0 raw30697step0Labels = mixedMoment B raw30697step1 raw30697step1Labels := by
      have ha : raw30697step1 = (fun i j => raw30697step0 (permutation127 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30697step1 raw30697step0; decide +kernel
      have hl : raw30697step1Labels = raw30697step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30697step0 raw30697step0Labels permutation127 permutation4
    mixedMoment B raw30697step1 raw30697step1Labels = mixedMoment B raw30697step2 raw30697step2Labels := by
      have ha : raw30697step2 = raw30697step1 := by apply Matrix.ext; unfold raw30697step2 raw30697step1; decide +kernel
      have hl : raw30697step1Labels = labelEmbedding7 ∘ raw30697step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30697step1 raw30697step1Labels raw30697step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4567 node4567Labels := by rfl

def raw30698 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![-3, 1, 2]]
def raw30698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![2, -4, 2], ![-3, 1, 2]]
def raw30698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -4, 2], ![-3, 1, 2]]
def raw30698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw30698step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30698step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw30698step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30698 raw30698Labels = mixedMoment B node4614 node4614Labels := by
  calc
    mixedMoment B raw30698 raw30698Labels = mixedMoment B raw30698step0 raw30698step0Labels := by
      have hz : ∀ j, raw30698 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30698step0 = (fun i j => raw30698 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30698step0 raw30698; decide +kernel
      have hl : raw30698step0Labels = raw30698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30698 raw30698Labels permutation434 hz
    mixedMoment B raw30698step0 raw30698step0Labels = mixedMoment B raw30698step1 raw30698step1Labels := by
      have hz : ∀ j, raw30698step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30698step1 = (fun i j => raw30698step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30698step1 raw30698step0; decide +kernel
      have hl : raw30698step1Labels = raw30698step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30698step0 raw30698step0Labels permutation80 hz
    mixedMoment B raw30698step1 raw30698step1Labels = mixedMoment B raw30698step2 raw30698step2Labels := by
      have ha : raw30698step2 = (fun i j => raw30698step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30698step2 raw30698step1; decide +kernel
      have hl : raw30698step2Labels = raw30698step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30698step1 raw30698step1Labels permutation25 permutation4
    mixedMoment B raw30698step2 raw30698step2Labels = mixedMoment B raw30698step3 raw30698step3Labels := by
      have ha : raw30698step3 = raw30698step2 := by apply Matrix.ext; unfold raw30698step3 raw30698step2; decide +kernel
      have hl : raw30698step2Labels = labelEmbedding7 ∘ raw30698step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30698step2 raw30698step2Labels raw30698step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4614 node4614Labels := by rfl

def raw30699 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw30699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw30699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30699step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -3, 2], ![-1, -1, 2]]
def raw30699step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30699step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw30699step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30699step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw30699step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30699step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw30699step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30699 raw30699Labels = mixedMoment B node4753 node4753Labels := by
  calc
    mixedMoment B raw30699 raw30699Labels = mixedMoment B raw30699step0 raw30699step0Labels := by
      have hz : ∀ j, raw30699 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30699step0 = (fun i j => raw30699 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30699step0 raw30699; decide +kernel
      have hl : raw30699step0Labels = raw30699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30699 raw30699Labels permutation434 hz
    mixedMoment B raw30699step0 raw30699step0Labels = mixedMoment B raw30699step1 raw30699step1Labels := by
      have hz : ∀ j, raw30699step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30699step1 = (fun i j => raw30699step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30699step1 raw30699step0; decide +kernel
      have hl : raw30699step1Labels = raw30699step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30699step0 raw30699step0Labels permutation80 hz
    mixedMoment B raw30699step1 raw30699step1Labels = mixedMoment B raw30699step2 raw30699step2Labels := by
      have ha : raw30699step2 = (fun i j => raw30699step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30699step2 raw30699step1; decide +kernel
      have hl : raw30699step2Labels = raw30699step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30699step1 raw30699step1Labels permutation9 permutation4
    mixedMoment B raw30699step2 raw30699step2Labels = mixedMoment B raw30699step3 raw30699step3Labels := by
      have ha : raw30699step3 = -raw30699step2 := by apply Matrix.ext; change ∀ i j, raw30699step3 i j = -(raw30699step2 i j); unfold raw30699step3 raw30699step2; decide +kernel
      have hl : raw30699step3Labels = raw30699step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30699step3 raw30699step3Labels = mixedMoment B raw30699step4 raw30699step4Labels := by
      have ha : raw30699step4 = raw30699step3 := by apply Matrix.ext; unfold raw30699step4 raw30699step3; decide +kernel
      have hl : raw30699step3Labels = labelEmbedding7 ∘ raw30699step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30699step3 raw30699step3Labels raw30699step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4753 node4753Labels := by rfl

def raw30700 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw30700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw30700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30700step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -3, 2], ![-1, -1, 2]]
def raw30700step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30700step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw30700step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30700step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw30700step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30700 raw30700Labels = mixedMoment B node5023 node5023Labels := by
  calc
    mixedMoment B raw30700 raw30700Labels = mixedMoment B raw30700step0 raw30700step0Labels := by
      have hz : ∀ j, raw30700 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30700step0 = (fun i j => raw30700 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30700step0 raw30700; decide +kernel
      have hl : raw30700step0Labels = raw30700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30700 raw30700Labels permutation434 hz
    mixedMoment B raw30700step0 raw30700step0Labels = mixedMoment B raw30700step1 raw30700step1Labels := by
      have hz : ∀ j, raw30700step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30700step1 = (fun i j => raw30700step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30700step1 raw30700step0; decide +kernel
      have hl : raw30700step1Labels = raw30700step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30700step0 raw30700step0Labels permutation80 hz
    mixedMoment B raw30700step1 raw30700step1Labels = mixedMoment B raw30700step2 raw30700step2Labels := by
      have ha : raw30700step2 = (fun i j => raw30700step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30700step2 raw30700step1; decide +kernel
      have hl : raw30700step2Labels = raw30700step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30700step1 raw30700step1Labels permutation25 permutation4
    mixedMoment B raw30700step2 raw30700step2Labels = mixedMoment B raw30700step3 raw30700step3Labels := by
      have ha : raw30700step3 = raw30700step2 := by apply Matrix.ext; unfold raw30700step3 raw30700step2; decide +kernel
      have hl : raw30700step2Labels = labelEmbedding7 ∘ raw30700step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30700step2 raw30700step2Labels raw30700step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5023 node5023Labels := by rfl

def raw30701 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw30701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw30701step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw30701step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30701step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw30701step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30701 raw30701Labels = mixedMoment B node5014 node5014Labels := by
  calc
    mixedMoment B raw30701 raw30701Labels = mixedMoment B raw30701step0 raw30701step0Labels := by
      have hz : ∀ j, raw30701 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30701step0 = (fun i j => raw30701 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30701step0 raw30701; decide +kernel
      have hl : raw30701step0Labels = raw30701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30701 raw30701Labels permutation434 hz
    mixedMoment B raw30701step0 raw30701step0Labels = mixedMoment B raw30701step1 raw30701step1Labels := by
      have ha : raw30701step1 = (fun i j => raw30701step0 (permutation127 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30701step1 raw30701step0; decide +kernel
      have hl : raw30701step1Labels = raw30701step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30701step0 raw30701step0Labels permutation127 permutation4
    mixedMoment B raw30701step1 raw30701step1Labels = mixedMoment B raw30701step2 raw30701step2Labels := by
      have ha : raw30701step2 = raw30701step1 := by apply Matrix.ext; unfold raw30701step2 raw30701step1; decide +kernel
      have hl : raw30701step1Labels = labelEmbedding7 ∘ raw30701step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30701step1 raw30701step1Labels raw30701step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5014 node5014Labels := by rfl

def raw30702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30702step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30702step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30702step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30702 raw30702Labels = mixedMoment B node5371 node5371Labels := by
  calc
    mixedMoment B raw30702 raw30702Labels = mixedMoment B raw30702step0 raw30702step0Labels := by
      have hz : ∀ j, raw30702 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30702step0 = (fun i j => raw30702 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30702step0 raw30702; decide +kernel
      have hl : raw30702step0Labels = raw30702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30702 raw30702Labels permutation434 hz
    mixedMoment B raw30702step0 raw30702step0Labels = mixedMoment B raw30702step1 raw30702step1Labels := by
      have hz : ∀ j, raw30702step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30702step1 = (fun i j => raw30702step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30702step1 raw30702step0; decide +kernel
      have hl : raw30702step1Labels = raw30702step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30702step0 raw30702step0Labels permutation80 hz
    mixedMoment B raw30702step1 raw30702step1Labels = mixedMoment B raw30702step2 raw30702step2Labels := by
      have ha : raw30702step2 = (fun i j => raw30702step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30702step2 raw30702step1; decide +kernel
      have hl : raw30702step2Labels = raw30702step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30702step1 raw30702step1Labels permutation9 permutation2
    _ = mixedMoment B node5371 node5371Labels := by rfl

def raw30703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw30703step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30703step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30703 raw30703Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw30703 raw30703Labels = mixedMoment B raw30703step0 raw30703step0Labels := by
      have hz : ∀ j, raw30703 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30703step0 = (fun i j => raw30703 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30703step0 raw30703; decide +kernel
      have hl : raw30703step0Labels = raw30703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30703 raw30703Labels permutation434 hz
    mixedMoment B raw30703step0 raw30703step0Labels = mixedMoment B raw30703step1 raw30703step1Labels := by
      have ha : raw30703step1 = (fun i j => raw30703step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30703step1 raw30703step0; decide +kernel
      have hl : raw30703step1Labels = raw30703step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30703step0 raw30703step0Labels permutation127 permutation2
    mixedMoment B raw30703step1 raw30703step1Labels = mixedMoment B raw30703step2 raw30703step2Labels := by
      have ha : raw30703step2 = -raw30703step1 := by apply Matrix.ext; change ∀ i j, raw30703step2 i j = -(raw30703step1 i j); unfold raw30703step2 raw30703step1; decide +kernel
      have hl : raw30703step2Labels = raw30703step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw30704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30704step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw30704step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30704step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30704step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30704 raw30704Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw30704 raw30704Labels = mixedMoment B raw30704step0 raw30704step0Labels := by
      have hz : ∀ j, raw30704 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30704step0 = (fun i j => raw30704 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30704step0 raw30704; decide +kernel
      have hl : raw30704step0Labels = raw30704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30704 raw30704Labels permutation346 hz
    mixedMoment B raw30704step0 raw30704step0Labels = mixedMoment B raw30704step1 raw30704step1Labels := by
      have ha : raw30704step1 = (fun i j => raw30704step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30704step1 raw30704step0; decide +kernel
      have hl : raw30704step1Labels = raw30704step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30704step0 raw30704step0Labels permutation127 permutation2
    mixedMoment B raw30704step1 raw30704step1Labels = mixedMoment B raw30704step2 raw30704step2Labels := by
      have ha : raw30704step2 = -raw30704step1 := by apply Matrix.ext; change ∀ i j, raw30704step2 i j = -(raw30704step1 i j); unfold raw30704step2 raw30704step1; decide +kernel
      have hl : raw30704step2Labels = raw30704step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw30705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30705step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw30705step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30705 raw30705Labels = mixedMoment B node5413 node5413Labels := by
  calc
    mixedMoment B raw30705 raw30705Labels = mixedMoment B raw30705step0 raw30705step0Labels := by
      have hz : ∀ j, raw30705 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30705step0 = (fun i j => raw30705 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30705step0 raw30705; decide +kernel
      have hl : raw30705step0Labels = raw30705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30705 raw30705Labels permutation434 hz
    mixedMoment B raw30705step0 raw30705step0Labels = mixedMoment B raw30705step1 raw30705step1Labels := by
      have hz : ∀ j, raw30705step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30705step1 = (fun i j => raw30705step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30705step1 raw30705step0; decide +kernel
      have hl : raw30705step1Labels = raw30705step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30705step0 raw30705step0Labels permutation80 hz
    _ = mixedMoment B node5413 node5413Labels := by rfl

def raw30706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30706Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30706step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30706step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30706step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw30706step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw30706step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw30706step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw30706step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw30706step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical30706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30706 raw30706Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw30706 raw30706Labels = mixedMoment B raw30706step0 raw30706step0Labels := by
      have hz : ∀ j, raw30706 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30706step0 = (fun i j => raw30706 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30706step0 raw30706; decide +kernel
      have hl : raw30706step0Labels = raw30706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30706 raw30706Labels permutation434 hz
    mixedMoment B raw30706step0 raw30706step0Labels = mixedMoment B raw30706step1 raw30706step1Labels := by
      have hz : ∀ j, raw30706step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30706step1 = (fun i j => raw30706step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30706step1 raw30706step0; decide +kernel
      have hl : raw30706step1Labels = raw30706step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30706step0 raw30706step0Labels permutation80 hz
    mixedMoment B raw30706step1 raw30706step1Labels = mixedMoment B raw30706step2 raw30706step2Labels := by
      have hz : ∀ i, raw30706step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw30706step2 = (fun i j => raw30706step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw30706step2 raw30706step1; decide +kernel
      have hl : raw30706step2Labels = (fun j => raw30706step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw30706step1 raw30706step1Labels permutation4 hz
    mixedMoment B raw30706step2 raw30706step2Labels = mixedMoment B raw30706step3 raw30706step3Labels := by
      have ha : raw30706step3 = (fun i j => raw30706step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw30706step3 raw30706step2; decide +kernel
      have hl : raw30706step3Labels = raw30706step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30706step2 raw30706step2Labels permutation9 permutation0
    mixedMoment B raw30706step3 raw30706step3Labels = mixedMoment B raw30706step4 raw30706step4Labels := by
      have ha : raw30706step4 = raw30706step3 := by apply Matrix.ext; unfold raw30706step4 raw30706step3; decide +kernel
      have hl : raw30706step3Labels = labelEmbedding2 ∘ raw30706step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30706step3 raw30706step3Labels raw30706step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw30707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30707step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30707step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30707step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30707step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30707 raw30707Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw30707 raw30707Labels = mixedMoment B raw30707step0 raw30707step0Labels := by
      have hz : ∀ j, raw30707 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30707step0 = (fun i j => raw30707 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30707step0 raw30707; decide +kernel
      have hl : raw30707step0Labels = raw30707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30707 raw30707Labels permutation434 hz
    mixedMoment B raw30707step0 raw30707step0Labels = mixedMoment B raw30707step1 raw30707step1Labels := by
      have hz : ∀ j, raw30707step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30707step1 = (fun i j => raw30707step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30707step1 raw30707step0; decide +kernel
      have hl : raw30707step1Labels = raw30707step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30707step0 raw30707step0Labels permutation80 hz
    mixedMoment B raw30707step1 raw30707step1Labels = mixedMoment B raw30707step2 raw30707step2Labels := by
      have ha : raw30707step2 = (fun i j => raw30707step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30707step2 raw30707step1; decide +kernel
      have hl : raw30707step2Labels = raw30707step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30707step1 raw30707step1Labels permutation9 permutation2
    _ = mixedMoment B node4612 node4612Labels := by rfl

def raw30708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30708step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30708 raw30708Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw30708 raw30708Labels = mixedMoment B raw30708step0 raw30708step0Labels := by
      have hz : ∀ j, raw30708 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30708step0 = (fun i j => raw30708 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30708step0 raw30708; decide +kernel
      have hl : raw30708step0Labels = raw30708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30708 raw30708Labels permutation434 hz
    mixedMoment B raw30708step0 raw30708step0Labels = mixedMoment B raw30708step1 raw30708step1Labels := by
      have ha : raw30708step1 = (fun i j => raw30708step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30708step1 raw30708step0; decide +kernel
      have hl : raw30708step1Labels = raw30708step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30708step0 raw30708step0Labels permutation39 permutation2
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw30709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30709step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30709step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30709 raw30709Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw30709 raw30709Labels = mixedMoment B raw30709step0 raw30709step0Labels := by
      have hz : ∀ j, raw30709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30709step0 = (fun i j => raw30709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30709step0 raw30709; decide +kernel
      have hl : raw30709step0Labels = raw30709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30709 raw30709Labels permutation346 hz
    mixedMoment B raw30709step0 raw30709step0Labels = mixedMoment B raw30709step1 raw30709step1Labels := by
      have ha : raw30709step1 = (fun i j => raw30709step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30709step1 raw30709step0; decide +kernel
      have hl : raw30709step1Labels = raw30709step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30709step0 raw30709step0Labels permutation39 permutation2
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw30710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30710step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30710step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30710step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30710step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw30710step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30710 raw30710Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw30710 raw30710Labels = mixedMoment B raw30710step0 raw30710step0Labels := by
      have hz : ∀ j, raw30710 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30710step0 = (fun i j => raw30710 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30710step0 raw30710; decide +kernel
      have hl : raw30710step0Labels = raw30710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30710 raw30710Labels permutation434 hz
    mixedMoment B raw30710step0 raw30710step0Labels = mixedMoment B raw30710step1 raw30710step1Labels := by
      have hz : ∀ j, raw30710step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30710step1 = (fun i j => raw30710step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30710step1 raw30710step0; decide +kernel
      have hl : raw30710step1Labels = raw30710step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30710step0 raw30710step0Labels permutation80 hz
    mixedMoment B raw30710step1 raw30710step1Labels = mixedMoment B raw30710step2 raw30710step2Labels := by
      have ha : raw30710step2 = (fun i j => raw30710step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30710step2 raw30710step1; decide +kernel
      have hl : raw30710step2Labels = raw30710step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30710step1 raw30710step1Labels permutation9 permutation2
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw30711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30711step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30711step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30711 raw30711Labels = mixedMoment B node4549 node4549Labels := by
  calc
    mixedMoment B raw30711 raw30711Labels = mixedMoment B raw30711step0 raw30711step0Labels := by
      have hz : ∀ j, raw30711 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30711step0 = (fun i j => raw30711 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30711step0 raw30711; decide +kernel
      have hl : raw30711step0Labels = raw30711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30711 raw30711Labels permutation434 hz
    mixedMoment B raw30711step0 raw30711step0Labels = mixedMoment B raw30711step1 raw30711step1Labels := by
      have ha : raw30711step1 = (fun i j => raw30711step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30711step1 raw30711step0; decide +kernel
      have hl : raw30711step1Labels = raw30711step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30711step0 raw30711step0Labels permutation33 permutation2
    _ = mixedMoment B node4549 node4549Labels := by rfl

def raw30712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30712step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30712step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30712 raw30712Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw30712 raw30712Labels = mixedMoment B raw30712step0 raw30712step0Labels := by
      have hz : ∀ j, raw30712 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30712step0 = (fun i j => raw30712 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30712step0 raw30712; decide +kernel
      have hl : raw30712step0Labels = raw30712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30712 raw30712Labels permutation434 hz
    mixedMoment B raw30712step0 raw30712step0Labels = mixedMoment B raw30712step1 raw30712step1Labels := by
      have ha : raw30712step1 = (fun i j => raw30712step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30712step1 raw30712step0; decide +kernel
      have hl : raw30712step1Labels = raw30712step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30712step0 raw30712step0Labels permutation33 permutation2
    _ = mixedMoment B node4946 node4946Labels := by rfl

def raw30713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30713step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30713 raw30713Labels = mixedMoment B node5036 node5036Labels := by
  calc
    mixedMoment B raw30713 raw30713Labels = mixedMoment B raw30713step0 raw30713step0Labels := by
      have ha : raw30713step0 = (fun i j => raw30713 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30713step0 raw30713; decide +kernel
      have hl : raw30713step0Labels = raw30713Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30713 raw30713Labels permutation159 permutation2
    _ = mixedMoment B node5036 node5036Labels := by rfl

def raw30714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30714step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30714 raw30714Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw30714 raw30714Labels = mixedMoment B raw30714step0 raw30714step0Labels := by
      have hz : ∀ j, raw30714 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30714step0 = (fun i j => raw30714 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30714step0 raw30714; decide +kernel
      have hl : raw30714step0Labels = raw30714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30714 raw30714Labels permutation434 hz
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw30715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30715step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30715 raw30715Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw30715 raw30715Labels = mixedMoment B raw30715step0 raw30715step0Labels := by
      have hz : ∀ j, raw30715 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30715step0 = (fun i j => raw30715 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30715step0 raw30715; decide +kernel
      have hl : raw30715step0Labels = raw30715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30715 raw30715Labels permutation434 hz
    mixedMoment B raw30715step0 raw30715step0Labels = mixedMoment B raw30715step1 raw30715step1Labels := by
      have ha : raw30715step1 = (fun i j => raw30715step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30715step1 raw30715step0; decide +kernel
      have hl : raw30715step1Labels = raw30715step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30715step0 raw30715step0Labels permutation33 permutation2
    _ = mixedMoment B node5101 node5101Labels := by rfl

def raw30716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30716step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30716step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30716 raw30716Labels = mixedMoment B node4549 node4549Labels := by
  calc
    mixedMoment B raw30716 raw30716Labels = mixedMoment B raw30716step0 raw30716step0Labels := by
      have hz : ∀ j, raw30716 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30716step0 = (fun i j => raw30716 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30716step0 raw30716; decide +kernel
      have hl : raw30716step0Labels = raw30716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30716 raw30716Labels permutation346 hz
    mixedMoment B raw30716step0 raw30716step0Labels = mixedMoment B raw30716step1 raw30716step1Labels := by
      have ha : raw30716step1 = (fun i j => raw30716step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30716step1 raw30716step0; decide +kernel
      have hl : raw30716step1Labels = raw30716step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30716step0 raw30716step0Labels permutation33 permutation2
    _ = mixedMoment B node4549 node4549Labels := by rfl

def raw30717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30717step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30717step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30717 raw30717Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw30717 raw30717Labels = mixedMoment B raw30717step0 raw30717step0Labels := by
      have hz : ∀ j, raw30717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30717step0 = (fun i j => raw30717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30717step0 raw30717; decide +kernel
      have hl : raw30717step0Labels = raw30717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30717 raw30717Labels permutation346 hz
    mixedMoment B raw30717step0 raw30717step0Labels = mixedMoment B raw30717step1 raw30717step1Labels := by
      have ha : raw30717step1 = (fun i j => raw30717step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30717step1 raw30717step0; decide +kernel
      have hl : raw30717step1Labels = raw30717step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30717step0 raw30717step0Labels permutation33 permutation2
    _ = mixedMoment B node4946 node4946Labels := by rfl

def raw30718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30718Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30718step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30718 raw30718Labels = mixedMoment B node5036 node5036Labels := by
  calc
    mixedMoment B raw30718 raw30718Labels = mixedMoment B raw30718step0 raw30718step0Labels := by
      have ha : raw30718step0 = (fun i j => raw30718 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30718step0 raw30718; decide +kernel
      have hl : raw30718step0Labels = raw30718Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30718 raw30718Labels permutation153 permutation2
    _ = mixedMoment B node5036 node5036Labels := by rfl

def raw30719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30719step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30719 raw30719Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw30719 raw30719Labels = mixedMoment B raw30719step0 raw30719step0Labels := by
      have hz : ∀ j, raw30719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30719step0 = (fun i j => raw30719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30719step0 raw30719; decide +kernel
      have hl : raw30719step0Labels = raw30719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30719 raw30719Labels permutation346 hz
    _ = mixedMoment B node5102 node5102Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
