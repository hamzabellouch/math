import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw3968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3968step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![4, -3, -1]]
def raw3968step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3968step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw3968step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3968step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw3968step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3968 raw3968Labels = mixedMoment B node1059 node1059Labels := by
  calc
    mixedMoment B raw3968 raw3968Labels = mixedMoment B raw3968step0 raw3968step0Labels := by
      have hz : ∀ j, raw3968 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3968step0 = (fun i j => raw3968 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3968step0 raw3968; decide +kernel
      have hl : raw3968step0Labels = raw3968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3968 raw3968Labels permutation434 hz
    mixedMoment B raw3968step0 raw3968step0Labels = mixedMoment B raw3968step1 raw3968step1Labels := by
      have hz : ∀ j, raw3968step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3968step1 = (fun i j => raw3968step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3968step1 raw3968step0; decide +kernel
      have hl : raw3968step1Labels = raw3968step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3968step0 raw3968step0Labels permutation80 hz
    mixedMoment B raw3968step1 raw3968step1Labels = mixedMoment B raw3968step2 raw3968step2Labels := by
      have ha : raw3968step2 = (fun i j => raw3968step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3968step2 raw3968step1; decide +kernel
      have hl : raw3968step2Labels = raw3968step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3968step1 raw3968step1Labels permutation31 permutation3
    mixedMoment B raw3968step2 raw3968step2Labels = mixedMoment B raw3968step3 raw3968step3Labels := by
      have ha : raw3968step3 = -raw3968step2 := by apply Matrix.ext; change ∀ i j, raw3968step3 i j = -(raw3968step2 i j); unfold raw3968step3 raw3968step2; decide +kernel
      have hl : raw3968step3Labels = raw3968step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1059 node1059Labels := by rfl

def raw3969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3969step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw3969step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw3969step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3969 raw3969Labels = mixedMoment B node991 node991Labels := by
  calc
    mixedMoment B raw3969 raw3969Labels = mixedMoment B raw3969step0 raw3969step0Labels := by
      have hz : ∀ j, raw3969 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3969step0 = (fun i j => raw3969 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3969step0 raw3969; decide +kernel
      have hl : raw3969step0Labels = raw3969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3969 raw3969Labels permutation434 hz
    mixedMoment B raw3969step0 raw3969step0Labels = mixedMoment B raw3969step1 raw3969step1Labels := by
      have ha : raw3969step1 = (fun i j => raw3969step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3969step1 raw3969step0; decide +kernel
      have hl : raw3969step1Labels = raw3969step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3969step0 raw3969step0Labels permutation139 permutation3
    mixedMoment B raw3969step1 raw3969step1Labels = mixedMoment B raw3969step2 raw3969step2Labels := by
      have ha : raw3969step2 = -raw3969step1 := by apply Matrix.ext; change ∀ i j, raw3969step2 i j = -(raw3969step1 i j); unfold raw3969step2 raw3969step1; decide +kernel
      have hl : raw3969step2Labels = raw3969step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node991 node991Labels := by rfl

def raw3970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3970step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw3970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw3970step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3970 raw3970Labels = mixedMoment B node991 node991Labels := by
  calc
    mixedMoment B raw3970 raw3970Labels = mixedMoment B raw3970step0 raw3970step0Labels := by
      have hz : ∀ j, raw3970 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3970step0 = (fun i j => raw3970 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3970step0 raw3970; decide +kernel
      have hl : raw3970step0Labels = raw3970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3970 raw3970Labels permutation346 hz
    mixedMoment B raw3970step0 raw3970step0Labels = mixedMoment B raw3970step1 raw3970step1Labels := by
      have ha : raw3970step1 = (fun i j => raw3970step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3970step1 raw3970step0; decide +kernel
      have hl : raw3970step1Labels = raw3970step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3970step0 raw3970step0Labels permutation139 permutation3
    mixedMoment B raw3970step1 raw3970step1Labels = mixedMoment B raw3970step2 raw3970step2Labels := by
      have ha : raw3970step2 = -raw3970step1 := by apply Matrix.ext; change ∀ i j, raw3970step2 i j = -(raw3970step1 i j); unfold raw3970step2 raw3970step1; decide +kernel
      have hl : raw3970step2Labels = raw3970step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node991 node991Labels := by rfl

def raw3971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![4, -3, -1]]
def raw3971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![4, -3, -1]]
def raw3971step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![4, -3, -1]]
def raw3971step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3971step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw3971step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw3971step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw3971step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3971 raw3971Labels = mixedMoment B node1010 node1010Labels := by
  calc
    mixedMoment B raw3971 raw3971Labels = mixedMoment B raw3971step0 raw3971step0Labels := by
      have hz : ∀ j, raw3971 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3971step0 = (fun i j => raw3971 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3971step0 raw3971; decide +kernel
      have hl : raw3971step0Labels = raw3971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3971 raw3971Labels permutation434 hz
    mixedMoment B raw3971step0 raw3971step0Labels = mixedMoment B raw3971step1 raw3971step1Labels := by
      have hz : ∀ j, raw3971step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3971step1 = (fun i j => raw3971step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3971step1 raw3971step0; decide +kernel
      have hl : raw3971step1Labels = raw3971step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3971step0 raw3971step0Labels permutation80 hz
    mixedMoment B raw3971step1 raw3971step1Labels = mixedMoment B raw3971step2 raw3971step2Labels := by
      have ha : raw3971step2 = (fun i j => raw3971step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3971step2 raw3971step1; decide +kernel
      have hl : raw3971step2Labels = raw3971step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3971step1 raw3971step1Labels permutation29 permutation3
    mixedMoment B raw3971step2 raw3971step2Labels = mixedMoment B raw3971step3 raw3971step3Labels := by
      have ha : raw3971step3 = -raw3971step2 := by apply Matrix.ext; change ∀ i j, raw3971step3 i j = -(raw3971step2 i j); unfold raw3971step3 raw3971step2; decide +kernel
      have hl : raw3971step3Labels = raw3971step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1010 node1010Labels := by rfl

def raw3972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3972Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3972step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![3, -2, -1]]
def raw3972step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3972step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3972step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3972step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw3972step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3972 raw3972Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw3972 raw3972Labels = mixedMoment B raw3972step0 raw3972step0Labels := by
      have hz : ∀ j, raw3972 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3972step0 = (fun i j => raw3972 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3972step0 raw3972; decide +kernel
      have hl : raw3972step0Labels = raw3972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3972 raw3972Labels permutation434 hz
    mixedMoment B raw3972step0 raw3972step0Labels = mixedMoment B raw3972step1 raw3972step1Labels := by
      have hz : ∀ j, raw3972step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3972step1 = (fun i j => raw3972step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3972step1 raw3972step0; decide +kernel
      have hl : raw3972step1Labels = raw3972step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3972step0 raw3972step0Labels permutation80 hz
    mixedMoment B raw3972step1 raw3972step1Labels = mixedMoment B raw3972step2 raw3972step2Labels := by
      have ha : raw3972step2 = (fun i j => raw3972step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3972step2 raw3972step1; decide +kernel
      have hl : raw3972step2Labels = raw3972step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3972step1 raw3972step1Labels permutation28 permutation5
    mixedMoment B raw3972step2 raw3972step2Labels = mixedMoment B raw3972step3 raw3972step3Labels := by
      have ha : raw3972step3 = raw3972step2 := by apply Matrix.ext; unfold raw3972step3 raw3972step2; decide +kernel
      have hl : raw3972step2Labels = labelEmbedding1 ∘ raw3972step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3972step2 raw3972step2Labels raw3972step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3626 node3626Labels := by rfl

def raw3973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3973Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3973step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw3973step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw3973step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3973 raw3973Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw3973 raw3973Labels = mixedMoment B raw3973step0 raw3973step0Labels := by
      have hz : ∀ j, raw3973 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3973step0 = (fun i j => raw3973 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3973step0 raw3973; decide +kernel
      have hl : raw3973step0Labels = raw3973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3973 raw3973Labels permutation434 hz
    mixedMoment B raw3973step0 raw3973step0Labels = mixedMoment B raw3973step1 raw3973step1Labels := by
      have ha : raw3973step1 = (fun i j => raw3973step0 (permutation134 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3973step1 raw3973step0; decide +kernel
      have hl : raw3973step1Labels = raw3973step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3973step0 raw3973step0Labels permutation134 permutation5
    mixedMoment B raw3973step1 raw3973step1Labels = mixedMoment B raw3973step2 raw3973step2Labels := by
      have ha : raw3973step2 = raw3973step1 := by apply Matrix.ext; unfold raw3973step2 raw3973step1; decide +kernel
      have hl : raw3973step1Labels = labelEmbedding1 ∘ raw3973step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3973step1 raw3973step1Labels raw3973step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw3974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3974Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3974step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw3974step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw3974step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3974 raw3974Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw3974 raw3974Labels = mixedMoment B raw3974step0 raw3974step0Labels := by
      have hz : ∀ j, raw3974 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3974step0 = (fun i j => raw3974 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3974step0 raw3974; decide +kernel
      have hl : raw3974step0Labels = raw3974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3974 raw3974Labels permutation346 hz
    mixedMoment B raw3974step0 raw3974step0Labels = mixedMoment B raw3974step1 raw3974step1Labels := by
      have ha : raw3974step1 = (fun i j => raw3974step0 (permutation134 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3974step1 raw3974step0; decide +kernel
      have hl : raw3974step1Labels = raw3974step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3974step0 raw3974step0Labels permutation134 permutation5
    mixedMoment B raw3974step1 raw3974step1Labels = mixedMoment B raw3974step2 raw3974step2Labels := by
      have ha : raw3974step2 = raw3974step1 := by apply Matrix.ext; unfold raw3974step2 raw3974step1; decide +kernel
      have hl : raw3974step1Labels = labelEmbedding1 ∘ raw3974step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3974step1 raw3974step1Labels raw3974step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw3975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3975Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3975step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![3, -2, -1]]
def raw3975step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3975step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 1, 0], ![-2, -1, 3]]
def raw3975step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3975step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw3975step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3975step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw3975step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3975 raw3975Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw3975 raw3975Labels = mixedMoment B raw3975step0 raw3975step0Labels := by
      have hz : ∀ j, raw3975 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3975step0 = (fun i j => raw3975 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3975step0 raw3975; decide +kernel
      have hl : raw3975step0Labels = raw3975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3975 raw3975Labels permutation434 hz
    mixedMoment B raw3975step0 raw3975step0Labels = mixedMoment B raw3975step1 raw3975step1Labels := by
      have hz : ∀ j, raw3975step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3975step1 = (fun i j => raw3975step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3975step1 raw3975step0; decide +kernel
      have hl : raw3975step1Labels = raw3975step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3975step0 raw3975step0Labels permutation80 hz
    mixedMoment B raw3975step1 raw3975step1Labels = mixedMoment B raw3975step2 raw3975step2Labels := by
      have ha : raw3975step2 = (fun i j => raw3975step1 (permutation20 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3975step2 raw3975step1; decide +kernel
      have hl : raw3975step2Labels = raw3975step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3975step1 raw3975step1Labels permutation20 permutation5
    mixedMoment B raw3975step2 raw3975step2Labels = mixedMoment B raw3975step3 raw3975step3Labels := by
      have ha : raw3975step3 = -raw3975step2 := by apply Matrix.ext; change ∀ i j, raw3975step3 i j = -(raw3975step2 i j); unfold raw3975step3 raw3975step2; decide +kernel
      have hl : raw3975step3Labels = raw3975step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3975step3 raw3975step3Labels = mixedMoment B raw3975step4 raw3975step4Labels := by
      have ha : raw3975step4 = raw3975step3 := by apply Matrix.ext; unfold raw3975step4 raw3975step3; decide +kernel
      have hl : raw3975step3Labels = labelEmbedding1 ∘ raw3975step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3975step3 raw3975step3Labels raw3975step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3052 node3052Labels := by rfl

def raw3976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3976Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3976step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw3976step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw3976step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3976step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw3976step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3976step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw3976step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3976 raw3976Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw3976 raw3976Labels = mixedMoment B raw3976step0 raw3976step0Labels := by
      have hz : ∀ j, raw3976 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3976step0 = (fun i j => raw3976 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3976step0 raw3976; decide +kernel
      have hl : raw3976step0Labels = raw3976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3976 raw3976Labels permutation434 hz
    mixedMoment B raw3976step0 raw3976step0Labels = mixedMoment B raw3976step1 raw3976step1Labels := by
      have hz : ∀ j, raw3976step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3976step1 = (fun i j => raw3976step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3976step1 raw3976step0; decide +kernel
      have hl : raw3976step1Labels = raw3976step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3976step0 raw3976step0Labels permutation80 hz
    mixedMoment B raw3976step1 raw3976step1Labels = mixedMoment B raw3976step2 raw3976step2Labels := by
      have ha : raw3976step2 = (fun i j => raw3976step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3976step2 raw3976step1; decide +kernel
      have hl : raw3976step2Labels = raw3976step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3976step1 raw3976step1Labels permutation9 permutation7
    mixedMoment B raw3976step2 raw3976step2Labels = mixedMoment B raw3976step3 raw3976step3Labels := by
      have ha : raw3976step3 = -raw3976step2 := by apply Matrix.ext; change ∀ i j, raw3976step3 i j = -(raw3976step2 i j); unfold raw3976step3 raw3976step2; decide +kernel
      have hl : raw3976step3Labels = raw3976step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3976step3 raw3976step3Labels = mixedMoment B raw3976step4 raw3976step4Labels := by
      have ha : raw3976step4 = raw3976step3 := by apply Matrix.ext; unfold raw3976step4 raw3976step3; decide +kernel
      have hl : raw3976step3Labels = labelEmbedding1 ∘ raw3976step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3976step3 raw3976step3Labels raw3976step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3862 node3862Labels := by rfl

def raw3977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3977Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3977step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![3, -2, -1]]
def raw3977step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw3977step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3977step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![2, -1, -1], ![2, 1, -3]]
def raw3977step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3977step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![2, -1, -1], ![2, 1, -3]]
def raw3977step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3977 raw3977Labels = mixedMoment B node3247 node3247Labels := by
  calc
    mixedMoment B raw3977 raw3977Labels = mixedMoment B raw3977step0 raw3977step0Labels := by
      have hz : ∀ j, raw3977 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3977step0 = (fun i j => raw3977 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3977step0 raw3977; decide +kernel
      have hl : raw3977step0Labels = raw3977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3977 raw3977Labels permutation434 hz
    mixedMoment B raw3977step0 raw3977step0Labels = mixedMoment B raw3977step1 raw3977step1Labels := by
      have hz : ∀ j, raw3977step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3977step1 = (fun i j => raw3977step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3977step1 raw3977step0; decide +kernel
      have hl : raw3977step1Labels = raw3977step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3977step0 raw3977step0Labels permutation80 hz
    mixedMoment B raw3977step1 raw3977step1Labels = mixedMoment B raw3977step2 raw3977step2Labels := by
      have ha : raw3977step2 = (fun i j => raw3977step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3977step2 raw3977step1; decide +kernel
      have hl : raw3977step2Labels = raw3977step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3977step1 raw3977step1Labels permutation10 permutation5
    mixedMoment B raw3977step2 raw3977step2Labels = mixedMoment B raw3977step3 raw3977step3Labels := by
      have ha : raw3977step3 = -raw3977step2 := by apply Matrix.ext; change ∀ i j, raw3977step3 i j = -(raw3977step2 i j); unfold raw3977step3 raw3977step2; decide +kernel
      have hl : raw3977step3Labels = raw3977step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3977step3 raw3977step3Labels = mixedMoment B raw3977step4 raw3977step4Labels := by
      have ha : raw3977step4 = raw3977step3 := by apply Matrix.ext; unfold raw3977step4 raw3977step3; decide +kernel
      have hl : raw3977step3Labels = labelEmbedding1 ∘ raw3977step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3977step3 raw3977step3Labels raw3977step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3247 node3247Labels := by rfl

def raw3978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3978Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3978step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3978step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3978step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3978 raw3978Labels = mixedMoment B node3358 node3358Labels := by
  calc
    mixedMoment B raw3978 raw3978Labels = mixedMoment B raw3978step0 raw3978step0Labels := by
      have hz : ∀ j, raw3978 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3978step0 = (fun i j => raw3978 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3978step0 raw3978; decide +kernel
      have hl : raw3978step0Labels = raw3978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3978 raw3978Labels permutation434 hz
    mixedMoment B raw3978step0 raw3978step0Labels = mixedMoment B raw3978step1 raw3978step1Labels := by
      have ha : raw3978step1 = (fun i j => raw3978step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3978step1 raw3978step0; decide +kernel
      have hl : raw3978step1Labels = raw3978step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3978step0 raw3978step0Labels permutation136 permutation5
    mixedMoment B raw3978step1 raw3978step1Labels = mixedMoment B raw3978step2 raw3978step2Labels := by
      have ha : raw3978step2 = raw3978step1 := by apply Matrix.ext; unfold raw3978step2 raw3978step1; decide +kernel
      have hl : raw3978step1Labels = labelEmbedding1 ∘ raw3978step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3978step1 raw3978step1Labels raw3978step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3358 node3358Labels := by rfl

def raw3979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3979Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3979step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3979step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3979step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3979step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3979 raw3979Labels = mixedMoment B node3358 node3358Labels := by
  calc
    mixedMoment B raw3979 raw3979Labels = mixedMoment B raw3979step0 raw3979step0Labels := by
      have hz : ∀ j, raw3979 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3979step0 = (fun i j => raw3979 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3979step0 raw3979; decide +kernel
      have hl : raw3979step0Labels = raw3979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3979 raw3979Labels permutation346 hz
    mixedMoment B raw3979step0 raw3979step0Labels = mixedMoment B raw3979step1 raw3979step1Labels := by
      have ha : raw3979step1 = (fun i j => raw3979step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3979step1 raw3979step0; decide +kernel
      have hl : raw3979step1Labels = raw3979step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3979step0 raw3979step0Labels permutation136 permutation5
    mixedMoment B raw3979step1 raw3979step1Labels = mixedMoment B raw3979step2 raw3979step2Labels := by
      have ha : raw3979step2 = raw3979step1 := by apply Matrix.ext; unfold raw3979step2 raw3979step1; decide +kernel
      have hl : raw3979step1Labels = labelEmbedding1 ∘ raw3979step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3979step1 raw3979step1Labels raw3979step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3358 node3358Labels := by rfl

def raw3980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3980Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3980step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3980step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![3, -2, -1]]
def raw3980step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3980step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-2, 1, 1], ![-2, -1, 3]]
def raw3980step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3980step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, -1, -1], ![2, 1, -3]]
def raw3980step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3980step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, -1, -1], ![2, 1, -3]]
def raw3980step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3980 raw3980Labels = mixedMoment B node2842 node2842Labels := by
  calc
    mixedMoment B raw3980 raw3980Labels = mixedMoment B raw3980step0 raw3980step0Labels := by
      have hz : ∀ j, raw3980 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3980step0 = (fun i j => raw3980 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3980step0 raw3980; decide +kernel
      have hl : raw3980step0Labels = raw3980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3980 raw3980Labels permutation434 hz
    mixedMoment B raw3980step0 raw3980step0Labels = mixedMoment B raw3980step1 raw3980step1Labels := by
      have hz : ∀ j, raw3980step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3980step1 = (fun i j => raw3980step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3980step1 raw3980step0; decide +kernel
      have hl : raw3980step1Labels = raw3980step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3980step0 raw3980step0Labels permutation80 hz
    mixedMoment B raw3980step1 raw3980step1Labels = mixedMoment B raw3980step2 raw3980step2Labels := by
      have ha : raw3980step2 = (fun i j => raw3980step1 (permutation20 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3980step2 raw3980step1; decide +kernel
      have hl : raw3980step2Labels = raw3980step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3980step1 raw3980step1Labels permutation20 permutation5
    mixedMoment B raw3980step2 raw3980step2Labels = mixedMoment B raw3980step3 raw3980step3Labels := by
      have ha : raw3980step3 = -raw3980step2 := by apply Matrix.ext; change ∀ i j, raw3980step3 i j = -(raw3980step2 i j); unfold raw3980step3 raw3980step2; decide +kernel
      have hl : raw3980step3Labels = raw3980step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3980step3 raw3980step3Labels = mixedMoment B raw3980step4 raw3980step4Labels := by
      have ha : raw3980step4 = raw3980step3 := by apply Matrix.ext; unfold raw3980step4 raw3980step3; decide +kernel
      have hl : raw3980step3Labels = labelEmbedding1 ∘ raw3980step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3980step3 raw3980step3Labels raw3980step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2842 node2842Labels := by rfl

def raw3981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3981Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3981step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw3981step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3981step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw3981step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3981step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3981step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3981step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3981step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3981 raw3981Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw3981 raw3981Labels = mixedMoment B raw3981step0 raw3981step0Labels := by
      have hz : ∀ j, raw3981 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3981step0 = (fun i j => raw3981 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3981step0 raw3981; decide +kernel
      have hl : raw3981step0Labels = raw3981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3981 raw3981Labels permutation434 hz
    mixedMoment B raw3981step0 raw3981step0Labels = mixedMoment B raw3981step1 raw3981step1Labels := by
      have hz : ∀ j, raw3981step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3981step1 = (fun i j => raw3981step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3981step1 raw3981step0; decide +kernel
      have hl : raw3981step1Labels = raw3981step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3981step0 raw3981step0Labels permutation80 hz
    mixedMoment B raw3981step1 raw3981step1Labels = mixedMoment B raw3981step2 raw3981step2Labels := by
      have ha : raw3981step2 = (fun i j => raw3981step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3981step2 raw3981step1; decide +kernel
      have hl : raw3981step2Labels = raw3981step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3981step1 raw3981step1Labels permutation9 permutation7
    mixedMoment B raw3981step2 raw3981step2Labels = mixedMoment B raw3981step3 raw3981step3Labels := by
      have ha : raw3981step3 = -raw3981step2 := by apply Matrix.ext; change ∀ i j, raw3981step3 i j = -(raw3981step2 i j); unfold raw3981step3 raw3981step2; decide +kernel
      have hl : raw3981step3Labels = raw3981step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3981step3 raw3981step3Labels = mixedMoment B raw3981step4 raw3981step4Labels := by
      have ha : raw3981step4 = raw3981step3 := by apply Matrix.ext; unfold raw3981step4 raw3981step3; decide +kernel
      have hl : raw3981step3Labels = labelEmbedding1 ∘ raw3981step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3981step3 raw3981step3Labels raw3981step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3584 node3584Labels := by rfl

def raw3982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3982Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3982step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw3982step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw3982step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3982step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw3982step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3982 raw3982Labels = mixedMoment B node3242 node3242Labels := by
  calc
    mixedMoment B raw3982 raw3982Labels = mixedMoment B raw3982step0 raw3982step0Labels := by
      have hz : ∀ j, raw3982 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3982step0 = (fun i j => raw3982 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3982step0 raw3982; decide +kernel
      have hl : raw3982step0Labels = raw3982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3982 raw3982Labels permutation434 hz
    mixedMoment B raw3982step0 raw3982step0Labels = mixedMoment B raw3982step1 raw3982step1Labels := by
      have ha : raw3982step1 = (fun i j => raw3982step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3982step1 raw3982step0; decide +kernel
      have hl : raw3982step1Labels = raw3982step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3982step0 raw3982step0Labels permutation44 permutation5
    mixedMoment B raw3982step1 raw3982step1Labels = mixedMoment B raw3982step2 raw3982step2Labels := by
      have ha : raw3982step2 = -raw3982step1 := by apply Matrix.ext; change ∀ i j, raw3982step2 i j = -(raw3982step1 i j); unfold raw3982step2 raw3982step1; decide +kernel
      have hl : raw3982step2Labels = raw3982step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3982step2 raw3982step2Labels = mixedMoment B raw3982step3 raw3982step3Labels := by
      have ha : raw3982step3 = raw3982step2 := by apply Matrix.ext; unfold raw3982step3 raw3982step2; decide +kernel
      have hl : raw3982step2Labels = labelEmbedding1 ∘ raw3982step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3982step2 raw3982step2Labels raw3982step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3242 node3242Labels := by rfl

def raw3983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3983Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3983step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3983step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3983step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3983 raw3983Labels = mixedMoment B node3472 node3472Labels := by
  calc
    mixedMoment B raw3983 raw3983Labels = mixedMoment B raw3983step0 raw3983step0Labels := by
      have hz : ∀ j, raw3983 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3983step0 = (fun i j => raw3983 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3983step0 raw3983; decide +kernel
      have hl : raw3983step0Labels = raw3983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3983 raw3983Labels permutation434 hz
    mixedMoment B raw3983step0 raw3983step0Labels = mixedMoment B raw3983step1 raw3983step1Labels := by
      have ha : raw3983step1 = (fun i j => raw3983step0 (permutation142 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3983step1 raw3983step0; decide +kernel
      have hl : raw3983step1Labels = raw3983step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3983step0 raw3983step0Labels permutation142 permutation5
    mixedMoment B raw3983step1 raw3983step1Labels = mixedMoment B raw3983step2 raw3983step2Labels := by
      have ha : raw3983step2 = raw3983step1 := by apply Matrix.ext; unfold raw3983step2 raw3983step1; decide +kernel
      have hl : raw3983step1Labels = labelEmbedding1 ∘ raw3983step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3983step1 raw3983step1Labels raw3983step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3472 node3472Labels := by rfl

def raw3984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3984Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3984step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3984 raw3984Labels = mixedMoment B node3437 node3437Labels := by
  calc
    mixedMoment B raw3984 raw3984Labels = mixedMoment B raw3984step0 raw3984step0Labels := by
      have ha : raw3984step0 = (fun i j => raw3984 (permutation631 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3984step0 raw3984; decide +kernel
      have hl : raw3984step0Labels = raw3984Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3984 raw3984Labels permutation631 permutation5
    mixedMoment B raw3984step0 raw3984step0Labels = mixedMoment B raw3984step1 raw3984step1Labels := by
      have ha : raw3984step1 = raw3984step0 := by apply Matrix.ext; unfold raw3984step1 raw3984step0; decide +kernel
      have hl : raw3984step0Labels = labelEmbedding1 ∘ raw3984step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3984step0 raw3984step0Labels raw3984step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3437 node3437Labels := by rfl

def raw3985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3985Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3985step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw3985step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3985step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw3985step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3985step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw3985step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3985 raw3985Labels = mixedMoment B node2837 node2837Labels := by
  calc
    mixedMoment B raw3985 raw3985Labels = mixedMoment B raw3985step0 raw3985step0Labels := by
      have hz : ∀ j, raw3985 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3985step0 = (fun i j => raw3985 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3985step0 raw3985; decide +kernel
      have hl : raw3985step0Labels = raw3985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3985 raw3985Labels permutation434 hz
    mixedMoment B raw3985step0 raw3985step0Labels = mixedMoment B raw3985step1 raw3985step1Labels := by
      have ha : raw3985step1 = (fun i j => raw3985step0 (permutation104 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3985step1 raw3985step0; decide +kernel
      have hl : raw3985step1Labels = raw3985step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3985step0 raw3985step0Labels permutation104 permutation5
    mixedMoment B raw3985step1 raw3985step1Labels = mixedMoment B raw3985step2 raw3985step2Labels := by
      have ha : raw3985step2 = -raw3985step1 := by apply Matrix.ext; change ∀ i j, raw3985step2 i j = -(raw3985step1 i j); unfold raw3985step2 raw3985step1; decide +kernel
      have hl : raw3985step2Labels = raw3985step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3985step2 raw3985step2Labels = mixedMoment B raw3985step3 raw3985step3Labels := by
      have ha : raw3985step3 = raw3985step2 := by apply Matrix.ext; unfold raw3985step3 raw3985step2; decide +kernel
      have hl : raw3985step2Labels = labelEmbedding1 ∘ raw3985step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3985step2 raw3985step2Labels raw3985step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2837 node2837Labels := by rfl

def raw3986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3986Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3986step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw3986step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3986step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3986step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3986step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3986step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3986 raw3986Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw3986 raw3986Labels = mixedMoment B raw3986step0 raw3986step0Labels := by
      have hz : ∀ j, raw3986 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3986step0 = (fun i j => raw3986 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3986step0 raw3986; decide +kernel
      have hl : raw3986step0Labels = raw3986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3986 raw3986Labels permutation434 hz
    mixedMoment B raw3986step0 raw3986step0Labels = mixedMoment B raw3986step1 raw3986step1Labels := by
      have ha : raw3986step1 = (fun i j => raw3986step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3986step1 raw3986step0; decide +kernel
      have hl : raw3986step1Labels = raw3986step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3986step0 raw3986step0Labels permutation33 permutation7
    mixedMoment B raw3986step1 raw3986step1Labels = mixedMoment B raw3986step2 raw3986step2Labels := by
      have ha : raw3986step2 = -raw3986step1 := by apply Matrix.ext; change ∀ i j, raw3986step2 i j = -(raw3986step1 i j); unfold raw3986step2 raw3986step1; decide +kernel
      have hl : raw3986step2Labels = raw3986step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3986step2 raw3986step2Labels = mixedMoment B raw3986step3 raw3986step3Labels := by
      have ha : raw3986step3 = raw3986step2 := by apply Matrix.ext; unfold raw3986step3 raw3986step2; decide +kernel
      have hl : raw3986step2Labels = labelEmbedding1 ∘ raw3986step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3986step2 raw3986step2Labels raw3986step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw3987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3987Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3987step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw3987step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3987step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw3987step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3987step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw3987step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3987 raw3987Labels = mixedMoment B node3242 node3242Labels := by
  calc
    mixedMoment B raw3987 raw3987Labels = mixedMoment B raw3987step0 raw3987step0Labels := by
      have hz : ∀ j, raw3987 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3987step0 = (fun i j => raw3987 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3987step0 raw3987; decide +kernel
      have hl : raw3987step0Labels = raw3987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3987 raw3987Labels permutation346 hz
    mixedMoment B raw3987step0 raw3987step0Labels = mixedMoment B raw3987step1 raw3987step1Labels := by
      have ha : raw3987step1 = (fun i j => raw3987step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3987step1 raw3987step0; decide +kernel
      have hl : raw3987step1Labels = raw3987step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3987step0 raw3987step0Labels permutation44 permutation5
    mixedMoment B raw3987step1 raw3987step1Labels = mixedMoment B raw3987step2 raw3987step2Labels := by
      have ha : raw3987step2 = -raw3987step1 := by apply Matrix.ext; change ∀ i j, raw3987step2 i j = -(raw3987step1 i j); unfold raw3987step2 raw3987step1; decide +kernel
      have hl : raw3987step2Labels = raw3987step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3987step2 raw3987step2Labels = mixedMoment B raw3987step3 raw3987step3Labels := by
      have ha : raw3987step3 = raw3987step2 := by apply Matrix.ext; unfold raw3987step3 raw3987step2; decide +kernel
      have hl : raw3987step2Labels = labelEmbedding1 ∘ raw3987step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3987step2 raw3987step2Labels raw3987step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3242 node3242Labels := by rfl

def raw3988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3988Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3988step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3988step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3988step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3988 raw3988Labels = mixedMoment B node3472 node3472Labels := by
  calc
    mixedMoment B raw3988 raw3988Labels = mixedMoment B raw3988step0 raw3988step0Labels := by
      have hz : ∀ j, raw3988 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3988step0 = (fun i j => raw3988 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3988step0 raw3988; decide +kernel
      have hl : raw3988step0Labels = raw3988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3988 raw3988Labels permutation346 hz
    mixedMoment B raw3988step0 raw3988step0Labels = mixedMoment B raw3988step1 raw3988step1Labels := by
      have ha : raw3988step1 = (fun i j => raw3988step0 (permutation142 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3988step1 raw3988step0; decide +kernel
      have hl : raw3988step1Labels = raw3988step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3988step0 raw3988step0Labels permutation142 permutation5
    mixedMoment B raw3988step1 raw3988step1Labels = mixedMoment B raw3988step2 raw3988step2Labels := by
      have ha : raw3988step2 = raw3988step1 := by apply Matrix.ext; unfold raw3988step2 raw3988step1; decide +kernel
      have hl : raw3988step1Labels = labelEmbedding1 ∘ raw3988step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3988step1 raw3988step1Labels raw3988step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3472 node3472Labels := by rfl

def raw3989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw3989Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3989step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3989step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3989step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3989 raw3989Labels = mixedMoment B node3437 node3437Labels := by
  calc
    mixedMoment B raw3989 raw3989Labels = mixedMoment B raw3989step0 raw3989step0Labels := by
      have ha : raw3989step0 = (fun i j => raw3989 (permutation652 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3989step0 raw3989; decide +kernel
      have hl : raw3989step0Labels = raw3989Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3989 raw3989Labels permutation652 permutation5
    mixedMoment B raw3989step0 raw3989step0Labels = mixedMoment B raw3989step1 raw3989step1Labels := by
      have ha : raw3989step1 = raw3989step0 := by apply Matrix.ext; unfold raw3989step1 raw3989step0; decide +kernel
      have hl : raw3989step0Labels = labelEmbedding1 ∘ raw3989step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3989step0 raw3989step0Labels raw3989step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3437 node3437Labels := by rfl

def raw3990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3990Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw3990step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw3990step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3990step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw3990step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3990step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw3990step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3990 raw3990Labels = mixedMoment B node2837 node2837Labels := by
  calc
    mixedMoment B raw3990 raw3990Labels = mixedMoment B raw3990step0 raw3990step0Labels := by
      have hz : ∀ j, raw3990 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3990step0 = (fun i j => raw3990 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3990step0 raw3990; decide +kernel
      have hl : raw3990step0Labels = raw3990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3990 raw3990Labels permutation346 hz
    mixedMoment B raw3990step0 raw3990step0Labels = mixedMoment B raw3990step1 raw3990step1Labels := by
      have ha : raw3990step1 = (fun i j => raw3990step0 (permutation104 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3990step1 raw3990step0; decide +kernel
      have hl : raw3990step1Labels = raw3990step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3990step0 raw3990step0Labels permutation104 permutation5
    mixedMoment B raw3990step1 raw3990step1Labels = mixedMoment B raw3990step2 raw3990step2Labels := by
      have ha : raw3990step2 = -raw3990step1 := by apply Matrix.ext; change ∀ i j, raw3990step2 i j = -(raw3990step1 i j); unfold raw3990step2 raw3990step1; decide +kernel
      have hl : raw3990step2Labels = raw3990step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3990step2 raw3990step2Labels = mixedMoment B raw3990step3 raw3990step3Labels := by
      have ha : raw3990step3 = raw3990step2 := by apply Matrix.ext; unfold raw3990step3 raw3990step2; decide +kernel
      have hl : raw3990step2Labels = labelEmbedding1 ∘ raw3990step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3990step2 raw3990step2Labels raw3990step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2837 node2837Labels := by rfl

def raw3991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3991Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw3991step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw3991step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3991step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3991step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw3991step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3991 raw3991Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw3991 raw3991Labels = mixedMoment B raw3991step0 raw3991step0Labels := by
      have hz : ∀ j, raw3991 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3991step0 = (fun i j => raw3991 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3991step0 raw3991; decide +kernel
      have hl : raw3991step0Labels = raw3991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3991 raw3991Labels permutation346 hz
    mixedMoment B raw3991step0 raw3991step0Labels = mixedMoment B raw3991step1 raw3991step1Labels := by
      have ha : raw3991step1 = (fun i j => raw3991step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3991step1 raw3991step0; decide +kernel
      have hl : raw3991step1Labels = raw3991step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3991step0 raw3991step0Labels permutation33 permutation7
    mixedMoment B raw3991step1 raw3991step1Labels = mixedMoment B raw3991step2 raw3991step2Labels := by
      have ha : raw3991step2 = -raw3991step1 := by apply Matrix.ext; change ∀ i j, raw3991step2 i j = -(raw3991step1 i j); unfold raw3991step2 raw3991step1; decide +kernel
      have hl : raw3991step2Labels = raw3991step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3991step2 raw3991step2Labels = mixedMoment B raw3991step3 raw3991step3Labels := by
      have ha : raw3991step3 = raw3991step2 := by apply Matrix.ext; unfold raw3991step3 raw3991step2; decide +kernel
      have hl : raw3991step2Labels = labelEmbedding1 ∘ raw3991step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3991step2 raw3991step2Labels raw3991step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw3992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3992Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3992step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3992step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw3992step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3992step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw3992step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3992step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw3992step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3992step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw3992step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3992 raw3992Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw3992 raw3992Labels = mixedMoment B raw3992step0 raw3992step0Labels := by
      have hz : ∀ j, raw3992 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3992step0 = (fun i j => raw3992 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3992step0 raw3992; decide +kernel
      have hl : raw3992step0Labels = raw3992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3992 raw3992Labels permutation434 hz
    mixedMoment B raw3992step0 raw3992step0Labels = mixedMoment B raw3992step1 raw3992step1Labels := by
      have hz : ∀ j, raw3992step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3992step1 = (fun i j => raw3992step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3992step1 raw3992step0; decide +kernel
      have hl : raw3992step1Labels = raw3992step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3992step0 raw3992step0Labels permutation80 hz
    mixedMoment B raw3992step1 raw3992step1Labels = mixedMoment B raw3992step2 raw3992step2Labels := by
      have ha : raw3992step2 = (fun i j => raw3992step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3992step2 raw3992step1; decide +kernel
      have hl : raw3992step2Labels = raw3992step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3992step1 raw3992step1Labels permutation9 permutation7
    mixedMoment B raw3992step2 raw3992step2Labels = mixedMoment B raw3992step3 raw3992step3Labels := by
      have ha : raw3992step3 = -raw3992step2 := by apply Matrix.ext; change ∀ i j, raw3992step3 i j = -(raw3992step2 i j); unfold raw3992step3 raw3992step2; decide +kernel
      have hl : raw3992step3Labels = raw3992step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3992step3 raw3992step3Labels = mixedMoment B raw3992step4 raw3992step4Labels := by
      have ha : raw3992step4 = raw3992step3 := by apply Matrix.ext; unfold raw3992step4 raw3992step3; decide +kernel
      have hl : raw3992step3Labels = labelEmbedding1 ∘ raw3992step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3992step3 raw3992step3Labels raw3992step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3302 node3302Labels := by rfl

def raw3993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3993Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3993step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw3993step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3993step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw3993step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3993step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw3993step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3993step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw3993step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3993 raw3993Labels = mixedMoment B node3486 node3486Labels := by
  calc
    mixedMoment B raw3993 raw3993Labels = mixedMoment B raw3993step0 raw3993step0Labels := by
      have hz : ∀ j, raw3993 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3993step0 = (fun i j => raw3993 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3993step0 raw3993; decide +kernel
      have hl : raw3993step0Labels = raw3993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3993 raw3993Labels permutation434 hz
    mixedMoment B raw3993step0 raw3993step0Labels = mixedMoment B raw3993step1 raw3993step1Labels := by
      have hz : ∀ j, raw3993step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3993step1 = (fun i j => raw3993step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3993step1 raw3993step0; decide +kernel
      have hl : raw3993step1Labels = raw3993step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3993step0 raw3993step0Labels permutation80 hz
    mixedMoment B raw3993step1 raw3993step1Labels = mixedMoment B raw3993step2 raw3993step2Labels := by
      have ha : raw3993step2 = (fun i j => raw3993step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3993step2 raw3993step1; decide +kernel
      have hl : raw3993step2Labels = raw3993step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3993step1 raw3993step1Labels permutation9 permutation7
    mixedMoment B raw3993step2 raw3993step2Labels = mixedMoment B raw3993step3 raw3993step3Labels := by
      have ha : raw3993step3 = -raw3993step2 := by apply Matrix.ext; change ∀ i j, raw3993step3 i j = -(raw3993step2 i j); unfold raw3993step3 raw3993step2; decide +kernel
      have hl : raw3993step3Labels = raw3993step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3993step3 raw3993step3Labels = mixedMoment B raw3993step4 raw3993step4Labels := by
      have ha : raw3993step4 = raw3993step3 := by apply Matrix.ext; unfold raw3993step4 raw3993step3; decide +kernel
      have hl : raw3993step3Labels = labelEmbedding1 ∘ raw3993step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3993step3 raw3993step3Labels raw3993step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3486 node3486Labels := by rfl

def raw3994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3994Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3994step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw3994step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3994step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw3994step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3994step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw3994step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3994 raw3994Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw3994 raw3994Labels = mixedMoment B raw3994step0 raw3994step0Labels := by
      have hz : ∀ j, raw3994 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3994step0 = (fun i j => raw3994 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3994step0 raw3994; decide +kernel
      have hl : raw3994step0Labels = raw3994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3994 raw3994Labels permutation434 hz
    mixedMoment B raw3994step0 raw3994step0Labels = mixedMoment B raw3994step1 raw3994step1Labels := by
      have ha : raw3994step1 = (fun i j => raw3994step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3994step1 raw3994step0; decide +kernel
      have hl : raw3994step1Labels = raw3994step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3994step0 raw3994step0Labels permutation33 permutation7
    mixedMoment B raw3994step1 raw3994step1Labels = mixedMoment B raw3994step2 raw3994step2Labels := by
      have ha : raw3994step2 = -raw3994step1 := by apply Matrix.ext; change ∀ i j, raw3994step2 i j = -(raw3994step1 i j); unfold raw3994step2 raw3994step1; decide +kernel
      have hl : raw3994step2Labels = raw3994step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3994step2 raw3994step2Labels = mixedMoment B raw3994step3 raw3994step3Labels := by
      have ha : raw3994step3 = raw3994step2 := by apply Matrix.ext; unfold raw3994step3 raw3994step2; decide +kernel
      have hl : raw3994step2Labels = labelEmbedding1 ∘ raw3994step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3994step2 raw3994step2Labels raw3994step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

def raw3995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3995Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw3995step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw3995step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw3995step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3995step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw3995step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3995 raw3995Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw3995 raw3995Labels = mixedMoment B raw3995step0 raw3995step0Labels := by
      have hz : ∀ j, raw3995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3995step0 = (fun i j => raw3995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3995step0 raw3995; decide +kernel
      have hl : raw3995step0Labels = raw3995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3995 raw3995Labels permutation346 hz
    mixedMoment B raw3995step0 raw3995step0Labels = mixedMoment B raw3995step1 raw3995step1Labels := by
      have ha : raw3995step1 = (fun i j => raw3995step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3995step1 raw3995step0; decide +kernel
      have hl : raw3995step1Labels = raw3995step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3995step0 raw3995step0Labels permutation33 permutation7
    mixedMoment B raw3995step1 raw3995step1Labels = mixedMoment B raw3995step2 raw3995step2Labels := by
      have ha : raw3995step2 = -raw3995step1 := by apply Matrix.ext; change ∀ i j, raw3995step2 i j = -(raw3995step1 i j); unfold raw3995step2 raw3995step1; decide +kernel
      have hl : raw3995step2Labels = raw3995step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3995step2 raw3995step2Labels = mixedMoment B raw3995step3 raw3995step3Labels := by
      have ha : raw3995step3 = raw3995step2 := by apply Matrix.ext; unfold raw3995step3 raw3995step2; decide +kernel
      have hl : raw3995step2Labels = labelEmbedding1 ∘ raw3995step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3995step2 raw3995step2Labels raw3995step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

def raw3996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw3996Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw3996step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3996step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw3996step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3996step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw3996step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3996step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw3996step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3996step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw3996step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3996 raw3996Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw3996 raw3996Labels = mixedMoment B raw3996step0 raw3996step0Labels := by
      have hz : ∀ j, raw3996 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3996step0 = (fun i j => raw3996 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3996step0 raw3996; decide +kernel
      have hl : raw3996step0Labels = raw3996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3996 raw3996Labels permutation434 hz
    mixedMoment B raw3996step0 raw3996step0Labels = mixedMoment B raw3996step1 raw3996step1Labels := by
      have hz : ∀ j, raw3996step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3996step1 = (fun i j => raw3996step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3996step1 raw3996step0; decide +kernel
      have hl : raw3996step1Labels = raw3996step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3996step0 raw3996step0Labels permutation80 hz
    mixedMoment B raw3996step1 raw3996step1Labels = mixedMoment B raw3996step2 raw3996step2Labels := by
      have ha : raw3996step2 = (fun i j => raw3996step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw3996step2 raw3996step1; decide +kernel
      have hl : raw3996step2Labels = raw3996step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3996step1 raw3996step1Labels permutation9 permutation7
    mixedMoment B raw3996step2 raw3996step2Labels = mixedMoment B raw3996step3 raw3996step3Labels := by
      have ha : raw3996step3 = -raw3996step2 := by apply Matrix.ext; change ∀ i j, raw3996step3 i j = -(raw3996step2 i j); unfold raw3996step3 raw3996step2; decide +kernel
      have hl : raw3996step3Labels = raw3996step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3996step3 raw3996step3Labels = mixedMoment B raw3996step4 raw3996step4Labels := by
      have ha : raw3996step4 = raw3996step3 := by apply Matrix.ext; unfold raw3996step4 raw3996step3; decide +kernel
      have hl : raw3996step3Labels = labelEmbedding1 ∘ raw3996step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3996step3 raw3996step3Labels raw3996step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3548 node3548Labels := by rfl

def raw3997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3997Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3997step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![4, -3, -1]]
def raw3997step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -2, 0], ![2, 2, -4]]
def raw3997step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3997step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -2, 0], ![2, 2, -4]]
def raw3997step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3997 raw3997Labels = mixedMoment B node1629 node1629Labels := by
  calc
    mixedMoment B raw3997 raw3997Labels = mixedMoment B raw3997step0 raw3997step0Labels := by
      have hz : ∀ j, raw3997 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3997step0 = (fun i j => raw3997 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3997step0 raw3997; decide +kernel
      have hl : raw3997step0Labels = raw3997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3997 raw3997Labels permutation434 hz
    mixedMoment B raw3997step0 raw3997step0Labels = mixedMoment B raw3997step1 raw3997step1Labels := by
      have hz : ∀ j, raw3997step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3997step1 = (fun i j => raw3997step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3997step1 raw3997step0; decide +kernel
      have hl : raw3997step1Labels = raw3997step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3997step0 raw3997step0Labels permutation80 hz
    mixedMoment B raw3997step1 raw3997step1Labels = mixedMoment B raw3997step2 raw3997step2Labels := by
      have ha : raw3997step2 = (fun i j => raw3997step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3997step2 raw3997step1; decide +kernel
      have hl : raw3997step2Labels = raw3997step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3997step1 raw3997step1Labels permutation29 permutation5
    mixedMoment B raw3997step2 raw3997step2Labels = mixedMoment B raw3997step3 raw3997step3Labels := by
      have ha : raw3997step3 = raw3997step2 := by apply Matrix.ext; unfold raw3997step3 raw3997step2; decide +kernel
      have hl : raw3997step2Labels = labelEmbedding1 ∘ raw3997step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3997step2 raw3997step2Labels raw3997step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1629 node1629Labels := by rfl

def raw3998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3998Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3998step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![4, -3, -1]]
def raw3998step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3998step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3998step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3998step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3998 raw3998Labels = mixedMoment B node1729 node1729Labels := by
  calc
    mixedMoment B raw3998 raw3998Labels = mixedMoment B raw3998step0 raw3998step0Labels := by
      have hz : ∀ j, raw3998 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3998step0 = (fun i j => raw3998 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3998step0 raw3998; decide +kernel
      have hl : raw3998step0Labels = raw3998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3998 raw3998Labels permutation434 hz
    mixedMoment B raw3998step0 raw3998step0Labels = mixedMoment B raw3998step1 raw3998step1Labels := by
      have hz : ∀ j, raw3998step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3998step1 = (fun i j => raw3998step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3998step1 raw3998step0; decide +kernel
      have hl : raw3998step1Labels = raw3998step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3998step0 raw3998step0Labels permutation80 hz
    mixedMoment B raw3998step1 raw3998step1Labels = mixedMoment B raw3998step2 raw3998step2Labels := by
      have ha : raw3998step2 = (fun i j => raw3998step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3998step2 raw3998step1; decide +kernel
      have hl : raw3998step2Labels = raw3998step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3998step1 raw3998step1Labels permutation28 permutation5
    mixedMoment B raw3998step2 raw3998step2Labels = mixedMoment B raw3998step3 raw3998step3Labels := by
      have ha : raw3998step3 = raw3998step2 := by apply Matrix.ext; unfold raw3998step3 raw3998step2; decide +kernel
      have hl : raw3998step2Labels = labelEmbedding1 ∘ raw3998step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3998step2 raw3998step2Labels raw3998step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1729 node1729Labels := by rfl

def raw3999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3999Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![4, -3, -1]]
def raw3999step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw3999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3999step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw3999step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw3999step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical3999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3999 raw3999Labels = mixedMoment B node1624 node1624Labels := by
  calc
    mixedMoment B raw3999 raw3999Labels = mixedMoment B raw3999step0 raw3999step0Labels := by
      have hz : ∀ j, raw3999 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3999step0 = (fun i j => raw3999 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3999step0 raw3999; decide +kernel
      have hl : raw3999step0Labels = raw3999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3999 raw3999Labels permutation434 hz
    mixedMoment B raw3999step0 raw3999step0Labels = mixedMoment B raw3999step1 raw3999step1Labels := by
      have ha : raw3999step1 = (fun i j => raw3999step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3999step1 raw3999step0; decide +kernel
      have hl : raw3999step1Labels = raw3999step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3999step0 raw3999step0Labels permutation136 permutation5
    mixedMoment B raw3999step1 raw3999step1Labels = mixedMoment B raw3999step2 raw3999step2Labels := by
      have ha : raw3999step2 = raw3999step1 := by apply Matrix.ext; unfold raw3999step2 raw3999step1; decide +kernel
      have hl : raw3999step1Labels = labelEmbedding1 ∘ raw3999step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3999step1 raw3999step1Labels raw3999step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1624 node1624Labels := by rfl

def raw4000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![4, -3, -1]]
def raw4000Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![4, -3, -1]]
def raw4000step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4000step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw4000step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4000 raw4000Labels = mixedMoment B node1624 node1624Labels := by
  calc
    mixedMoment B raw4000 raw4000Labels = mixedMoment B raw4000step0 raw4000step0Labels := by
      have hz : ∀ j, raw4000 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4000step0 = (fun i j => raw4000 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4000step0 raw4000; decide +kernel
      have hl : raw4000step0Labels = raw4000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4000 raw4000Labels permutation346 hz
    mixedMoment B raw4000step0 raw4000step0Labels = mixedMoment B raw4000step1 raw4000step1Labels := by
      have ha : raw4000step1 = (fun i j => raw4000step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4000step1 raw4000step0; decide +kernel
      have hl : raw4000step1Labels = raw4000step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4000step0 raw4000step0Labels permutation136 permutation5
    mixedMoment B raw4000step1 raw4000step1Labels = mixedMoment B raw4000step2 raw4000step2Labels := by
      have ha : raw4000step2 = raw4000step1 := by apply Matrix.ext; unfold raw4000step2 raw4000step1; decide +kernel
      have hl : raw4000step1Labels = labelEmbedding1 ∘ raw4000step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4000step1 raw4000step1Labels raw4000step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1624 node1624Labels := by rfl

def raw4001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![4, -3, -1]]
def raw4001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![4, -3, -1]]
def raw4001step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![4, -3, -1]]
def raw4001step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw4001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 2, -3], ![3, -2, -1]]
def raw4001step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw4001step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 2, -3], ![3, -2, -1]]
def raw4001step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4001 raw4001Labels = mixedMoment B node1628 node1628Labels := by
  calc
    mixedMoment B raw4001 raw4001Labels = mixedMoment B raw4001step0 raw4001step0Labels := by
      have hz : ∀ j, raw4001 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4001step0 = (fun i j => raw4001 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4001step0 raw4001; decide +kernel
      have hl : raw4001step0Labels = raw4001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4001 raw4001Labels permutation434 hz
    mixedMoment B raw4001step0 raw4001step0Labels = mixedMoment B raw4001step1 raw4001step1Labels := by
      have hz : ∀ j, raw4001step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4001step1 = (fun i j => raw4001step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4001step1 raw4001step0; decide +kernel
      have hl : raw4001step1Labels = raw4001step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4001step0 raw4001step0Labels permutation80 hz
    mixedMoment B raw4001step1 raw4001step1Labels = mixedMoment B raw4001step2 raw4001step2Labels := by
      have ha : raw4001step2 = (fun i j => raw4001step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw4001step2 raw4001step1; decide +kernel
      have hl : raw4001step2Labels = raw4001step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4001step1 raw4001step1Labels permutation28 permutation5
    mixedMoment B raw4001step2 raw4001step2Labels = mixedMoment B raw4001step3 raw4001step3Labels := by
      have ha : raw4001step3 = raw4001step2 := by apply Matrix.ext; unfold raw4001step3 raw4001step2; decide +kernel
      have hl : raw4001step2Labels = labelEmbedding1 ∘ raw4001step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4001step2 raw4001step2Labels raw4001step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1628 node1628Labels := by rfl

def raw4002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4002Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4002step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4002step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4002 raw4002Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw4002 raw4002Labels = mixedMoment B raw4002step0 raw4002step0Labels := by
      have hz : ∀ j, raw4002 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4002step0 = (fun i j => raw4002 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4002step0 raw4002; decide +kernel
      have hl : raw4002step0Labels = raw4002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4002 raw4002Labels permutation434 hz
    mixedMoment B raw4002step0 raw4002step0Labels = mixedMoment B raw4002step1 raw4002step1Labels := by
      have hz : ∀ j, raw4002step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4002step1 = (fun i j => raw4002step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4002step1 raw4002step0; decide +kernel
      have hl : raw4002step1Labels = raw4002step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4002step0 raw4002step0Labels permutation80 hz
    _ = mixedMoment B node2734 node2734Labels := by rfl

def raw4003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4003step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4003step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4003step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4003step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-2, 0, 2]]
def raw4003step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4003step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw4003step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4003 raw4003Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw4003 raw4003Labels = mixedMoment B raw4003step0 raw4003step0Labels := by
      have hz : ∀ j, raw4003 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4003step0 = (fun i j => raw4003 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4003step0 raw4003; decide +kernel
      have hl : raw4003step0Labels = raw4003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4003 raw4003Labels permutation434 hz
    mixedMoment B raw4003step0 raw4003step0Labels = mixedMoment B raw4003step1 raw4003step1Labels := by
      have hz : ∀ j, raw4003step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4003step1 = (fun i j => raw4003step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4003step1 raw4003step0; decide +kernel
      have hl : raw4003step1Labels = raw4003step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4003step0 raw4003step0Labels permutation80 hz
    mixedMoment B raw4003step1 raw4003step1Labels = mixedMoment B raw4003step2 raw4003step2Labels := by
      have ha : raw4003step2 = (fun i j => raw4003step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4003step2 raw4003step1; decide +kernel
      have hl : raw4003step2Labels = raw4003step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4003step1 raw4003step1Labels permutation31 permutation2
    mixedMoment B raw4003step2 raw4003step2Labels = mixedMoment B raw4003step3 raw4003step3Labels := by
      have ha : raw4003step3 = -raw4003step2 := by apply Matrix.ext; change ∀ i j, raw4003step3 i j = -(raw4003step2 i j); unfold raw4003step3 raw4003step2; decide +kernel
      have hl : raw4003step3Labels = raw4003step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw4004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4004Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4004step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw4004step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4004step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4004 raw4004Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw4004 raw4004Labels = mixedMoment B raw4004step0 raw4004step0Labels := by
      have hz : ∀ j, raw4004 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4004step0 = (fun i j => raw4004 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4004step0 raw4004; decide +kernel
      have hl : raw4004step0Labels = raw4004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4004 raw4004Labels permutation434 hz
    mixedMoment B raw4004step0 raw4004step0Labels = mixedMoment B raw4004step1 raw4004step1Labels := by
      have ha : raw4004step1 = (fun i j => raw4004step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4004step1 raw4004step0; decide +kernel
      have hl : raw4004step1Labels = raw4004step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4004step0 raw4004step0Labels permutation149 permutation2
    mixedMoment B raw4004step1 raw4004step1Labels = mixedMoment B raw4004step2 raw4004step2Labels := by
      have ha : raw4004step2 = -raw4004step1 := by apply Matrix.ext; change ∀ i j, raw4004step2 i j = -(raw4004step1 i j); unfold raw4004step2 raw4004step1; decide +kernel
      have hl : raw4004step2Labels = raw4004step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw4005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw4005step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4005step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw4005step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4005 raw4005Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw4005 raw4005Labels = mixedMoment B raw4005step0 raw4005step0Labels := by
      have hz : ∀ j, raw4005 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4005step0 = (fun i j => raw4005 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4005step0 raw4005; decide +kernel
      have hl : raw4005step0Labels = raw4005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4005 raw4005Labels permutation346 hz
    mixedMoment B raw4005step0 raw4005step0Labels = mixedMoment B raw4005step1 raw4005step1Labels := by
      have ha : raw4005step1 = (fun i j => raw4005step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4005step1 raw4005step0; decide +kernel
      have hl : raw4005step1Labels = raw4005step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4005step0 raw4005step0Labels permutation149 permutation2
    mixedMoment B raw4005step1 raw4005step1Labels = mixedMoment B raw4005step2 raw4005step2Labels := by
      have ha : raw4005step2 = -raw4005step1 := by apply Matrix.ext; change ∀ i j, raw4005step2 i j = -(raw4005step1 i j); unfold raw4005step2 raw4005step1; decide +kernel
      have hl : raw4005step2Labels = raw4005step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw4006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw4006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw4006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4006step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![3, -2, -1]]
def raw4006step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4006step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 3, -1]]
def raw4006step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4006step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw4006step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4006 raw4006Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw4006 raw4006Labels = mixedMoment B raw4006step0 raw4006step0Labels := by
      have hz : ∀ j, raw4006 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4006step0 = (fun i j => raw4006 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4006step0 raw4006; decide +kernel
      have hl : raw4006step0Labels = raw4006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4006 raw4006Labels permutation434 hz
    mixedMoment B raw4006step0 raw4006step0Labels = mixedMoment B raw4006step1 raw4006step1Labels := by
      have hz : ∀ j, raw4006step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4006step1 = (fun i j => raw4006step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4006step1 raw4006step0; decide +kernel
      have hl : raw4006step1Labels = raw4006step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4006step0 raw4006step0Labels permutation80 hz
    mixedMoment B raw4006step1 raw4006step1Labels = mixedMoment B raw4006step2 raw4006step2Labels := by
      have ha : raw4006step2 = (fun i j => raw4006step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4006step2 raw4006step1; decide +kernel
      have hl : raw4006step2Labels = raw4006step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4006step1 raw4006step1Labels permutation20 permutation4
    mixedMoment B raw4006step2 raw4006step2Labels = mixedMoment B raw4006step3 raw4006step3Labels := by
      have ha : raw4006step3 = -raw4006step2 := by apply Matrix.ext; change ∀ i j, raw4006step3 i j = -(raw4006step2 i j); unfold raw4006step3 raw4006step2; decide +kernel
      have hl : raw4006step3Labels = raw4006step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2777 node2777Labels := by rfl

def raw4007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw4007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw4007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4007step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw4007step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4007 raw4007Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw4007 raw4007Labels = mixedMoment B raw4007step0 raw4007step0Labels := by
      have hz : ∀ j, raw4007 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4007step0 = (fun i j => raw4007 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4007step0 raw4007; decide +kernel
      have hl : raw4007step0Labels = raw4007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4007 raw4007Labels permutation434 hz
    mixedMoment B raw4007step0 raw4007step0Labels = mixedMoment B raw4007step1 raw4007step1Labels := by
      have hz : ∀ j, raw4007step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4007step1 = (fun i j => raw4007step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4007step1 raw4007step0; decide +kernel
      have hl : raw4007step1Labels = raw4007step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4007step0 raw4007step0Labels permutation80 hz
    _ = mixedMoment B node3907 node3907Labels := by rfl

def raw4008 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]
def raw4008Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4008step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![2, -2], ![1, -1]]
def raw4008step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4008step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw4008step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw4008step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw4008step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical4008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4008 raw4008Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw4008 raw4008Labels = mixedMoment B raw4008step0 raw4008step0Labels := by
      have hz : ∀ j, raw4008 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4008step0 = (fun i j => raw4008 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4008step0 raw4008; decide +kernel
      have hl : raw4008step0Labels = raw4008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4008 raw4008Labels permutation434 hz
    mixedMoment B raw4008step0 raw4008step0Labels = mixedMoment B raw4008step1 raw4008step1Labels := by
      have hz : ∀ j, raw4008step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4008step1 = (fun i j => raw4008step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4008step1 raw4008step0; decide +kernel
      have hl : raw4008step1Labels = raw4008step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4008step0 raw4008step0Labels permutation80 hz
    mixedMoment B raw4008step1 raw4008step1Labels = mixedMoment B raw4008step2 raw4008step2Labels := by
      have ha : raw4008step2 = (fun i j => raw4008step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw4008step2 raw4008step1; decide +kernel
      have hl : raw4008step2Labels = raw4008step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4008step1 raw4008step1Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw4009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4009step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4009step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4009step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw4009step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4009 raw4009Labels = mixedMoment B node1279 node1279Labels := by
  calc
    mixedMoment B raw4009 raw4009Labels = mixedMoment B raw4009step0 raw4009step0Labels := by
      have hz : ∀ j, raw4009 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4009step0 = (fun i j => raw4009 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4009step0 raw4009; decide +kernel
      have hl : raw4009step0Labels = raw4009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4009 raw4009Labels permutation434 hz
    mixedMoment B raw4009step0 raw4009step0Labels = mixedMoment B raw4009step1 raw4009step1Labels := by
      have hz : ∀ j, raw4009step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4009step1 = (fun i j => raw4009step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4009step1 raw4009step0; decide +kernel
      have hl : raw4009step1Labels = raw4009step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4009step0 raw4009step0Labels permutation80 hz
    mixedMoment B raw4009step1 raw4009step1Labels = mixedMoment B raw4009step2 raw4009step2Labels := by
      have ha : raw4009step2 = (fun i j => raw4009step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4009step2 raw4009step1; decide +kernel
      have hl : raw4009step2Labels = raw4009step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4009step1 raw4009step1Labels permutation10 permutation2
    _ = mixedMoment B node1279 node1279Labels := by rfl

def raw4010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4010Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4010step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4010 raw4010Labels = mixedMoment B node1224 node1224Labels := by
  calc
    mixedMoment B raw4010 raw4010Labels = mixedMoment B raw4010step0 raw4010step0Labels := by
      have hz : ∀ j, raw4010 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4010step0 = (fun i j => raw4010 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4010step0 raw4010; decide +kernel
      have hl : raw4010step0Labels = raw4010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4010 raw4010Labels permutation434 hz
    mixedMoment B raw4010step0 raw4010step0Labels = mixedMoment B raw4010step1 raw4010step1Labels := by
      have ha : raw4010step1 = (fun i j => raw4010step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4010step1 raw4010step0; decide +kernel
      have hl : raw4010step1Labels = raw4010step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4010step0 raw4010step0Labels permutation34 permutation2
    _ = mixedMoment B node1224 node1224Labels := by rfl

def raw4011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4011Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4011step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4011 raw4011Labels = mixedMoment B node1224 node1224Labels := by
  calc
    mixedMoment B raw4011 raw4011Labels = mixedMoment B raw4011step0 raw4011step0Labels := by
      have hz : ∀ j, raw4011 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4011step0 = (fun i j => raw4011 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4011step0 raw4011; decide +kernel
      have hl : raw4011step0Labels = raw4011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4011 raw4011Labels permutation346 hz
    mixedMoment B raw4011step0 raw4011step0Labels = mixedMoment B raw4011step1 raw4011step1Labels := by
      have ha : raw4011step1 = (fun i j => raw4011step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4011step1 raw4011step0; decide +kernel
      have hl : raw4011step1Labels = raw4011step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4011step0 raw4011step0Labels permutation34 permutation2
    _ = mixedMoment B node1224 node1224Labels := by rfl

def raw4012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4012step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4012step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4012step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4012 raw4012Labels = mixedMoment B node1243 node1243Labels := by
  calc
    mixedMoment B raw4012 raw4012Labels = mixedMoment B raw4012step0 raw4012step0Labels := by
      have hz : ∀ j, raw4012 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4012step0 = (fun i j => raw4012 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4012step0 raw4012; decide +kernel
      have hl : raw4012step0Labels = raw4012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4012 raw4012Labels permutation434 hz
    mixedMoment B raw4012step0 raw4012step0Labels = mixedMoment B raw4012step1 raw4012step1Labels := by
      have hz : ∀ j, raw4012step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4012step1 = (fun i j => raw4012step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4012step1 raw4012step0; decide +kernel
      have hl : raw4012step1Labels = raw4012step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4012step0 raw4012step0Labels permutation80 hz
    _ = mixedMoment B node1243 node1243Labels := by rfl

def raw4013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw4013Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw4013step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4013step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![4, -3, -1]]
def raw4013step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4013 raw4013Labels = mixedMoment B node1227 node1227Labels := by
  calc
    mixedMoment B raw4013 raw4013Labels = mixedMoment B raw4013step0 raw4013step0Labels := by
      have hz : ∀ j, raw4013 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4013step0 = (fun i j => raw4013 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4013step0 raw4013; decide +kernel
      have hl : raw4013step0Labels = raw4013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4013 raw4013Labels permutation434 hz
    mixedMoment B raw4013step0 raw4013step0Labels = mixedMoment B raw4013step1 raw4013step1Labels := by
      have hz : ∀ j, raw4013step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4013step1 = (fun i j => raw4013step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4013step1 raw4013step0; decide +kernel
      have hl : raw4013step1Labels = raw4013step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4013step0 raw4013step0Labels permutation80 hz
    _ = mixedMoment B node1227 node1227Labels := by rfl

def raw4014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4014step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw4014step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4014 raw4014Labels = mixedMoment B node2579 node2579Labels := by
  calc
    mixedMoment B raw4014 raw4014Labels = mixedMoment B raw4014step0 raw4014step0Labels := by
      have hz : ∀ j, raw4014 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4014step0 = (fun i j => raw4014 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4014step0 raw4014; decide +kernel
      have hl : raw4014step0Labels = raw4014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4014 raw4014Labels permutation434 hz
    mixedMoment B raw4014step0 raw4014step0Labels = mixedMoment B raw4014step1 raw4014step1Labels := by
      have ha : raw4014step1 = (fun i j => raw4014step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4014step1 raw4014step0; decide +kernel
      have hl : raw4014step1Labels = raw4014step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4014step0 raw4014step0Labels permutation40 permutation2
    _ = mixedMoment B node2579 node2579Labels := by rfl

def raw4015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4015step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw4015step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4015 raw4015Labels = mixedMoment B node2579 node2579Labels := by
  calc
    mixedMoment B raw4015 raw4015Labels = mixedMoment B raw4015step0 raw4015step0Labels := by
      have hz : ∀ j, raw4015 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4015step0 = (fun i j => raw4015 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4015step0 raw4015; decide +kernel
      have hl : raw4015step0Labels = raw4015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4015 raw4015Labels permutation346 hz
    mixedMoment B raw4015step0 raw4015step0Labels = mixedMoment B raw4015step1 raw4015step1Labels := by
      have ha : raw4015step1 = (fun i j => raw4015step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4015step1 raw4015step0; decide +kernel
      have hl : raw4015step1Labels = raw4015step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4015step0 raw4015step0Labels permutation40 permutation2
    _ = mixedMoment B node2579 node2579Labels := by rfl

def raw4016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw4016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw4016step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![3, -2, -1]]
def raw4016step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4016step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def raw4016step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4016 raw4016Labels = mixedMoment B node2651 node2651Labels := by
  calc
    mixedMoment B raw4016 raw4016Labels = mixedMoment B raw4016step0 raw4016step0Labels := by
      have hz : ∀ j, raw4016 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4016step0 = (fun i j => raw4016 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4016step0 raw4016; decide +kernel
      have hl : raw4016step0Labels = raw4016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4016 raw4016Labels permutation434 hz
    mixedMoment B raw4016step0 raw4016step0Labels = mixedMoment B raw4016step1 raw4016step1Labels := by
      have hz : ∀ j, raw4016step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4016step1 = (fun i j => raw4016step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4016step1 raw4016step0; decide +kernel
      have hl : raw4016step1Labels = raw4016step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4016step0 raw4016step0Labels permutation80 hz
    mixedMoment B raw4016step1 raw4016step1Labels = mixedMoment B raw4016step2 raw4016step2Labels := by
      have ha : raw4016step2 = (fun i j => raw4016step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4016step2 raw4016step1; decide +kernel
      have hl : raw4016step2Labels = raw4016step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4016step1 raw4016step1Labels permutation10 permutation2
    _ = mixedMoment B node2651 node2651Labels := by rfl

def raw4017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw4017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw4017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw4017step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4017step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw4017step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4017 raw4017Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw4017 raw4017Labels = mixedMoment B raw4017step0 raw4017step0Labels := by
      have hz : ∀ j, raw4017 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4017step0 = (fun i j => raw4017 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4017step0 raw4017; decide +kernel
      have hl : raw4017step0Labels = raw4017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4017 raw4017Labels permutation434 hz
    mixedMoment B raw4017step0 raw4017step0Labels = mixedMoment B raw4017step1 raw4017step1Labels := by
      have hz : ∀ j, raw4017step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4017step1 = (fun i j => raw4017step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4017step1 raw4017step0; decide +kernel
      have hl : raw4017step1Labels = raw4017step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4017step0 raw4017step0Labels permutation80 hz
    mixedMoment B raw4017step1 raw4017step1Labels = mixedMoment B raw4017step2 raw4017step2Labels := by
      have ha : raw4017step2 = (fun i j => raw4017step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4017step2 raw4017step1; decide +kernel
      have hl : raw4017step2Labels = raw4017step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4017step1 raw4017step1Labels permutation10 permutation2
    _ = mixedMoment B node2774 node2774Labels := by rfl

def raw4018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4018step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4018step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4018 raw4018Labels = mixedMoment B node2495 node2495Labels := by
  calc
    mixedMoment B raw4018 raw4018Labels = mixedMoment B raw4018step0 raw4018step0Labels := by
      have hz : ∀ j, raw4018 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4018step0 = (fun i j => raw4018 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4018step0 raw4018; decide +kernel
      have hl : raw4018step0Labels = raw4018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4018 raw4018Labels permutation434 hz
    mixedMoment B raw4018step0 raw4018step0Labels = mixedMoment B raw4018step1 raw4018step1Labels := by
      have ha : raw4018step1 = (fun i j => raw4018step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4018step1 raw4018step0; decide +kernel
      have hl : raw4018step1Labels = raw4018step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4018step0 raw4018step0Labels permutation34 permutation2
    _ = mixedMoment B node2495 node2495Labels := by rfl

def raw4019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4019Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4019step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4019step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4019 raw4019Labels = mixedMoment B node2495 node2495Labels := by
  calc
    mixedMoment B raw4019 raw4019Labels = mixedMoment B raw4019step0 raw4019step0Labels := by
      have hz : ∀ j, raw4019 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4019step0 = (fun i j => raw4019 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4019step0 raw4019; decide +kernel
      have hl : raw4019step0Labels = raw4019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4019 raw4019Labels permutation346 hz
    mixedMoment B raw4019step0 raw4019step0Labels = mixedMoment B raw4019step1 raw4019step1Labels := by
      have ha : raw4019step1 = (fun i j => raw4019step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4019step1 raw4019step0; decide +kernel
      have hl : raw4019step1Labels = raw4019step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4019step0 raw4019step0Labels permutation34 permutation2
    _ = mixedMoment B node2495 node2495Labels := by rfl

def raw4020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4020step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4020 raw4020Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw4020 raw4020Labels = mixedMoment B raw4020step0 raw4020step0Labels := by
      have hz : ∀ j, raw4020 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4020step0 = (fun i j => raw4020 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4020step0 raw4020; decide +kernel
      have hl : raw4020step0Labels = raw4020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4020 raw4020Labels permutation434 hz
    mixedMoment B raw4020step0 raw4020step0Labels = mixedMoment B raw4020step1 raw4020step1Labels := by
      have hz : ∀ j, raw4020step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4020step1 = (fun i j => raw4020step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4020step1 raw4020step0; decide +kernel
      have hl : raw4020step1Labels = raw4020step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4020step0 raw4020step0Labels permutation80 hz
    _ = mixedMoment B node2519 node2519Labels := by rfl

def raw4021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw4021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw4021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4021step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![4, -3, -1]]
def raw4021step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4021step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![-1, 0, 1], ![-3, 1, 2]]
def raw4021step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4021step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw4021step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4021 raw4021Labels = mixedMoment B node1372 node1372Labels := by
  calc
    mixedMoment B raw4021 raw4021Labels = mixedMoment B raw4021step0 raw4021step0Labels := by
      have hz : ∀ j, raw4021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4021step0 = (fun i j => raw4021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4021step0 raw4021; decide +kernel
      have hl : raw4021step0Labels = raw4021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4021 raw4021Labels permutation434 hz
    mixedMoment B raw4021step0 raw4021step0Labels = mixedMoment B raw4021step1 raw4021step1Labels := by
      have hz : ∀ j, raw4021step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4021step1 = (fun i j => raw4021step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4021step1 raw4021step0; decide +kernel
      have hl : raw4021step1Labels = raw4021step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4021step0 raw4021step0Labels permutation80 hz
    mixedMoment B raw4021step1 raw4021step1Labels = mixedMoment B raw4021step2 raw4021step2Labels := by
      have ha : raw4021step2 = (fun i j => raw4021step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4021step2 raw4021step1; decide +kernel
      have hl : raw4021step2Labels = raw4021step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4021step1 raw4021step1Labels permutation31 permutation2
    mixedMoment B raw4021step2 raw4021step2Labels = mixedMoment B raw4021step3 raw4021step3Labels := by
      have ha : raw4021step3 = -raw4021step2 := by apply Matrix.ext; change ∀ i j, raw4021step3 i j = -(raw4021step2 i j); unfold raw4021step3 raw4021step2; decide +kernel
      have hl : raw4021step3Labels = raw4021step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1372 node1372Labels := by rfl

def raw4022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4022step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4022step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4022 raw4022Labels = mixedMoment B node2547 node2547Labels := by
  calc
    mixedMoment B raw4022 raw4022Labels = mixedMoment B raw4022step0 raw4022step0Labels := by
      have ha : raw4022step0 = (fun i j => raw4022 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4022step0 raw4022; decide +kernel
      have hl : raw4022step0Labels = raw4022Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4022 raw4022Labels permutation202 permutation2
    _ = mixedMoment B node2547 node2547Labels := by rfl

def raw4023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw4023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw4023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def raw4023step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4023 raw4023Labels = mixedMoment B node2647 node2647Labels := by
  calc
    mixedMoment B raw4023 raw4023Labels = mixedMoment B raw4023step0 raw4023step0Labels := by
      have hz : ∀ j, raw4023 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4023step0 = (fun i j => raw4023 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4023step0 raw4023; decide +kernel
      have hl : raw4023step0Labels = raw4023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4023 raw4023Labels permutation434 hz
    mixedMoment B raw4023step0 raw4023step0Labels = mixedMoment B raw4023step1 raw4023step1Labels := by
      have ha : raw4023step1 = (fun i j => raw4023step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4023step1 raw4023step0; decide +kernel
      have hl : raw4023step1Labels = raw4023step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4023step0 raw4023step0Labels permutation44 permutation2
    _ = mixedMoment B node2647 node2647Labels := by rfl

def raw4024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw4024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw4024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw4024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4024 raw4024Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw4024 raw4024Labels = mixedMoment B raw4024step0 raw4024step0Labels := by
      have hz : ∀ j, raw4024 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4024step0 = (fun i j => raw4024 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4024step0 raw4024; decide +kernel
      have hl : raw4024step0Labels = raw4024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4024 raw4024Labels permutation434 hz
    mixedMoment B raw4024step0 raw4024step0Labels = mixedMoment B raw4024step1 raw4024step1Labels := by
      have ha : raw4024step1 = (fun i j => raw4024step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4024step1 raw4024step0; decide +kernel
      have hl : raw4024step1Labels = raw4024step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4024step0 raw4024step0Labels permutation34 permutation2
    _ = mixedMoment B node2731 node2731Labels := by rfl

def raw4025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![3, -2, -1]]
def raw4025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw4025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4025 raw4025Labels = mixedMoment B node2547 node2547Labels := by
  calc
    mixedMoment B raw4025 raw4025Labels = mixedMoment B raw4025step0 raw4025step0Labels := by
      have ha : raw4025step0 = (fun i j => raw4025 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4025step0 raw4025; decide +kernel
      have hl : raw4025step0Labels = raw4025Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4025 raw4025Labels permutation178 permutation2
    _ = mixedMoment B node2547 node2547Labels := by rfl

def raw4026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4026step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4026 raw4026Labels = mixedMoment B node2558 node2558Labels := by
  calc
    mixedMoment B raw4026 raw4026Labels = mixedMoment B raw4026step0 raw4026step0Labels := by
      have hz : ∀ j, raw4026 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4026step0 = (fun i j => raw4026 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4026step0 raw4026; decide +kernel
      have hl : raw4026step0Labels = raw4026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4026 raw4026Labels permutation434 hz
    mixedMoment B raw4026step0 raw4026step0Labels = mixedMoment B raw4026step1 raw4026step1Labels := by
      have ha : raw4026step1 = (fun i j => raw4026step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4026step1 raw4026step0; decide +kernel
      have hl : raw4026step1Labels = raw4026step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4026step0 raw4026step0Labels permutation38 permutation2
    _ = mixedMoment B node2558 node2558Labels := by rfl

def raw4027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![4, -3, -1]]
def raw4027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![4, -3, -1]]
def raw4027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4027step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4027 raw4027Labels = mixedMoment B node1359 node1359Labels := by
  calc
    mixedMoment B raw4027 raw4027Labels = mixedMoment B raw4027step0 raw4027step0Labels := by
      have hz : ∀ j, raw4027 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4027step0 = (fun i j => raw4027 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4027step0 raw4027; decide +kernel
      have hl : raw4027step0Labels = raw4027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4027 raw4027Labels permutation434 hz
    mixedMoment B raw4027step0 raw4027step0Labels = mixedMoment B raw4027step1 raw4027step1Labels := by
      have ha : raw4027step1 = (fun i j => raw4027step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4027step1 raw4027step0; decide +kernel
      have hl : raw4027step1Labels = raw4027step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4027step0 raw4027step0Labels permutation149 permutation2
    mixedMoment B raw4027step1 raw4027step1Labels = mixedMoment B raw4027step2 raw4027step2Labels := by
      have ha : raw4027step2 = -raw4027step1 := by apply Matrix.ext; change ∀ i j, raw4027step2 i j = -(raw4027step1 i j); unfold raw4027step2 raw4027step1; decide +kernel
      have hl : raw4027step2Labels = raw4027step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1359 node1359Labels := by rfl

def raw4028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw4028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw4028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4028 raw4028Labels = mixedMoment B node2558 node2558Labels := by
  calc
    mixedMoment B raw4028 raw4028Labels = mixedMoment B raw4028step0 raw4028step0Labels := by
      have hz : ∀ j, raw4028 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4028step0 = (fun i j => raw4028 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4028step0 raw4028; decide +kernel
      have hl : raw4028step0Labels = raw4028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4028 raw4028Labels permutation346 hz
    mixedMoment B raw4028step0 raw4028step0Labels = mixedMoment B raw4028step1 raw4028step1Labels := by
      have ha : raw4028step1 = (fun i j => raw4028step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4028step1 raw4028step0; decide +kernel
      have hl : raw4028step1Labels = raw4028step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4028step0 raw4028step0Labels permutation38 permutation2
    _ = mixedMoment B node2558 node2558Labels := by rfl

def raw4029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw4029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw4029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4029step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw4029step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4029 raw4029Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw4029 raw4029Labels = mixedMoment B raw4029step0 raw4029step0Labels := by
      have hz : ∀ j, raw4029 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4029step0 = (fun i j => raw4029 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4029step0 raw4029; decide +kernel
      have hl : raw4029step0Labels = raw4029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4029 raw4029Labels permutation434 hz
    mixedMoment B raw4029step0 raw4029step0Labels = mixedMoment B raw4029step1 raw4029step1Labels := by
      have hz : ∀ j, raw4029step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4029step1 = (fun i j => raw4029step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4029step1 raw4029step0; decide +kernel
      have hl : raw4029step1Labels = raw4029step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4029step0 raw4029step0Labels permutation80 hz
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw4030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw4030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![3, -2, -1]]
def raw4030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def raw4030step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4030 raw4030Labels = mixedMoment B node2647 node2647Labels := by
  calc
    mixedMoment B raw4030 raw4030Labels = mixedMoment B raw4030step0 raw4030step0Labels := by
      have hz : ∀ j, raw4030 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4030step0 = (fun i j => raw4030 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4030step0 raw4030; decide +kernel
      have hl : raw4030step0Labels = raw4030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4030 raw4030Labels permutation346 hz
    mixedMoment B raw4030step0 raw4030step0Labels = mixedMoment B raw4030step1 raw4030step1Labels := by
      have ha : raw4030step1 = (fun i j => raw4030step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4030step1 raw4030step0; decide +kernel
      have hl : raw4030step1Labels = raw4030step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4030step0 raw4030step0Labels permutation44 permutation2
    _ = mixedMoment B node2647 node2647Labels := by rfl

def raw4031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![4, -3, -1]]
def raw4031Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![4, -3, -1]]
def raw4031step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4031step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![4, -3, -1]]
def raw4031step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4031step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -3, -1], ![0, -1, 1], ![-1, 3, -2], ![-3, 1, 2]]
def raw4031step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4031step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![3, -1, -2]]
def raw4031step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4031 raw4031Labels = mixedMoment B node1424 node1424Labels := by
  calc
    mixedMoment B raw4031 raw4031Labels = mixedMoment B raw4031step0 raw4031step0Labels := by
      have hz : ∀ j, raw4031 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4031step0 = (fun i j => raw4031 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4031step0 raw4031; decide +kernel
      have hl : raw4031step0Labels = raw4031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4031 raw4031Labels permutation434 hz
    mixedMoment B raw4031step0 raw4031step0Labels = mixedMoment B raw4031step1 raw4031step1Labels := by
      have hz : ∀ j, raw4031step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4031step1 = (fun i j => raw4031step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4031step1 raw4031step0; decide +kernel
      have hl : raw4031step1Labels = raw4031step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4031step0 raw4031step0Labels permutation80 hz
    mixedMoment B raw4031step1 raw4031step1Labels = mixedMoment B raw4031step2 raw4031step2Labels := by
      have ha : raw4031step2 = (fun i j => raw4031step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4031step2 raw4031step1; decide +kernel
      have hl : raw4031step2Labels = raw4031step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4031step1 raw4031step1Labels permutation29 permutation2
    mixedMoment B raw4031step2 raw4031step2Labels = mixedMoment B raw4031step3 raw4031step3Labels := by
      have ha : raw4031step3 = -raw4031step2 := by apply Matrix.ext; change ∀ i j, raw4031step3 i j = -(raw4031step2 i j); unfold raw4031step3 raw4031step2; decide +kernel
      have hl : raw4031step3Labels = raw4031step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1424 node1424Labels := by rfl

def raw4032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![4, -3, -1]]
def raw4032Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![4, -3, -1]]
def raw4032step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw4032step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4032step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw4032step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4032 raw4032Labels = mixedMoment B node1359 node1359Labels := by
  calc
    mixedMoment B raw4032 raw4032Labels = mixedMoment B raw4032step0 raw4032step0Labels := by
      have hz : ∀ j, raw4032 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4032step0 = (fun i j => raw4032 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4032step0 raw4032; decide +kernel
      have hl : raw4032step0Labels = raw4032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4032 raw4032Labels permutation346 hz
    mixedMoment B raw4032step0 raw4032step0Labels = mixedMoment B raw4032step1 raw4032step1Labels := by
      have ha : raw4032step1 = (fun i j => raw4032step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4032step1 raw4032step0; decide +kernel
      have hl : raw4032step1Labels = raw4032step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4032step0 raw4032step0Labels permutation149 permutation2
    mixedMoment B raw4032step1 raw4032step1Labels = mixedMoment B raw4032step2 raw4032step2Labels := by
      have ha : raw4032step2 = -raw4032step1 := by apply Matrix.ext; change ∀ i j, raw4032step2 i j = -(raw4032step1 i j); unfold raw4032step2 raw4032step1; decide +kernel
      have hl : raw4032step2Labels = raw4032step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1359 node1359Labels := by rfl

def raw4033 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4033step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4033step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4033step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4033step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw4033step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4033step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw4033step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4033 raw4033Labels = mixedMoment B node5235 node5235Labels := by
  calc
    mixedMoment B raw4033 raw4033Labels = mixedMoment B raw4033step0 raw4033step0Labels := by
      have hz : ∀ j, raw4033 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4033step0 = (fun i j => raw4033 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4033step0 raw4033; decide +kernel
      have hl : raw4033step0Labels = raw4033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4033 raw4033Labels permutation434 hz
    mixedMoment B raw4033step0 raw4033step0Labels = mixedMoment B raw4033step1 raw4033step1Labels := by
      have hz : ∀ j, raw4033step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4033step1 = (fun i j => raw4033step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4033step1 raw4033step0; decide +kernel
      have hl : raw4033step1Labels = raw4033step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4033step0 raw4033step0Labels permutation80 hz
    mixedMoment B raw4033step1 raw4033step1Labels = mixedMoment B raw4033step2 raw4033step2Labels := by
      have ha : raw4033step2 = (fun i j => raw4033step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4033step2 raw4033step1; decide +kernel
      have hl : raw4033step2Labels = raw4033step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4033step1 raw4033step1Labels permutation10 permutation7
    mixedMoment B raw4033step2 raw4033step2Labels = mixedMoment B raw4033step3 raw4033step3Labels := by
      have ha : raw4033step3 = raw4033step2 := by apply Matrix.ext; unfold raw4033step3 raw4033step2; decide +kernel
      have hl : raw4033step2Labels = labelEmbedding10 ∘ raw4033step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4033step2 raw4033step2Labels raw4033step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5235 node5235Labels := by rfl

def raw4034 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4034step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4034step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4034step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4034step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4034 raw4034Labels = mixedMoment B node5222 node5222Labels := by
  calc
    mixedMoment B raw4034 raw4034Labels = mixedMoment B raw4034step0 raw4034step0Labels := by
      have hz : ∀ j, raw4034 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4034step0 = (fun i j => raw4034 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4034step0 raw4034; decide +kernel
      have hl : raw4034step0Labels = raw4034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4034 raw4034Labels permutation434 hz
    mixedMoment B raw4034step0 raw4034step0Labels = mixedMoment B raw4034step1 raw4034step1Labels := by
      have ha : raw4034step1 = (fun i j => raw4034step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4034step1 raw4034step0; decide +kernel
      have hl : raw4034step1Labels = raw4034step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4034step0 raw4034step0Labels permutation44 permutation7
    mixedMoment B raw4034step1 raw4034step1Labels = mixedMoment B raw4034step2 raw4034step2Labels := by
      have ha : raw4034step2 = raw4034step1 := by apply Matrix.ext; unfold raw4034step2 raw4034step1; decide +kernel
      have hl : raw4034step1Labels = labelEmbedding10 ∘ raw4034step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4034step1 raw4034step1Labels raw4034step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5222 node5222Labels := by rfl

def raw4035 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4035step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4035step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4035step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4035step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4035 raw4035Labels = mixedMoment B node5222 node5222Labels := by
  calc
    mixedMoment B raw4035 raw4035Labels = mixedMoment B raw4035step0 raw4035step0Labels := by
      have hz : ∀ j, raw4035 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4035step0 = (fun i j => raw4035 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4035step0 raw4035; decide +kernel
      have hl : raw4035step0Labels = raw4035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4035 raw4035Labels permutation346 hz
    mixedMoment B raw4035step0 raw4035step0Labels = mixedMoment B raw4035step1 raw4035step1Labels := by
      have ha : raw4035step1 = (fun i j => raw4035step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4035step1 raw4035step0; decide +kernel
      have hl : raw4035step1Labels = raw4035step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4035step0 raw4035step0Labels permutation44 permutation7
    mixedMoment B raw4035step1 raw4035step1Labels = mixedMoment B raw4035step2 raw4035step2Labels := by
      have ha : raw4035step2 = raw4035step1 := by apply Matrix.ext; unfold raw4035step2 raw4035step1; decide +kernel
      have hl : raw4035step1Labels = labelEmbedding10 ∘ raw4035step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4035step1 raw4035step1Labels raw4035step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5222 node5222Labels := by rfl

def raw4036 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4036step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4036step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4036step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4036step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4036step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw4036step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4036step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4036 raw4036Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw4036 raw4036Labels = mixedMoment B raw4036step0 raw4036step0Labels := by
      have hz : ∀ j, raw4036 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4036step0 = (fun i j => raw4036 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4036step0 raw4036; decide +kernel
      have hl : raw4036step0Labels = raw4036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4036 raw4036Labels permutation434 hz
    mixedMoment B raw4036step0 raw4036step0Labels = mixedMoment B raw4036step1 raw4036step1Labels := by
      have hz : ∀ j, raw4036step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4036step1 = (fun i j => raw4036step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4036step1 raw4036step0; decide +kernel
      have hl : raw4036step1Labels = raw4036step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4036step0 raw4036step0Labels permutation80 hz
    mixedMoment B raw4036step1 raw4036step1Labels = mixedMoment B raw4036step2 raw4036step2Labels := by
      have ha : raw4036step2 = (fun i j => raw4036step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw4036step2 raw4036step1; decide +kernel
      have hl : raw4036step2Labels = raw4036step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4036step1 raw4036step1Labels permutation10 permutation7
    mixedMoment B raw4036step2 raw4036step2Labels = mixedMoment B raw4036step3 raw4036step3Labels := by
      have ha : raw4036step3 = raw4036step2 := by apply Matrix.ext; unfold raw4036step3 raw4036step2; decide +kernel
      have hl : raw4036step2Labels = labelEmbedding10 ∘ raw4036step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4036step2 raw4036step2Labels raw4036step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw4037 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4037step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4037step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4037step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4037step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4037step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4037 raw4037Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw4037 raw4037Labels = mixedMoment B raw4037step0 raw4037step0Labels := by
      have hz : ∀ j, raw4037 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4037step0 = (fun i j => raw4037 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4037step0 raw4037; decide +kernel
      have hl : raw4037step0Labels = raw4037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4037 raw4037Labels permutation434 hz
    mixedMoment B raw4037step0 raw4037step0Labels = mixedMoment B raw4037step1 raw4037step1Labels := by
      have hz : ∀ j, raw4037step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4037step1 = (fun i j => raw4037step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4037step1 raw4037step0; decide +kernel
      have hl : raw4037step1Labels = raw4037step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4037step0 raw4037step0Labels permutation80 hz
    mixedMoment B raw4037step1 raw4037step1Labels = mixedMoment B raw4037step2 raw4037step2Labels := by
      have ha : raw4037step2 = (fun i j => raw4037step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4037step2 raw4037step1; decide +kernel
      have hl : raw4037step2Labels = raw4037step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4037step1 raw4037step1Labels permutation29 permutation2
    _ = mixedMoment B node4845 node4845Labels := by rfl

def raw4038 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4038step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4038step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4038step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4038step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4038step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4038 raw4038Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw4038 raw4038Labels = mixedMoment B raw4038step0 raw4038step0Labels := by
      have hz : ∀ j, raw4038 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4038step0 = (fun i j => raw4038 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4038step0 raw4038; decide +kernel
      have hl : raw4038step0Labels = raw4038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4038 raw4038Labels permutation434 hz
    mixedMoment B raw4038step0 raw4038step0Labels = mixedMoment B raw4038step1 raw4038step1Labels := by
      have hz : ∀ j, raw4038step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4038step1 = (fun i j => raw4038step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4038step1 raw4038step0; decide +kernel
      have hl : raw4038step1Labels = raw4038step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4038step0 raw4038step0Labels permutation56 hz
    mixedMoment B raw4038step1 raw4038step1Labels = mixedMoment B raw4038step2 raw4038step2Labels := by
      have ha : raw4038step2 = (fun i j => raw4038step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4038step2 raw4038step1; decide +kernel
      have hl : raw4038step2Labels = raw4038step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4038step1 raw4038step1Labels permutation8 permutation6
    mixedMoment B raw4038step2 raw4038step2Labels = mixedMoment B raw4038step3 raw4038step3Labels := by
      have ha : raw4038step3 = raw4038step2 := by apply Matrix.ext; unfold raw4038step3 raw4038step2; decide +kernel
      have hl : raw4038step2Labels = labelEmbedding9 ∘ raw4038step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4038step2 raw4038step2Labels raw4038step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5268 node5268Labels := by rfl

def raw4039 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4039step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4039step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4039step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4039step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4039step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4039step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4039step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4039 raw4039Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw4039 raw4039Labels = mixedMoment B raw4039step0 raw4039step0Labels := by
      have hz : ∀ j, raw4039 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4039step0 = (fun i j => raw4039 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4039step0 raw4039; decide +kernel
      have hl : raw4039step0Labels = raw4039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4039 raw4039Labels permutation346 hz
    mixedMoment B raw4039step0 raw4039step0Labels = mixedMoment B raw4039step1 raw4039step1Labels := by
      have hz : ∀ j, raw4039step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4039step1 = (fun i j => raw4039step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4039step1 raw4039step0; decide +kernel
      have hl : raw4039step1Labels = raw4039step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4039step0 raw4039step0Labels permutation56 hz
    mixedMoment B raw4039step1 raw4039step1Labels = mixedMoment B raw4039step2 raw4039step2Labels := by
      have ha : raw4039step2 = (fun i j => raw4039step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4039step2 raw4039step1; decide +kernel
      have hl : raw4039step2Labels = raw4039step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4039step1 raw4039step1Labels permutation8 permutation6
    mixedMoment B raw4039step2 raw4039step2Labels = mixedMoment B raw4039step3 raw4039step3Labels := by
      have ha : raw4039step3 = raw4039step2 := by apply Matrix.ext; unfold raw4039step3 raw4039step2; decide +kernel
      have hl : raw4039step2Labels = labelEmbedding9 ∘ raw4039step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4039step2 raw4039step2Labels raw4039step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5268 node5268Labels := by rfl

def raw4040 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4040step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4040step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4040step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4040step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw4040step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4040step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4040step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4040step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4040step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4040 raw4040Labels = mixedMoment B node5296 node5296Labels := by
  calc
    mixedMoment B raw4040 raw4040Labels = mixedMoment B raw4040step0 raw4040step0Labels := by
      have hz : ∀ j, raw4040 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4040step0 = (fun i j => raw4040 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4040step0 raw4040; decide +kernel
      have hl : raw4040step0Labels = raw4040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4040 raw4040Labels permutation434 hz
    mixedMoment B raw4040step0 raw4040step0Labels = mixedMoment B raw4040step1 raw4040step1Labels := by
      have hz : ∀ j, raw4040step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4040step1 = (fun i j => raw4040step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4040step1 raw4040step0; decide +kernel
      have hl : raw4040step1Labels = raw4040step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4040step0 raw4040step0Labels permutation80 hz
    mixedMoment B raw4040step1 raw4040step1Labels = mixedMoment B raw4040step2 raw4040step2Labels := by
      have hz : ∀ j, raw4040step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4040step2 = (fun i j => raw4040step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4040step2 raw4040step1; decide +kernel
      have hl : raw4040step2Labels = raw4040step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4040step1 raw4040step1Labels permutation14 hz
    mixedMoment B raw4040step2 raw4040step2Labels = mixedMoment B raw4040step3 raw4040step3Labels := by
      have ha : raw4040step3 = (fun i j => raw4040step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4040step3 raw4040step2; decide +kernel
      have hl : raw4040step3Labels = raw4040step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4040step2 raw4040step2Labels permutation2 permutation6
    mixedMoment B raw4040step3 raw4040step3Labels = mixedMoment B raw4040step4 raw4040step4Labels := by
      have ha : raw4040step4 = raw4040step3 := by apply Matrix.ext; unfold raw4040step4 raw4040step3; decide +kernel
      have hl : raw4040step3Labels = labelEmbedding9 ∘ raw4040step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4040step3 raw4040step3Labels raw4040step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5296 node5296Labels := by rfl

def raw4041 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4041step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw4041step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4041step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4041step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4041step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4041step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4041 raw4041Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw4041 raw4041Labels = mixedMoment B raw4041step0 raw4041step0Labels := by
      have hz : ∀ j, raw4041 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4041step0 = (fun i j => raw4041 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4041step0 raw4041; decide +kernel
      have hl : raw4041step0Labels = raw4041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4041 raw4041Labels permutation434 hz
    mixedMoment B raw4041step0 raw4041step0Labels = mixedMoment B raw4041step1 raw4041step1Labels := by
      have ha : raw4041step1 = (fun i j => raw4041step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4041step1 raw4041step0; decide +kernel
      have hl : raw4041step1Labels = raw4041step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4041step0 raw4041step0Labels permutation33 permutation4
    mixedMoment B raw4041step1 raw4041step1Labels = mixedMoment B raw4041step2 raw4041step2Labels := by
      have ha : raw4041step2 = -raw4041step1 := by apply Matrix.ext; change ∀ i j, raw4041step2 i j = -(raw4041step1 i j); unfold raw4041step2 raw4041step1; decide +kernel
      have hl : raw4041step2Labels = raw4041step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4041step2 raw4041step2Labels = mixedMoment B raw4041step3 raw4041step3Labels := by
      have ha : raw4041step3 = raw4041step2 := by apply Matrix.ext; unfold raw4041step3 raw4041step2; decide +kernel
      have hl : raw4041step2Labels = labelEmbedding7 ∘ raw4041step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4041step2 raw4041step2Labels raw4041step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4836 node4836Labels := by rfl

def raw4042 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4042step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4042step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4042step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4042step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4042 raw4042Labels = mixedMoment B node5225 node5225Labels := by
  calc
    mixedMoment B raw4042 raw4042Labels = mixedMoment B raw4042step0 raw4042step0Labels := by
      have hz : ∀ j, raw4042 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4042step0 = (fun i j => raw4042 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4042step0 raw4042; decide +kernel
      have hl : raw4042step0Labels = raw4042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4042 raw4042Labels permutation434 hz
    mixedMoment B raw4042step0 raw4042step0Labels = mixedMoment B raw4042step1 raw4042step1Labels := by
      have ha : raw4042step1 = (fun i j => raw4042step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4042step1 raw4042step0; decide +kernel
      have hl : raw4042step1Labels = raw4042step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4042step0 raw4042step0Labels permutation32 permutation6
    mixedMoment B raw4042step1 raw4042step1Labels = mixedMoment B raw4042step2 raw4042step2Labels := by
      have ha : raw4042step2 = raw4042step1 := by apply Matrix.ext; unfold raw4042step2 raw4042step1; decide +kernel
      have hl : raw4042step1Labels = labelEmbedding9 ∘ raw4042step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4042step1 raw4042step1Labels raw4042step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5225 node5225Labels := by rfl

def raw4043 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4043step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4043step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4043step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4043 raw4043Labels = mixedMoment B node5240 node5240Labels := by
  calc
    mixedMoment B raw4043 raw4043Labels = mixedMoment B raw4043step0 raw4043step0Labels := by
      have ha : raw4043step0 = (fun i j => raw4043 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4043step0 raw4043; decide +kernel
      have hl : raw4043step0Labels = raw4043Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4043 raw4043Labels permutation158 permutation6
    mixedMoment B raw4043step0 raw4043step0Labels = mixedMoment B raw4043step1 raw4043step1Labels := by
      have ha : raw4043step1 = raw4043step0 := by apply Matrix.ext; unfold raw4043step1 raw4043step0; decide +kernel
      have hl : raw4043step0Labels = labelEmbedding9 ∘ raw4043step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4043step0 raw4043step0Labels raw4043step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5240 node5240Labels := by rfl

def raw4044 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4044step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4044step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4044step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4044step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4044 raw4044Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw4044 raw4044Labels = mixedMoment B raw4044step0 raw4044step0Labels := by
      have hz : ∀ j, raw4044 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4044step0 = (fun i j => raw4044 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4044step0 raw4044; decide +kernel
      have hl : raw4044step0Labels = raw4044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4044 raw4044Labels permutation434 hz
    mixedMoment B raw4044step0 raw4044step0Labels = mixedMoment B raw4044step1 raw4044step1Labels := by
      have ha : raw4044step1 = (fun i j => raw4044step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4044step1 raw4044step0; decide +kernel
      have hl : raw4044step1Labels = raw4044step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4044step0 raw4044step0Labels permutation32 permutation6
    mixedMoment B raw4044step1 raw4044step1Labels = mixedMoment B raw4044step2 raw4044step2Labels := by
      have ha : raw4044step2 = raw4044step1 := by apply Matrix.ext; unfold raw4044step2 raw4044step1; decide +kernel
      have hl : raw4044step1Labels = labelEmbedding9 ∘ raw4044step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4044step1 raw4044step1Labels raw4044step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5252 node5252Labels := by rfl

def raw4045 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4045step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4045step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4045 raw4045Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw4045 raw4045Labels = mixedMoment B raw4045step0 raw4045step0Labels := by
      have hz : ∀ j, raw4045 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4045step0 = (fun i j => raw4045 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4045step0 raw4045; decide +kernel
      have hl : raw4045step0Labels = raw4045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4045 raw4045Labels permutation434 hz
    mixedMoment B raw4045step0 raw4045step0Labels = mixedMoment B raw4045step1 raw4045step1Labels := by
      have ha : raw4045step1 = (fun i j => raw4045step0 (permutation136 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4045step1 raw4045step0; decide +kernel
      have hl : raw4045step1Labels = raw4045step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4045step0 raw4045step0Labels permutation136 permutation2
    _ = mixedMoment B node4836 node4836Labels := by rfl

def raw4046 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4046step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4046step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4046step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4046step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4046step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4046 raw4046Labels = mixedMoment B node5225 node5225Labels := by
  calc
    mixedMoment B raw4046 raw4046Labels = mixedMoment B raw4046step0 raw4046step0Labels := by
      have hz : ∀ j, raw4046 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4046step0 = (fun i j => raw4046 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4046step0 raw4046; decide +kernel
      have hl : raw4046step0Labels = raw4046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4046 raw4046Labels permutation346 hz
    mixedMoment B raw4046step0 raw4046step0Labels = mixedMoment B raw4046step1 raw4046step1Labels := by
      have ha : raw4046step1 = (fun i j => raw4046step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4046step1 raw4046step0; decide +kernel
      have hl : raw4046step1Labels = raw4046step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4046step0 raw4046step0Labels permutation32 permutation6
    mixedMoment B raw4046step1 raw4046step1Labels = mixedMoment B raw4046step2 raw4046step2Labels := by
      have ha : raw4046step2 = raw4046step1 := by apply Matrix.ext; unfold raw4046step2 raw4046step1; decide +kernel
      have hl : raw4046step1Labels = labelEmbedding9 ∘ raw4046step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4046step1 raw4046step1Labels raw4046step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5225 node5225Labels := by rfl

def raw4047 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4047step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4047step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4047step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4047 raw4047Labels = mixedMoment B node5240 node5240Labels := by
  calc
    mixedMoment B raw4047 raw4047Labels = mixedMoment B raw4047step0 raw4047step0Labels := by
      have ha : raw4047step0 = (fun i j => raw4047 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4047step0 raw4047; decide +kernel
      have hl : raw4047step0Labels = raw4047Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4047 raw4047Labels permutation152 permutation6
    mixedMoment B raw4047step0 raw4047step0Labels = mixedMoment B raw4047step1 raw4047step1Labels := by
      have ha : raw4047step1 = raw4047step0 := by apply Matrix.ext; unfold raw4047step1 raw4047step0; decide +kernel
      have hl : raw4047step0Labels = labelEmbedding9 ∘ raw4047step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4047step0 raw4047step0Labels raw4047step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5240 node5240Labels := by rfl

def raw4048 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4048step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4048step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4048step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4048step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4048 raw4048Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw4048 raw4048Labels = mixedMoment B raw4048step0 raw4048step0Labels := by
      have hz : ∀ j, raw4048 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4048step0 = (fun i j => raw4048 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4048step0 raw4048; decide +kernel
      have hl : raw4048step0Labels = raw4048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4048 raw4048Labels permutation346 hz
    mixedMoment B raw4048step0 raw4048step0Labels = mixedMoment B raw4048step1 raw4048step1Labels := by
      have ha : raw4048step1 = (fun i j => raw4048step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4048step1 raw4048step0; decide +kernel
      have hl : raw4048step1Labels = raw4048step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4048step0 raw4048step0Labels permutation32 permutation6
    mixedMoment B raw4048step1 raw4048step1Labels = mixedMoment B raw4048step2 raw4048step2Labels := by
      have ha : raw4048step2 = raw4048step1 := by apply Matrix.ext; unfold raw4048step2 raw4048step1; decide +kernel
      have hl : raw4048step1Labels = labelEmbedding9 ∘ raw4048step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4048step1 raw4048step1Labels raw4048step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5252 node5252Labels := by rfl

def raw4049 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4049step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4049step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4049step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4049step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -2, 3], ![-3, 3, 0]]
def raw4049step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4049step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw4049step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4049step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw4049step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4049 raw4049Labels = mixedMoment B node4844 node4844Labels := by
  calc
    mixedMoment B raw4049 raw4049Labels = mixedMoment B raw4049step0 raw4049step0Labels := by
      have hz : ∀ j, raw4049 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4049step0 = (fun i j => raw4049 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4049step0 raw4049; decide +kernel
      have hl : raw4049step0Labels = raw4049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4049 raw4049Labels permutation434 hz
    mixedMoment B raw4049step0 raw4049step0Labels = mixedMoment B raw4049step1 raw4049step1Labels := by
      have hz : ∀ j, raw4049step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4049step1 = (fun i j => raw4049step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4049step1 raw4049step0; decide +kernel
      have hl : raw4049step1Labels = raw4049step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4049step0 raw4049step0Labels permutation80 hz
    mixedMoment B raw4049step1 raw4049step1Labels = mixedMoment B raw4049step2 raw4049step2Labels := by
      have ha : raw4049step2 = (fun i j => raw4049step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4049step2 raw4049step1; decide +kernel
      have hl : raw4049step2Labels = raw4049step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4049step1 raw4049step1Labels permutation9 permutation4
    mixedMoment B raw4049step2 raw4049step2Labels = mixedMoment B raw4049step3 raw4049step3Labels := by
      have ha : raw4049step3 = -raw4049step2 := by apply Matrix.ext; change ∀ i j, raw4049step3 i j = -(raw4049step2 i j); unfold raw4049step3 raw4049step2; decide +kernel
      have hl : raw4049step3Labels = raw4049step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4049step3 raw4049step3Labels = mixedMoment B raw4049step4 raw4049step4Labels := by
      have ha : raw4049step4 = raw4049step3 := by apply Matrix.ext; unfold raw4049step4 raw4049step3; decide +kernel
      have hl : raw4049step3Labels = labelEmbedding7 ∘ raw4049step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4049step3 raw4049step3Labels raw4049step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4844 node4844Labels := by rfl

def raw4050 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4050step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4050step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4050step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4050step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-2, 3, -1], ![-2, 0, 2]]
def raw4050step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4050step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -3, 1], ![2, 0, -2]]
def raw4050step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4050step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -3, 1], ![2, 0, -2]]
def raw4050step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4050 raw4050Labels = mixedMoment B node4883 node4883Labels := by
  calc
    mixedMoment B raw4050 raw4050Labels = mixedMoment B raw4050step0 raw4050step0Labels := by
      have hz : ∀ j, raw4050 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4050step0 = (fun i j => raw4050 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4050step0 raw4050; decide +kernel
      have hl : raw4050step0Labels = raw4050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4050 raw4050Labels permutation434 hz
    mixedMoment B raw4050step0 raw4050step0Labels = mixedMoment B raw4050step1 raw4050step1Labels := by
      have hz : ∀ j, raw4050step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4050step1 = (fun i j => raw4050step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4050step1 raw4050step0; decide +kernel
      have hl : raw4050step1Labels = raw4050step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4050step0 raw4050step0Labels permutation80 hz
    mixedMoment B raw4050step1 raw4050step1Labels = mixedMoment B raw4050step2 raw4050step2Labels := by
      have ha : raw4050step2 = (fun i j => raw4050step1 (permutation21 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4050step2 raw4050step1; decide +kernel
      have hl : raw4050step2Labels = raw4050step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4050step1 raw4050step1Labels permutation21 permutation3
    mixedMoment B raw4050step2 raw4050step2Labels = mixedMoment B raw4050step3 raw4050step3Labels := by
      have ha : raw4050step3 = -raw4050step2 := by apply Matrix.ext; change ∀ i j, raw4050step3 i j = -(raw4050step2 i j); unfold raw4050step3 raw4050step2; decide +kernel
      have hl : raw4050step3Labels = raw4050step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4050step3 raw4050step3Labels = mixedMoment B raw4050step4 raw4050step4Labels := by
      have ha : raw4050step4 = raw4050step3 := by apply Matrix.ext; unfold raw4050step4 raw4050step3; decide +kernel
      have hl : raw4050step3Labels = labelEmbedding6 ∘ raw4050step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4050step3 raw4050step3Labels raw4050step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4883 node4883Labels := by rfl

def raw4051 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4051step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw4051step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4051step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw4051step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4051step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw4051step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4051 raw4051Labels = mixedMoment B node4882 node4882Labels := by
  calc
    mixedMoment B raw4051 raw4051Labels = mixedMoment B raw4051step0 raw4051step0Labels := by
      have hz : ∀ j, raw4051 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4051step0 = (fun i j => raw4051 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4051step0 raw4051; decide +kernel
      have hl : raw4051step0Labels = raw4051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4051 raw4051Labels permutation434 hz
    mixedMoment B raw4051step0 raw4051step0Labels = mixedMoment B raw4051step1 raw4051step1Labels := by
      have ha : raw4051step1 = (fun i j => raw4051step0 (permutation104 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4051step1 raw4051step0; decide +kernel
      have hl : raw4051step1Labels = raw4051step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4051step0 raw4051step0Labels permutation104 permutation3
    mixedMoment B raw4051step1 raw4051step1Labels = mixedMoment B raw4051step2 raw4051step2Labels := by
      have ha : raw4051step2 = -raw4051step1 := by apply Matrix.ext; change ∀ i j, raw4051step2 i j = -(raw4051step1 i j); unfold raw4051step2 raw4051step1; decide +kernel
      have hl : raw4051step2Labels = raw4051step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4051step2 raw4051step2Labels = mixedMoment B raw4051step3 raw4051step3Labels := by
      have ha : raw4051step3 = raw4051step2 := by apply Matrix.ext; unfold raw4051step3 raw4051step2; decide +kernel
      have hl : raw4051step2Labels = labelEmbedding6 ∘ raw4051step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4051step2 raw4051step2Labels raw4051step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4882 node4882Labels := by rfl

def raw4052 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4052step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw4052step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw4052step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw4052step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw4052step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4052 raw4052Labels = mixedMoment B node4882 node4882Labels := by
  calc
    mixedMoment B raw4052 raw4052Labels = mixedMoment B raw4052step0 raw4052step0Labels := by
      have hz : ∀ j, raw4052 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4052step0 = (fun i j => raw4052 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4052step0 raw4052; decide +kernel
      have hl : raw4052step0Labels = raw4052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4052 raw4052Labels permutation346 hz
    mixedMoment B raw4052step0 raw4052step0Labels = mixedMoment B raw4052step1 raw4052step1Labels := by
      have ha : raw4052step1 = (fun i j => raw4052step0 (permutation104 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4052step1 raw4052step0; decide +kernel
      have hl : raw4052step1Labels = raw4052step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4052step0 raw4052step0Labels permutation104 permutation3
    mixedMoment B raw4052step1 raw4052step1Labels = mixedMoment B raw4052step2 raw4052step2Labels := by
      have ha : raw4052step2 = -raw4052step1 := by apply Matrix.ext; change ∀ i j, raw4052step2 i j = -(raw4052step1 i j); unfold raw4052step2 raw4052step1; decide +kernel
      have hl : raw4052step2Labels = raw4052step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4052step2 raw4052step2Labels = mixedMoment B raw4052step3 raw4052step3Labels := by
      have ha : raw4052step3 = raw4052step2 := by apply Matrix.ext; unfold raw4052step3 raw4052step2; decide +kernel
      have hl : raw4052step2Labels = labelEmbedding6 ∘ raw4052step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4052step2 raw4052step2Labels raw4052step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4882 node4882Labels := by rfl

def raw4053 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4053step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4053step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4053step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw4053step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4053 raw4053Labels = mixedMoment B node4844 node4844Labels := by
  calc
    mixedMoment B raw4053 raw4053Labels = mixedMoment B raw4053step0 raw4053step0Labels := by
      have hz : ∀ j, raw4053 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4053step0 = (fun i j => raw4053 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4053step0 raw4053; decide +kernel
      have hl : raw4053step0Labels = raw4053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4053 raw4053Labels permutation434 hz
    mixedMoment B raw4053step0 raw4053step0Labels = mixedMoment B raw4053step1 raw4053step1Labels := by
      have hz : ∀ j, raw4053step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4053step1 = (fun i j => raw4053step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4053step1 raw4053step0; decide +kernel
      have hl : raw4053step1Labels = raw4053step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4053step0 raw4053step0Labels permutation80 hz
    mixedMoment B raw4053step1 raw4053step1Labels = mixedMoment B raw4053step2 raw4053step2Labels := by
      have ha : raw4053step2 = (fun i j => raw4053step1 (permutation28 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4053step2 raw4053step1; decide +kernel
      have hl : raw4053step2Labels = raw4053step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4053step1 raw4053step1Labels permutation28 permutation2
    _ = mixedMoment B node4844 node4844Labels := by rfl

def raw4054 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4054step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4054step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4054step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4054step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw4054step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4054step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4054step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4054step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4054step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4054 raw4054Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw4054 raw4054Labels = mixedMoment B raw4054step0 raw4054step0Labels := by
      have hz : ∀ j, raw4054 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4054step0 = (fun i j => raw4054 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4054step0 raw4054; decide +kernel
      have hl : raw4054step0Labels = raw4054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4054 raw4054Labels permutation434 hz
    mixedMoment B raw4054step0 raw4054step0Labels = mixedMoment B raw4054step1 raw4054step1Labels := by
      have hz : ∀ j, raw4054step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4054step1 = (fun i j => raw4054step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4054step1 raw4054step0; decide +kernel
      have hl : raw4054step1Labels = raw4054step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4054step0 raw4054step0Labels permutation80 hz
    mixedMoment B raw4054step1 raw4054step1Labels = mixedMoment B raw4054step2 raw4054step2Labels := by
      have ha : raw4054step2 = (fun i j => raw4054step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4054step2 raw4054step1; decide +kernel
      have hl : raw4054step2Labels = raw4054step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4054step1 raw4054step1Labels permutation8 permutation4
    mixedMoment B raw4054step2 raw4054step2Labels = mixedMoment B raw4054step3 raw4054step3Labels := by
      have ha : raw4054step3 = -raw4054step2 := by apply Matrix.ext; change ∀ i j, raw4054step3 i j = -(raw4054step2 i j); unfold raw4054step3 raw4054step2; decide +kernel
      have hl : raw4054step3Labels = raw4054step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4054step3 raw4054step3Labels = mixedMoment B raw4054step4 raw4054step4Labels := by
      have ha : raw4054step4 = raw4054step3 := by apply Matrix.ext; unfold raw4054step4 raw4054step3; decide +kernel
      have hl : raw4054step3Labels = labelEmbedding7 ∘ raw4054step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4054step3 raw4054step3Labels raw4054step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4845 node4845Labels := by rfl

def raw4055 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4055Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4055step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4055step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4055step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4055step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw4055step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4055step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw4055step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4055 raw4055Labels = mixedMoment B node5235 node5235Labels := by
  calc
    mixedMoment B raw4055 raw4055Labels = mixedMoment B raw4055step0 raw4055step0Labels := by
      have hz : ∀ j, raw4055 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4055step0 = (fun i j => raw4055 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4055step0 raw4055; decide +kernel
      have hl : raw4055step0Labels = raw4055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4055 raw4055Labels permutation434 hz
    mixedMoment B raw4055step0 raw4055step0Labels = mixedMoment B raw4055step1 raw4055step1Labels := by
      have hz : ∀ j, raw4055step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4055step1 = (fun i j => raw4055step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4055step1 raw4055step0; decide +kernel
      have hl : raw4055step1Labels = raw4055step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4055step0 raw4055step0Labels permutation80 hz
    mixedMoment B raw4055step1 raw4055step1Labels = mixedMoment B raw4055step2 raw4055step2Labels := by
      have ha : raw4055step2 = (fun i j => raw4055step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4055step2 raw4055step1; decide +kernel
      have hl : raw4055step2Labels = raw4055step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4055step1 raw4055step1Labels permutation8 permutation6
    mixedMoment B raw4055step2 raw4055step2Labels = mixedMoment B raw4055step3 raw4055step3Labels := by
      have ha : raw4055step3 = raw4055step2 := by apply Matrix.ext; unfold raw4055step3 raw4055step2; decide +kernel
      have hl : raw4055step2Labels = labelEmbedding9 ∘ raw4055step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4055step2 raw4055step2Labels raw4055step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5235 node5235Labels := by rfl

def raw4056 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4056Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4056step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw4056step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4056step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4056step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4056step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4056step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4056 raw4056Labels = mixedMoment B node5222 node5222Labels := by
  calc
    mixedMoment B raw4056 raw4056Labels = mixedMoment B raw4056step0 raw4056step0Labels := by
      have hz : ∀ j, raw4056 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4056step0 = (fun i j => raw4056 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4056step0 raw4056; decide +kernel
      have hl : raw4056step0Labels = raw4056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4056 raw4056Labels permutation434 hz
    mixedMoment B raw4056step0 raw4056step0Labels = mixedMoment B raw4056step1 raw4056step1Labels := by
      have ha : raw4056step1 = (fun i j => raw4056step0 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4056step1 raw4056step0; decide +kernel
      have hl : raw4056step1Labels = raw4056step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4056step0 raw4056step0Labels permutation149 permutation6
    mixedMoment B raw4056step1 raw4056step1Labels = mixedMoment B raw4056step2 raw4056step2Labels := by
      have ha : raw4056step2 = -raw4056step1 := by apply Matrix.ext; change ∀ i j, raw4056step2 i j = -(raw4056step1 i j); unfold raw4056step2 raw4056step1; decide +kernel
      have hl : raw4056step2Labels = raw4056step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4056step2 raw4056step2Labels = mixedMoment B raw4056step3 raw4056step3Labels := by
      have ha : raw4056step3 = raw4056step2 := by apply Matrix.ext; unfold raw4056step3 raw4056step2; decide +kernel
      have hl : raw4056step2Labels = labelEmbedding9 ∘ raw4056step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4056step2 raw4056step2Labels raw4056step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5222 node5222Labels := by rfl

def raw4057 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4057Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4057step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw4057step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4057step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4057step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4057step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4057step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4057 raw4057Labels = mixedMoment B node5222 node5222Labels := by
  calc
    mixedMoment B raw4057 raw4057Labels = mixedMoment B raw4057step0 raw4057step0Labels := by
      have hz : ∀ j, raw4057 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4057step0 = (fun i j => raw4057 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4057step0 raw4057; decide +kernel
      have hl : raw4057step0Labels = raw4057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4057 raw4057Labels permutation346 hz
    mixedMoment B raw4057step0 raw4057step0Labels = mixedMoment B raw4057step1 raw4057step1Labels := by
      have ha : raw4057step1 = (fun i j => raw4057step0 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4057step1 raw4057step0; decide +kernel
      have hl : raw4057step1Labels = raw4057step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4057step0 raw4057step0Labels permutation149 permutation6
    mixedMoment B raw4057step1 raw4057step1Labels = mixedMoment B raw4057step2 raw4057step2Labels := by
      have ha : raw4057step2 = -raw4057step1 := by apply Matrix.ext; change ∀ i j, raw4057step2 i j = -(raw4057step1 i j); unfold raw4057step2 raw4057step1; decide +kernel
      have hl : raw4057step2Labels = raw4057step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw4057step2 raw4057step2Labels = mixedMoment B raw4057step3 raw4057step3Labels := by
      have ha : raw4057step3 = raw4057step2 := by apply Matrix.ext; unfold raw4057step3 raw4057step2; decide +kernel
      have hl : raw4057step2Labels = labelEmbedding9 ∘ raw4057step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4057step2 raw4057step2Labels raw4057step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5222 node5222Labels := by rfl

def raw4058 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4058Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4058step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4058step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4058step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4058step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4058step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw4058step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4058step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4058 raw4058Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw4058 raw4058Labels = mixedMoment B raw4058step0 raw4058step0Labels := by
      have hz : ∀ j, raw4058 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4058step0 = (fun i j => raw4058 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4058step0 raw4058; decide +kernel
      have hl : raw4058step0Labels = raw4058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4058 raw4058Labels permutation434 hz
    mixedMoment B raw4058step0 raw4058step0Labels = mixedMoment B raw4058step1 raw4058step1Labels := by
      have hz : ∀ j, raw4058step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4058step1 = (fun i j => raw4058step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4058step1 raw4058step0; decide +kernel
      have hl : raw4058step1Labels = raw4058step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4058step0 raw4058step0Labels permutation80 hz
    mixedMoment B raw4058step1 raw4058step1Labels = mixedMoment B raw4058step2 raw4058step2Labels := by
      have ha : raw4058step2 = (fun i j => raw4058step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4058step2 raw4058step1; decide +kernel
      have hl : raw4058step2Labels = raw4058step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4058step1 raw4058step1Labels permutation8 permutation6
    mixedMoment B raw4058step2 raw4058step2Labels = mixedMoment B raw4058step3 raw4058step3Labels := by
      have ha : raw4058step3 = raw4058step2 := by apply Matrix.ext; unfold raw4058step3 raw4058step2; decide +kernel
      have hl : raw4058step2Labels = labelEmbedding9 ∘ raw4058step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4058step2 raw4058step2Labels raw4058step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw4059 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4059Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4059step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4059step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4059step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4059step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw4059step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4059 raw4059Labels = mixedMoment B node3046 node3046Labels := by
  calc
    mixedMoment B raw4059 raw4059Labels = mixedMoment B raw4059step0 raw4059step0Labels := by
      have hz : ∀ j, raw4059 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4059step0 = (fun i j => raw4059 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4059step0 raw4059; decide +kernel
      have hl : raw4059step0Labels = raw4059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4059 raw4059Labels permutation434 hz
    mixedMoment B raw4059step0 raw4059step0Labels = mixedMoment B raw4059step1 raw4059step1Labels := by
      have hz : ∀ j, raw4059step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4059step1 = (fun i j => raw4059step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4059step1 raw4059step0; decide +kernel
      have hl : raw4059step1Labels = raw4059step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4059step0 raw4059step0Labels permutation80 hz
    mixedMoment B raw4059step1 raw4059step1Labels = mixedMoment B raw4059step2 raw4059step2Labels := by
      have ha : raw4059step2 = (fun i j => raw4059step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4059step2 raw4059step1; decide +kernel
      have hl : raw4059step2Labels = raw4059step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4059step1 raw4059step1Labels permutation8 permutation6
    _ = mixedMoment B node3046 node3046Labels := by rfl

def raw4060 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4060Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4060step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4060step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4060step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4060step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4060 raw4060Labels = mixedMoment B node3031 node3031Labels := by
  calc
    mixedMoment B raw4060 raw4060Labels = mixedMoment B raw4060step0 raw4060step0Labels := by
      have hz : ∀ j, raw4060 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4060step0 = (fun i j => raw4060 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4060step0 raw4060; decide +kernel
      have hl : raw4060step0Labels = raw4060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4060 raw4060Labels permutation434 hz
    mixedMoment B raw4060step0 raw4060step0Labels = mixedMoment B raw4060step1 raw4060step1Labels := by
      have ha : raw4060step1 = (fun i j => raw4060step0 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4060step1 raw4060step0; decide +kernel
      have hl : raw4060step1Labels = raw4060step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4060step0 raw4060step0Labels permutation149 permutation6
    mixedMoment B raw4060step1 raw4060step1Labels = mixedMoment B raw4060step2 raw4060step2Labels := by
      have ha : raw4060step2 = -raw4060step1 := by apply Matrix.ext; change ∀ i j, raw4060step2 i j = -(raw4060step1 i j); unfold raw4060step2 raw4060step1; decide +kernel
      have hl : raw4060step2Labels = raw4060step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3031 node3031Labels := by rfl

def raw4061 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4061Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4061step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4061step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4061step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4061step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4061 raw4061Labels = mixedMoment B node3031 node3031Labels := by
  calc
    mixedMoment B raw4061 raw4061Labels = mixedMoment B raw4061step0 raw4061step0Labels := by
      have hz : ∀ j, raw4061 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4061step0 = (fun i j => raw4061 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4061step0 raw4061; decide +kernel
      have hl : raw4061step0Labels = raw4061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4061 raw4061Labels permutation346 hz
    mixedMoment B raw4061step0 raw4061step0Labels = mixedMoment B raw4061step1 raw4061step1Labels := by
      have ha : raw4061step1 = (fun i j => raw4061step0 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4061step1 raw4061step0; decide +kernel
      have hl : raw4061step1Labels = raw4061step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4061step0 raw4061step0Labels permutation149 permutation6
    mixedMoment B raw4061step1 raw4061step1Labels = mixedMoment B raw4061step2 raw4061step2Labels := by
      have ha : raw4061step2 = -raw4061step1 := by apply Matrix.ext; change ∀ i j, raw4061step2 i j = -(raw4061step1 i j); unfold raw4061step2 raw4061step1; decide +kernel
      have hl : raw4061step2Labels = raw4061step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3031 node3031Labels := by rfl

def raw4062 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4062Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4062step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4062step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4062step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4062step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw4062step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4062 raw4062Labels = mixedMoment B node3090 node3090Labels := by
  calc
    mixedMoment B raw4062 raw4062Labels = mixedMoment B raw4062step0 raw4062step0Labels := by
      have hz : ∀ j, raw4062 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4062step0 = (fun i j => raw4062 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4062step0 raw4062; decide +kernel
      have hl : raw4062step0Labels = raw4062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4062 raw4062Labels permutation434 hz
    mixedMoment B raw4062step0 raw4062step0Labels = mixedMoment B raw4062step1 raw4062step1Labels := by
      have hz : ∀ j, raw4062step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4062step1 = (fun i j => raw4062step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4062step1 raw4062step0; decide +kernel
      have hl : raw4062step1Labels = raw4062step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4062step0 raw4062step0Labels permutation80 hz
    mixedMoment B raw4062step1 raw4062step1Labels = mixedMoment B raw4062step2 raw4062step2Labels := by
      have ha : raw4062step2 = (fun i j => raw4062step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4062step2 raw4062step1; decide +kernel
      have hl : raw4062step2Labels = raw4062step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4062step1 raw4062step1Labels permutation8 permutation6
    _ = mixedMoment B node3090 node3090Labels := by rfl

def raw4063 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4063Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4063step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4063step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4063step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4063step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw4063step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4063 raw4063Labels = mixedMoment B node3095 node3095Labels := by
  calc
    mixedMoment B raw4063 raw4063Labels = mixedMoment B raw4063step0 raw4063step0Labels := by
      have hz : ∀ j, raw4063 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4063step0 = (fun i j => raw4063 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4063step0 raw4063; decide +kernel
      have hl : raw4063step0Labels = raw4063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4063 raw4063Labels permutation434 hz
    mixedMoment B raw4063step0 raw4063step0Labels = mixedMoment B raw4063step1 raw4063step1Labels := by
      have hz : ∀ j, raw4063step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4063step1 = (fun i j => raw4063step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4063step1 raw4063step0; decide +kernel
      have hl : raw4063step1Labels = raw4063step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4063step0 raw4063step0Labels permutation80 hz
    mixedMoment B raw4063step1 raw4063step1Labels = mixedMoment B raw4063step2 raw4063step2Labels := by
      have ha : raw4063step2 = (fun i j => raw4063step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4063step2 raw4063step1; decide +kernel
      have hl : raw4063step2Labels = raw4063step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4063step1 raw4063step1Labels permutation8 permutation6
    _ = mixedMoment B node3095 node3095Labels := by rfl

def raw4064 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4064Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4064step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4064step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4064step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4064step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4064step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4064 raw4064Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw4064 raw4064Labels = mixedMoment B raw4064step0 raw4064step0Labels := by
      have hz : ∀ j, raw4064 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4064step0 = (fun i j => raw4064 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4064step0 raw4064; decide +kernel
      have hl : raw4064step0Labels = raw4064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4064 raw4064Labels permutation434 hz
    mixedMoment B raw4064step0 raw4064step0Labels = mixedMoment B raw4064step1 raw4064step1Labels := by
      have hz : ∀ j, raw4064step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4064step1 = (fun i j => raw4064step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4064step1 raw4064step0; decide +kernel
      have hl : raw4064step1Labels = raw4064step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4064step0 raw4064step0Labels permutation56 hz
    mixedMoment B raw4064step1 raw4064step1Labels = mixedMoment B raw4064step2 raw4064step2Labels := by
      have ha : raw4064step2 = (fun i j => raw4064step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4064step2 raw4064step1; decide +kernel
      have hl : raw4064step2Labels = raw4064step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4064step1 raw4064step1Labels permutation8 permutation6
    _ = mixedMoment B node2734 node2734Labels := by rfl

def raw4065 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4065Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4065step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4065step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4065step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4065step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4065step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4065 raw4065Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw4065 raw4065Labels = mixedMoment B raw4065step0 raw4065step0Labels := by
      have hz : ∀ j, raw4065 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4065step0 = (fun i j => raw4065 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4065step0 raw4065; decide +kernel
      have hl : raw4065step0Labels = raw4065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4065 raw4065Labels permutation346 hz
    mixedMoment B raw4065step0 raw4065step0Labels = mixedMoment B raw4065step1 raw4065step1Labels := by
      have hz : ∀ j, raw4065step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4065step1 = (fun i j => raw4065step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4065step1 raw4065step0; decide +kernel
      have hl : raw4065step1Labels = raw4065step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4065step0 raw4065step0Labels permutation56 hz
    mixedMoment B raw4065step1 raw4065step1Labels = mixedMoment B raw4065step2 raw4065step2Labels := by
      have ha : raw4065step2 = (fun i j => raw4065step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4065step2 raw4065step1; decide +kernel
      have hl : raw4065step2Labels = raw4065step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4065step1 raw4065step1Labels permutation8 permutation6
    _ = mixedMoment B node2734 node2734Labels := by rfl

def raw4066 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4066Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4066step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4066step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4066step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4066step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw4066step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4066step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4066step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4066 raw4066Labels = mixedMoment B node2770 node2770Labels := by
  calc
    mixedMoment B raw4066 raw4066Labels = mixedMoment B raw4066step0 raw4066step0Labels := by
      have hz : ∀ j, raw4066 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4066step0 = (fun i j => raw4066 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4066step0 raw4066; decide +kernel
      have hl : raw4066step0Labels = raw4066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4066 raw4066Labels permutation434 hz
    mixedMoment B raw4066step0 raw4066step0Labels = mixedMoment B raw4066step1 raw4066step1Labels := by
      have hz : ∀ j, raw4066step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4066step1 = (fun i j => raw4066step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4066step1 raw4066step0; decide +kernel
      have hl : raw4066step1Labels = raw4066step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4066step0 raw4066step0Labels permutation80 hz
    mixedMoment B raw4066step1 raw4066step1Labels = mixedMoment B raw4066step2 raw4066step2Labels := by
      have hz : ∀ j, raw4066step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4066step2 = (fun i j => raw4066step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4066step2 raw4066step1; decide +kernel
      have hl : raw4066step2Labels = raw4066step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4066step1 raw4066step1Labels permutation14 hz
    mixedMoment B raw4066step2 raw4066step2Labels = mixedMoment B raw4066step3 raw4066step3Labels := by
      have ha : raw4066step3 = (fun i j => raw4066step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4066step3 raw4066step2; decide +kernel
      have hl : raw4066step3Labels = raw4066step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4066step2 raw4066step2Labels permutation2 permutation6
    _ = mixedMoment B node2770 node2770Labels := by rfl

def raw4067 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4067Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4067step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4067step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4067step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4067 raw4067Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw4067 raw4067Labels = mixedMoment B raw4067step0 raw4067step0Labels := by
      have hz : ∀ j, raw4067 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4067step0 = (fun i j => raw4067 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4067step0 raw4067; decide +kernel
      have hl : raw4067step0Labels = raw4067Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4067 raw4067Labels permutation434 hz
    mixedMoment B raw4067step0 raw4067step0Labels = mixedMoment B raw4067step1 raw4067step1Labels := by
      have ha : raw4067step1 = (fun i j => raw4067step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4067step1 raw4067step0; decide +kernel
      have hl : raw4067step1Labels = raw4067step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4067step0 raw4067step0Labels permutation32 permutation6
    _ = mixedMoment B node2197 node2197Labels := by rfl

def raw4068 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4068Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4068step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4068step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4068step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4068 raw4068Labels = mixedMoment B node2667 node2667Labels := by
  calc
    mixedMoment B raw4068 raw4068Labels = mixedMoment B raw4068step0 raw4068step0Labels := by
      have hz : ∀ j, raw4068 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4068step0 = (fun i j => raw4068 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4068step0 raw4068; decide +kernel
      have hl : raw4068step0Labels = raw4068Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4068 raw4068Labels permutation434 hz
    mixedMoment B raw4068step0 raw4068step0Labels = mixedMoment B raw4068step1 raw4068step1Labels := by
      have ha : raw4068step1 = (fun i j => raw4068step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4068step1 raw4068step0; decide +kernel
      have hl : raw4068step1Labels = raw4068step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4068step0 raw4068step0Labels permutation32 permutation6
    _ = mixedMoment B node2667 node2667Labels := by rfl

def raw4069 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4069Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4069step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4069 raw4069Labels = mixedMoment B node2692 node2692Labels := by
  calc
    mixedMoment B raw4069 raw4069Labels = mixedMoment B raw4069step0 raw4069step0Labels := by
      have ha : raw4069step0 = (fun i j => raw4069 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4069step0 raw4069; decide +kernel
      have hl : raw4069step0Labels = raw4069Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4069 raw4069Labels permutation158 permutation6
    _ = mixedMoment B node2692 node2692Labels := by rfl

def raw4070 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4070Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4070step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4070step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4070 raw4070Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw4070 raw4070Labels = mixedMoment B raw4070step0 raw4070step0Labels := by
      have hz : ∀ j, raw4070 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4070step0 = (fun i j => raw4070 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4070step0 raw4070; decide +kernel
      have hl : raw4070step0Labels = raw4070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4070 raw4070Labels permutation434 hz
    mixedMoment B raw4070step0 raw4070step0Labels = mixedMoment B raw4070step1 raw4070step1Labels := by
      have ha : raw4070step1 = (fun i j => raw4070step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4070step1 raw4070step0; decide +kernel
      have hl : raw4070step1Labels = raw4070step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4070step0 raw4070step0Labels permutation32 permutation6
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw4071 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4071Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4071step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4071step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw4071step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4071 raw4071Labels = mixedMoment B node2716 node2716Labels := by
  calc
    mixedMoment B raw4071 raw4071Labels = mixedMoment B raw4071step0 raw4071step0Labels := by
      have hz : ∀ j, raw4071 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4071step0 = (fun i j => raw4071 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4071step0 raw4071; decide +kernel
      have hl : raw4071step0Labels = raw4071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4071 raw4071Labels permutation434 hz
    mixedMoment B raw4071step0 raw4071step0Labels = mixedMoment B raw4071step1 raw4071step1Labels := by
      have ha : raw4071step1 = (fun i j => raw4071step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4071step1 raw4071step0; decide +kernel
      have hl : raw4071step1Labels = raw4071step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4071step0 raw4071step0Labels permutation32 permutation6
    _ = mixedMoment B node2716 node2716Labels := by rfl

def raw4072 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4072Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4072step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4072step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4072step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4072 raw4072Labels = mixedMoment B node2667 node2667Labels := by
  calc
    mixedMoment B raw4072 raw4072Labels = mixedMoment B raw4072step0 raw4072step0Labels := by
      have hz : ∀ j, raw4072 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4072step0 = (fun i j => raw4072 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4072step0 raw4072; decide +kernel
      have hl : raw4072step0Labels = raw4072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4072 raw4072Labels permutation346 hz
    mixedMoment B raw4072step0 raw4072step0Labels = mixedMoment B raw4072step1 raw4072step1Labels := by
      have ha : raw4072step1 = (fun i j => raw4072step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4072step1 raw4072step0; decide +kernel
      have hl : raw4072step1Labels = raw4072step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4072step0 raw4072step0Labels permutation32 permutation6
    _ = mixedMoment B node2667 node2667Labels := by rfl

def raw4073 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4073Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw4073step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4073 raw4073Labels = mixedMoment B node2692 node2692Labels := by
  calc
    mixedMoment B raw4073 raw4073Labels = mixedMoment B raw4073step0 raw4073step0Labels := by
      have ha : raw4073step0 = (fun i j => raw4073 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4073step0 raw4073; decide +kernel
      have hl : raw4073step0Labels = raw4073Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4073 raw4073Labels permutation152 permutation6
    _ = mixedMoment B node2692 node2692Labels := by rfl

def raw4074 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4074Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4074step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4074step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4074 raw4074Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw4074 raw4074Labels = mixedMoment B raw4074step0 raw4074step0Labels := by
      have hz : ∀ j, raw4074 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4074step0 = (fun i j => raw4074 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4074step0 raw4074; decide +kernel
      have hl : raw4074step0Labels = raw4074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4074 raw4074Labels permutation346 hz
    mixedMoment B raw4074step0 raw4074step0Labels = mixedMoment B raw4074step1 raw4074step1Labels := by
      have ha : raw4074step1 = (fun i j => raw4074step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4074step1 raw4074step0; decide +kernel
      have hl : raw4074step1Labels = raw4074step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4074step0 raw4074step0Labels permutation32 permutation6
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw4075 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4075Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4075step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4075step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4075step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4075step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw4075step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4075 raw4075Labels = mixedMoment B node2222 node2222Labels := by
  calc
    mixedMoment B raw4075 raw4075Labels = mixedMoment B raw4075step0 raw4075step0Labels := by
      have hz : ∀ j, raw4075 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4075step0 = (fun i j => raw4075 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4075step0 raw4075; decide +kernel
      have hl : raw4075step0Labels = raw4075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4075 raw4075Labels permutation434 hz
    mixedMoment B raw4075step0 raw4075step0Labels = mixedMoment B raw4075step1 raw4075step1Labels := by
      have hz : ∀ j, raw4075step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4075step1 = (fun i j => raw4075step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4075step1 raw4075step0; decide +kernel
      have hl : raw4075step1Labels = raw4075step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4075step0 raw4075step0Labels permutation80 hz
    mixedMoment B raw4075step1 raw4075step1Labels = mixedMoment B raw4075step2 raw4075step2Labels := by
      have ha : raw4075step2 = (fun i j => raw4075step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4075step2 raw4075step1; decide +kernel
      have hl : raw4075step2Labels = raw4075step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4075step1 raw4075step1Labels permutation8 permutation6
    _ = mixedMoment B node2222 node2222Labels := by rfl

def raw4076 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4076Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4076step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4076step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4076step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4076step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-2, 3, -1], ![-2, 0, 2]]
def raw4076step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4076step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -3, 1], ![2, 0, -2]]
def raw4076step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4076 raw4076Labels = mixedMoment B node2137 node2137Labels := by
  calc
    mixedMoment B raw4076 raw4076Labels = mixedMoment B raw4076step0 raw4076step0Labels := by
      have hz : ∀ j, raw4076 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4076step0 = (fun i j => raw4076 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4076step0 raw4076; decide +kernel
      have hl : raw4076step0Labels = raw4076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4076 raw4076Labels permutation434 hz
    mixedMoment B raw4076step0 raw4076step0Labels = mixedMoment B raw4076step1 raw4076step1Labels := by
      have hz : ∀ j, raw4076step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4076step1 = (fun i j => raw4076step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4076step1 raw4076step0; decide +kernel
      have hl : raw4076step1Labels = raw4076step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4076step0 raw4076step0Labels permutation80 hz
    mixedMoment B raw4076step1 raw4076step1Labels = mixedMoment B raw4076step2 raw4076step2Labels := by
      have ha : raw4076step2 = (fun i j => raw4076step1 (permutation21 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4076step2 raw4076step1; decide +kernel
      have hl : raw4076step2Labels = raw4076step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4076step1 raw4076step1Labels permutation21 permutation3
    mixedMoment B raw4076step2 raw4076step2Labels = mixedMoment B raw4076step3 raw4076step3Labels := by
      have ha : raw4076step3 = -raw4076step2 := by apply Matrix.ext; change ∀ i j, raw4076step3 i j = -(raw4076step2 i j); unfold raw4076step3 raw4076step2; decide +kernel
      have hl : raw4076step3Labels = raw4076step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2137 node2137Labels := by rfl

def raw4077 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4077Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4077step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw4077step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4077step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw4077step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4077 raw4077Labels = mixedMoment B node2135 node2135Labels := by
  calc
    mixedMoment B raw4077 raw4077Labels = mixedMoment B raw4077step0 raw4077step0Labels := by
      have hz : ∀ j, raw4077 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4077step0 = (fun i j => raw4077 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4077step0 raw4077; decide +kernel
      have hl : raw4077step0Labels = raw4077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4077 raw4077Labels permutation434 hz
    mixedMoment B raw4077step0 raw4077step0Labels = mixedMoment B raw4077step1 raw4077step1Labels := by
      have ha : raw4077step1 = (fun i j => raw4077step0 (permutation104 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4077step1 raw4077step0; decide +kernel
      have hl : raw4077step1Labels = raw4077step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4077step0 raw4077step0Labels permutation104 permutation3
    mixedMoment B raw4077step1 raw4077step1Labels = mixedMoment B raw4077step2 raw4077step2Labels := by
      have ha : raw4077step2 = -raw4077step1 := by apply Matrix.ext; change ∀ i j, raw4077step2 i j = -(raw4077step1 i j); unfold raw4077step2 raw4077step1; decide +kernel
      have hl : raw4077step2Labels = raw4077step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2135 node2135Labels := by rfl

def raw4078 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4078Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4078step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw4078step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw4078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4078 raw4078Labels = mixedMoment B node2135 node2135Labels := by
  calc
    mixedMoment B raw4078 raw4078Labels = mixedMoment B raw4078step0 raw4078step0Labels := by
      have hz : ∀ j, raw4078 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4078step0 = (fun i j => raw4078 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4078step0 raw4078; decide +kernel
      have hl : raw4078step0Labels = raw4078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4078 raw4078Labels permutation346 hz
    mixedMoment B raw4078step0 raw4078step0Labels = mixedMoment B raw4078step1 raw4078step1Labels := by
      have ha : raw4078step1 = (fun i j => raw4078step0 (permutation104 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4078step1 raw4078step0; decide +kernel
      have hl : raw4078step1Labels = raw4078step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4078step0 raw4078step0Labels permutation104 permutation3
    mixedMoment B raw4078step1 raw4078step1Labels = mixedMoment B raw4078step2 raw4078step2Labels := by
      have ha : raw4078step2 = -raw4078step1 := by apply Matrix.ext; change ∀ i j, raw4078step2 i j = -(raw4078step1 i j); unfold raw4078step2 raw4078step1; decide +kernel
      have hl : raw4078step2Labels = raw4078step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2135 node2135Labels := by rfl

def raw4079 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4079Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4079step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4079step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-3, 0, 3]]
def raw4079step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4079step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw4079step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4079step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw4079step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4079 raw4079Labels = mixedMoment B node2136 node2136Labels := by
  calc
    mixedMoment B raw4079 raw4079Labels = mixedMoment B raw4079step0 raw4079step0Labels := by
      have hz : ∀ j, raw4079 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4079step0 = (fun i j => raw4079 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4079step0 raw4079; decide +kernel
      have hl : raw4079step0Labels = raw4079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4079 raw4079Labels permutation434 hz
    mixedMoment B raw4079step0 raw4079step0Labels = mixedMoment B raw4079step1 raw4079step1Labels := by
      have hz : ∀ j, raw4079step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4079step1 = (fun i j => raw4079step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4079step1 raw4079step0; decide +kernel
      have hl : raw4079step1Labels = raw4079step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4079step0 raw4079step0Labels permutation80 hz
    mixedMoment B raw4079step1 raw4079step1Labels = mixedMoment B raw4079step2 raw4079step2Labels := by
      have ha : raw4079step2 = (fun i j => raw4079step1 (permutation20 i) (permutation3 j)) := by apply Matrix.ext; unfold raw4079step2 raw4079step1; decide +kernel
      have hl : raw4079step2Labels = raw4079step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4079step1 raw4079step1Labels permutation20 permutation3
    mixedMoment B raw4079step2 raw4079step2Labels = mixedMoment B raw4079step3 raw4079step3Labels := by
      have ha : raw4079step3 = -raw4079step2 := by apply Matrix.ext; change ∀ i j, raw4079step3 i j = -(raw4079step2 i j); unfold raw4079step3 raw4079step2; decide +kernel
      have hl : raw4079step3Labels = raw4079step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2136 node2136Labels := by rfl

def raw4080 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4080Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4080step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4080step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4080step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4080step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw4080step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4080 raw4080Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw4080 raw4080Labels = mixedMoment B raw4080step0 raw4080step0Labels := by
      have hz : ∀ j, raw4080 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4080step0 = (fun i j => raw4080 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4080step0 raw4080; decide +kernel
      have hl : raw4080step0Labels = raw4080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4080 raw4080Labels permutation434 hz
    mixedMoment B raw4080step0 raw4080step0Labels = mixedMoment B raw4080step1 raw4080step1Labels := by
      have hz : ∀ j, raw4080step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4080step1 = (fun i j => raw4080step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4080step1 raw4080step0; decide +kernel
      have hl : raw4080step1Labels = raw4080step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4080step0 raw4080step0Labels permutation80 hz
    mixedMoment B raw4080step1 raw4080step1Labels = mixedMoment B raw4080step2 raw4080step2Labels := by
      have ha : raw4080step2 = (fun i j => raw4080step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4080step2 raw4080step1; decide +kernel
      have hl : raw4080step2Labels = raw4080step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4080step1 raw4080step1Labels permutation8 permutation6
    _ = mixedMoment B node2218 node2218Labels := by rfl

def raw4081 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4081Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4081step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4081step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4081step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4081step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw4081step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4081 raw4081Labels = mixedMoment B node2680 node2680Labels := by
  calc
    mixedMoment B raw4081 raw4081Labels = mixedMoment B raw4081step0 raw4081step0Labels := by
      have hz : ∀ j, raw4081 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4081step0 = (fun i j => raw4081 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4081step0 raw4081; decide +kernel
      have hl : raw4081step0Labels = raw4081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4081 raw4081Labels permutation434 hz
    mixedMoment B raw4081step0 raw4081step0Labels = mixedMoment B raw4081step1 raw4081step1Labels := by
      have hz : ∀ j, raw4081step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4081step1 = (fun i j => raw4081step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4081step1 raw4081step0; decide +kernel
      have hl : raw4081step1Labels = raw4081step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4081step0 raw4081step0Labels permutation80 hz
    mixedMoment B raw4081step1 raw4081step1Labels = mixedMoment B raw4081step2 raw4081step2Labels := by
      have ha : raw4081step2 = (fun i j => raw4081step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4081step2 raw4081step1; decide +kernel
      have hl : raw4081step2Labels = raw4081step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4081step1 raw4081step1Labels permutation8 permutation6
    _ = mixedMoment B node2680 node2680Labels := by rfl

def raw4082 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4082Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4082step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw4082step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4082step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4082 raw4082Labels = mixedMoment B node2664 node2664Labels := by
  calc
    mixedMoment B raw4082 raw4082Labels = mixedMoment B raw4082step0 raw4082step0Labels := by
      have hz : ∀ j, raw4082 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4082step0 = (fun i j => raw4082 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4082step0 raw4082; decide +kernel
      have hl : raw4082step0Labels = raw4082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4082 raw4082Labels permutation434 hz
    mixedMoment B raw4082step0 raw4082step0Labels = mixedMoment B raw4082step1 raw4082step1Labels := by
      have ha : raw4082step1 = (fun i j => raw4082step0 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4082step1 raw4082step0; decide +kernel
      have hl : raw4082step1Labels = raw4082step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4082step0 raw4082step0Labels permutation149 permutation6
    mixedMoment B raw4082step1 raw4082step1Labels = mixedMoment B raw4082step2 raw4082step2Labels := by
      have ha : raw4082step2 = -raw4082step1 := by apply Matrix.ext; change ∀ i j, raw4082step2 i j = -(raw4082step1 i j); unfold raw4082step2 raw4082step1; decide +kernel
      have hl : raw4082step2Labels = raw4082step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2664 node2664Labels := by rfl

def raw4083 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4083Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4083step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw4083step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4083step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw4083step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4083 raw4083Labels = mixedMoment B node2664 node2664Labels := by
  calc
    mixedMoment B raw4083 raw4083Labels = mixedMoment B raw4083step0 raw4083step0Labels := by
      have hz : ∀ j, raw4083 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4083step0 = (fun i j => raw4083 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4083step0 raw4083; decide +kernel
      have hl : raw4083step0Labels = raw4083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4083 raw4083Labels permutation346 hz
    mixedMoment B raw4083step0 raw4083step0Labels = mixedMoment B raw4083step1 raw4083step1Labels := by
      have ha : raw4083step1 = (fun i j => raw4083step0 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4083step1 raw4083step0; decide +kernel
      have hl : raw4083step1Labels = raw4083step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4083step0 raw4083step0Labels permutation149 permutation6
    mixedMoment B raw4083step1 raw4083step1Labels = mixedMoment B raw4083step2 raw4083step2Labels := by
      have ha : raw4083step2 = -raw4083step1 := by apply Matrix.ext; change ∀ i j, raw4083step2 i j = -(raw4083step1 i j); unfold raw4083step2 raw4083step1; decide +kernel
      have hl : raw4083step2Labels = raw4083step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2664 node2664Labels := by rfl

def raw4084 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4084Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4084step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4084step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw4084step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4084step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw4084step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4084 raw4084Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw4084 raw4084Labels = mixedMoment B raw4084step0 raw4084step0Labels := by
      have hz : ∀ j, raw4084 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4084step0 = (fun i j => raw4084 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4084step0 raw4084; decide +kernel
      have hl : raw4084step0Labels = raw4084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4084 raw4084Labels permutation434 hz
    mixedMoment B raw4084step0 raw4084step0Labels = mixedMoment B raw4084step1 raw4084step1Labels := by
      have hz : ∀ j, raw4084step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4084step1 = (fun i j => raw4084step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4084step1 raw4084step0; decide +kernel
      have hl : raw4084step1Labels = raw4084step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4084step0 raw4084step0Labels permutation80 hz
    mixedMoment B raw4084step1 raw4084step1Labels = mixedMoment B raw4084step2 raw4084step2Labels := by
      have ha : raw4084step2 = (fun i j => raw4084step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4084step2 raw4084step1; decide +kernel
      have hl : raw4084step2Labels = raw4084step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4084step1 raw4084step1Labels permutation8 permutation6
    _ = mixedMoment B node2726 node2726Labels := by rfl

def raw4085 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4085Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4085step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4085step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4085step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4085step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4085step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4085 raw4085Labels = mixedMoment B node3549 node3549Labels := by
  calc
    mixedMoment B raw4085 raw4085Labels = mixedMoment B raw4085step0 raw4085step0Labels := by
      have hz : ∀ j, raw4085 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4085step0 = (fun i j => raw4085 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4085step0 raw4085; decide +kernel
      have hl : raw4085step0Labels = raw4085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4085 raw4085Labels permutation434 hz
    mixedMoment B raw4085step0 raw4085step0Labels = mixedMoment B raw4085step1 raw4085step1Labels := by
      have hz : ∀ j, raw4085step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4085step1 = (fun i j => raw4085step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4085step1 raw4085step0; decide +kernel
      have hl : raw4085step1Labels = raw4085step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4085step0 raw4085step0Labels permutation80 hz
    mixedMoment B raw4085step1 raw4085step1Labels = mixedMoment B raw4085step2 raw4085step2Labels := by
      have ha : raw4085step2 = (fun i j => raw4085step1 (permutation28 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4085step2 raw4085step1; decide +kernel
      have hl : raw4085step2Labels = raw4085step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4085step1 raw4085step1Labels permutation28 permutation2
    _ = mixedMoment B node3549 node3549Labels := by rfl

def raw4086 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4086Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4086step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4086step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4086step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4086step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4086step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4086 raw4086Labels = mixedMoment B node3396 node3396Labels := by
  calc
    mixedMoment B raw4086 raw4086Labels = mixedMoment B raw4086step0 raw4086step0Labels := by
      have hz : ∀ j, raw4086 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4086step0 = (fun i j => raw4086 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4086step0 raw4086; decide +kernel
      have hl : raw4086step0Labels = raw4086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4086 raw4086Labels permutation434 hz
    mixedMoment B raw4086step0 raw4086step0Labels = mixedMoment B raw4086step1 raw4086step1Labels := by
      have hz : ∀ j, raw4086step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4086step1 = (fun i j => raw4086step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4086step1 raw4086step0; decide +kernel
      have hl : raw4086step1Labels = raw4086step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4086step0 raw4086step0Labels permutation80 hz
    mixedMoment B raw4086step1 raw4086step1Labels = mixedMoment B raw4086step2 raw4086step2Labels := by
      have ha : raw4086step2 = (fun i j => raw4086step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4086step2 raw4086step1; decide +kernel
      have hl : raw4086step2Labels = raw4086step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4086step1 raw4086step1Labels permutation29 permutation2
    _ = mixedMoment B node3396 node3396Labels := by rfl

def raw4087 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4087Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4087step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4087step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4087step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4087step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4087 raw4087Labels = mixedMoment B node3389 node3389Labels := by
  calc
    mixedMoment B raw4087 raw4087Labels = mixedMoment B raw4087step0 raw4087step0Labels := by
      have hz : ∀ j, raw4087 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4087step0 = (fun i j => raw4087 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4087step0 raw4087; decide +kernel
      have hl : raw4087step0Labels = raw4087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4087 raw4087Labels permutation434 hz
    mixedMoment B raw4087step0 raw4087step0Labels = mixedMoment B raw4087step1 raw4087step1Labels := by
      have ha : raw4087step1 = (fun i j => raw4087step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4087step1 raw4087step0; decide +kernel
      have hl : raw4087step1Labels = raw4087step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4087step0 raw4087step0Labels permutation44 permutation2
    mixedMoment B raw4087step1 raw4087step1Labels = mixedMoment B raw4087step2 raw4087step2Labels := by
      have ha : raw4087step2 = -raw4087step1 := by apply Matrix.ext; change ∀ i j, raw4087step2 i j = -(raw4087step1 i j); unfold raw4087step2 raw4087step1; decide +kernel
      have hl : raw4087step2Labels = raw4087step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3389 node3389Labels := by rfl

def raw4088 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4088Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4088step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4088step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4088step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4088 raw4088Labels = mixedMoment B node3389 node3389Labels := by
  calc
    mixedMoment B raw4088 raw4088Labels = mixedMoment B raw4088step0 raw4088step0Labels := by
      have hz : ∀ j, raw4088 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4088step0 = (fun i j => raw4088 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4088step0 raw4088; decide +kernel
      have hl : raw4088step0Labels = raw4088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4088 raw4088Labels permutation346 hz
    mixedMoment B raw4088step0 raw4088step0Labels = mixedMoment B raw4088step1 raw4088step1Labels := by
      have ha : raw4088step1 = (fun i j => raw4088step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4088step1 raw4088step0; decide +kernel
      have hl : raw4088step1Labels = raw4088step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4088step0 raw4088step0Labels permutation44 permutation2
    mixedMoment B raw4088step1 raw4088step1Labels = mixedMoment B raw4088step2 raw4088step2Labels := by
      have ha : raw4088step2 = -raw4088step1 := by apply Matrix.ext; change ∀ i j, raw4088step2 i j = -(raw4088step1 i j); unfold raw4088step2 raw4088step1; decide +kernel
      have hl : raw4088step2Labels = raw4088step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3389 node3389Labels := by rfl

def raw4089 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4089Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4089step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-2, -1, 3]]
def raw4089step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4089step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4089step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4089 raw4089Labels = mixedMoment B node3545 node3545Labels := by
  calc
    mixedMoment B raw4089 raw4089Labels = mixedMoment B raw4089step0 raw4089step0Labels := by
      have hz : ∀ j, raw4089 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4089step0 = (fun i j => raw4089 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4089step0 raw4089; decide +kernel
      have hl : raw4089step0Labels = raw4089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4089 raw4089Labels permutation434 hz
    mixedMoment B raw4089step0 raw4089step0Labels = mixedMoment B raw4089step1 raw4089step1Labels := by
      have hz : ∀ j, raw4089step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4089step1 = (fun i j => raw4089step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4089step1 raw4089step0; decide +kernel
      have hl : raw4089step1Labels = raw4089step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4089step0 raw4089step0Labels permutation80 hz
    mixedMoment B raw4089step1 raw4089step1Labels = mixedMoment B raw4089step2 raw4089step2Labels := by
      have ha : raw4089step2 = (fun i j => raw4089step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4089step2 raw4089step1; decide +kernel
      have hl : raw4089step2Labels = raw4089step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4089step1 raw4089step1Labels permutation29 permutation2
    _ = mixedMoment B node3545 node3545Labels := by rfl

def raw4090 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4090Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4090step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4090step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-3, 0, 3]]
def raw4090step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4090step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4090 raw4090Labels = mixedMoment B node2065 node2065Labels := by
  calc
    mixedMoment B raw4090 raw4090Labels = mixedMoment B raw4090step0 raw4090step0Labels := by
      have hz : ∀ j, raw4090 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4090step0 = (fun i j => raw4090 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4090step0 raw4090; decide +kernel
      have hl : raw4090step0Labels = raw4090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4090 raw4090Labels permutation434 hz
    mixedMoment B raw4090step0 raw4090step0Labels = mixedMoment B raw4090step1 raw4090step1Labels := by
      have hz : ∀ j, raw4090step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4090step1 = (fun i j => raw4090step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4090step1 raw4090step0; decide +kernel
      have hl : raw4090step1Labels = raw4090step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4090step0 raw4090step0Labels permutation80 hz
    mixedMoment B raw4090step1 raw4090step1Labels = mixedMoment B raw4090step2 raw4090step2Labels := by
      have ha : raw4090step2 = (fun i j => raw4090step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4090step2 raw4090step1; decide +kernel
      have hl : raw4090step2Labels = raw4090step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4090step1 raw4090step1Labels permutation29 permutation2
    _ = mixedMoment B node2065 node2065Labels := by rfl

def raw4091 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4091Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4091step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4091step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4091step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4091step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-2, -1, 3]]
def raw4091step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4091step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -2, 3], ![-2, 2, 0]]
def raw4091step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4091step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw4091step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4091 raw4091Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw4091 raw4091Labels = mixedMoment B raw4091step0 raw4091step0Labels := by
      have hz : ∀ j, raw4091 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4091step0 = (fun i j => raw4091 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4091step0 raw4091; decide +kernel
      have hl : raw4091step0Labels = raw4091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4091 raw4091Labels permutation434 hz
    mixedMoment B raw4091step0 raw4091step0Labels = mixedMoment B raw4091step1 raw4091step1Labels := by
      have hz : ∀ j, raw4091step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4091step1 = (fun i j => raw4091step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4091step1 raw4091step0; decide +kernel
      have hl : raw4091step1Labels = raw4091step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4091step0 raw4091step0Labels permutation80 hz
    mixedMoment B raw4091step1 raw4091step1Labels = mixedMoment B raw4091step2 raw4091step2Labels := by
      have hz : ∀ j, raw4091step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4091step2 = (fun i j => raw4091step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4091step2 raw4091step1; decide +kernel
      have hl : raw4091step2Labels = raw4091step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4091step1 raw4091step1Labels permutation14 hz
    mixedMoment B raw4091step2 raw4091step2Labels = mixedMoment B raw4091step3 raw4091step3Labels := by
      have ha : raw4091step3 = (fun i j => raw4091step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4091step3 raw4091step2; decide +kernel
      have hl : raw4091step3Labels = raw4091step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4091step2 raw4091step2Labels permutation3 permutation4
    mixedMoment B raw4091step3 raw4091step3Labels = mixedMoment B raw4091step4 raw4091step4Labels := by
      have ha : raw4091step4 = -raw4091step3 := by apply Matrix.ext; change ∀ i j, raw4091step4 i j = -(raw4091step3 i j); unfold raw4091step4 raw4091step3; decide +kernel
      have hl : raw4091step4Labels = raw4091step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2294 node2294Labels := by rfl

def raw4092 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4092step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw4092step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4092step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4092step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4092 raw4092Labels = mixedMoment B node2055 node2055Labels := by
  calc
    mixedMoment B raw4092 raw4092Labels = mixedMoment B raw4092step0 raw4092step0Labels := by
      have hz : ∀ j, raw4092 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4092step0 = (fun i j => raw4092 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4092step0 raw4092; decide +kernel
      have hl : raw4092step0Labels = raw4092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4092 raw4092Labels permutation434 hz
    mixedMoment B raw4092step0 raw4092step0Labels = mixedMoment B raw4092step1 raw4092step1Labels := by
      have ha : raw4092step1 = (fun i j => raw4092step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4092step1 raw4092step0; decide +kernel
      have hl : raw4092step1Labels = raw4092step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4092step0 raw4092step0Labels permutation33 permutation4
    mixedMoment B raw4092step1 raw4092step1Labels = mixedMoment B raw4092step2 raw4092step2Labels := by
      have ha : raw4092step2 = -raw4092step1 := by apply Matrix.ext; change ∀ i j, raw4092step2 i j = -(raw4092step1 i j); unfold raw4092step2 raw4092step1; decide +kernel
      have hl : raw4092step2Labels = raw4092step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2055 node2055Labels := by rfl

def raw4093 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4093Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4093step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4093step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, -1, 3]]
def raw4093step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4093step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -2, 3], ![-3, 3, 0]]
def raw4093step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4093step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw4093step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4093 raw4093Labels = mixedMoment B node2063 node2063Labels := by
  calc
    mixedMoment B raw4093 raw4093Labels = mixedMoment B raw4093step0 raw4093step0Labels := by
      have hz : ∀ j, raw4093 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4093step0 = (fun i j => raw4093 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4093step0 raw4093; decide +kernel
      have hl : raw4093step0Labels = raw4093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4093 raw4093Labels permutation434 hz
    mixedMoment B raw4093step0 raw4093step0Labels = mixedMoment B raw4093step1 raw4093step1Labels := by
      have hz : ∀ j, raw4093step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4093step1 = (fun i j => raw4093step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4093step1 raw4093step0; decide +kernel
      have hl : raw4093step1Labels = raw4093step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4093step0 raw4093step0Labels permutation80 hz
    mixedMoment B raw4093step1 raw4093step1Labels = mixedMoment B raw4093step2 raw4093step2Labels := by
      have ha : raw4093step2 = (fun i j => raw4093step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4093step2 raw4093step1; decide +kernel
      have hl : raw4093step2Labels = raw4093step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4093step1 raw4093step1Labels permutation9 permutation4
    mixedMoment B raw4093step2 raw4093step2Labels = mixedMoment B raw4093step3 raw4093step3Labels := by
      have ha : raw4093step3 = -raw4093step2 := by apply Matrix.ext; change ∀ i j, raw4093step3 i j = -(raw4093step2 i j); unfold raw4093step3 raw4093step2; decide +kernel
      have hl : raw4093step3Labels = raw4093step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2063 node2063Labels := by rfl

def raw4094 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4094Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4094step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4094step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, -2, 3]]
def raw4094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4094step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw4094step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4094step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4094step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4094 raw4094Labels = mixedMoment B node2065 node2065Labels := by
  calc
    mixedMoment B raw4094 raw4094Labels = mixedMoment B raw4094step0 raw4094step0Labels := by
      have hz : ∀ j, raw4094 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4094step0 = (fun i j => raw4094 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4094step0 raw4094; decide +kernel
      have hl : raw4094step0Labels = raw4094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4094 raw4094Labels permutation434 hz
    mixedMoment B raw4094step0 raw4094step0Labels = mixedMoment B raw4094step1 raw4094step1Labels := by
      have hz : ∀ j, raw4094step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4094step1 = (fun i j => raw4094step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4094step1 raw4094step0; decide +kernel
      have hl : raw4094step1Labels = raw4094step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4094step0 raw4094step0Labels permutation80 hz
    mixedMoment B raw4094step1 raw4094step1Labels = mixedMoment B raw4094step2 raw4094step2Labels := by
      have ha : raw4094step2 = (fun i j => raw4094step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4094step2 raw4094step1; decide +kernel
      have hl : raw4094step2Labels = raw4094step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4094step1 raw4094step1Labels permutation8 permutation4
    mixedMoment B raw4094step2 raw4094step2Labels = mixedMoment B raw4094step3 raw4094step3Labels := by
      have ha : raw4094step3 = -raw4094step2 := by apply Matrix.ext; change ∀ i j, raw4094step3 i j = -(raw4094step2 i j); unfold raw4094step3 raw4094step2; decide +kernel
      have hl : raw4094step3Labels = raw4094step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2065 node2065Labels := by rfl

def raw4095 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4095Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4095step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, -1, 3]]
def raw4095step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4095step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw4095step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4095 raw4095Labels = mixedMoment B node3549 node3549Labels := by
  calc
    mixedMoment B raw4095 raw4095Labels = mixedMoment B raw4095step0 raw4095step0Labels := by
      have hz : ∀ j, raw4095 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4095step0 = (fun i j => raw4095 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4095step0 raw4095; decide +kernel
      have hl : raw4095step0Labels = raw4095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4095 raw4095Labels permutation434 hz
    mixedMoment B raw4095step0 raw4095step0Labels = mixedMoment B raw4095step1 raw4095step1Labels := by
      have hz : ∀ j, raw4095step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw4095step1 = (fun i j => raw4095step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw4095step1 raw4095step0; decide +kernel
      have hl : raw4095step1Labels = raw4095step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4095step0 raw4095step0Labels permutation56 hz
    mixedMoment B raw4095step1 raw4095step1Labels = mixedMoment B raw4095step2 raw4095step2Labels := by
      have ha : raw4095step2 = (fun i j => raw4095step1 (permutation28 i) (permutation2 j)) := by apply Matrix.ext; unfold raw4095step2 raw4095step1; decide +kernel
      have hl : raw4095step2Labels = raw4095step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4095step1 raw4095step1Labels permutation28 permutation2
    _ = mixedMoment B node3549 node3549Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
