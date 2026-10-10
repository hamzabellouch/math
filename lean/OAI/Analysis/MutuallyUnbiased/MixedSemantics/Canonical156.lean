import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw19968 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -4, 4]]
def raw19968Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -4, 4]]
def raw19968step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -4, 4]]
def raw19968step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19968step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -4, 4]]
def raw19968step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19968step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-4, 1, 3]]
def raw19968step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19968step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19968step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19968step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19968step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19968 raw19968Labels = mixedMoment B node4274 node4274Labels := by
  calc
    mixedMoment B raw19968 raw19968Labels = mixedMoment B raw19968step0 raw19968step0Labels := by
      have hz : ∀ j, raw19968 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19968step0 = (fun i j => raw19968 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19968step0 raw19968; decide +kernel
      have hl : raw19968step0Labels = raw19968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19968 raw19968Labels permutation520 hz
    mixedMoment B raw19968step0 raw19968step0Labels = mixedMoment B raw19968step1 raw19968step1Labels := by
      have hz : ∀ j, raw19968step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19968step1 = (fun i j => raw19968step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19968step1 raw19968step0; decide +kernel
      have hl : raw19968step1Labels = raw19968step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19968step0 raw19968step0Labels permutation104 hz
    mixedMoment B raw19968step1 raw19968step1Labels = mixedMoment B raw19968step2 raw19968step2Labels := by
      have hz : ∀ j, raw19968step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw19968step2 = (fun i j => raw19968step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw19968step2 raw19968step1; decide +kernel
      have hl : raw19968step2Labels = raw19968step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19968step1 raw19968step1Labels permutation20 hz
    mixedMoment B raw19968step2 raw19968step2Labels = mixedMoment B raw19968step3 raw19968step3Labels := by
      have ha : raw19968step3 = (fun i j => raw19968step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19968step3 raw19968step2; decide +kernel
      have hl : raw19968step3Labels = raw19968step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19968step2 raw19968step2Labels permutation7 permutation6
    mixedMoment B raw19968step3 raw19968step3Labels = mixedMoment B raw19968step4 raw19968step4Labels := by
      have ha : raw19968step4 = -raw19968step3 := by apply Matrix.ext; change ∀ i j, raw19968step4 i j = -(raw19968step3 i j); unfold raw19968step4 raw19968step3; decide +kernel
      have hl : raw19968step4Labels = raw19968step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19968step4 raw19968step4Labels = mixedMoment B raw19968step5 raw19968step5Labels := by
      have ha : raw19968step5 = raw19968step4 := by apply Matrix.ext; unfold raw19968step5 raw19968step4; decide +kernel
      have hl : raw19968step4Labels = labelEmbedding9 ∘ raw19968step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19968step4 raw19968step4Labels raw19968step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4274 node4274Labels := by rfl

def raw19969 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -4, 4]]
def raw19969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -4, 4]]
def raw19969step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19969step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19969step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19969step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -4, 4]]
def raw19969step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19969step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-4, 1, 3]]
def raw19969step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19969step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19969step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19969step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19969step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19969 raw19969Labels = mixedMoment B node4274 node4274Labels := by
  calc
    mixedMoment B raw19969 raw19969Labels = mixedMoment B raw19969step0 raw19969step0Labels := by
      have hz : ∀ j, raw19969 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19969step0 = (fun i j => raw19969 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19969step0 raw19969; decide +kernel
      have hl : raw19969step0Labels = raw19969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19969 raw19969Labels permutation520 hz
    mixedMoment B raw19969step0 raw19969step0Labels = mixedMoment B raw19969step1 raw19969step1Labels := by
      have hz : ∀ j, raw19969step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw19969step1 = (fun i j => raw19969step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw19969step1 raw19969step0; decide +kernel
      have hl : raw19969step1Labels = raw19969step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19969step0 raw19969step0Labels permutation104 hz
    mixedMoment B raw19969step1 raw19969step1Labels = mixedMoment B raw19969step2 raw19969step2Labels := by
      have hz : ∀ j, raw19969step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19969step2 = (fun i j => raw19969step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19969step2 raw19969step1; decide +kernel
      have hl : raw19969step2Labels = raw19969step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19969step1 raw19969step1Labels permutation14 hz
    mixedMoment B raw19969step2 raw19969step2Labels = mixedMoment B raw19969step3 raw19969step3Labels := by
      have ha : raw19969step3 = (fun i j => raw19969step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19969step3 raw19969step2; decide +kernel
      have hl : raw19969step3Labels = raw19969step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19969step2 raw19969step2Labels permutation7 permutation6
    mixedMoment B raw19969step3 raw19969step3Labels = mixedMoment B raw19969step4 raw19969step4Labels := by
      have ha : raw19969step4 = -raw19969step3 := by apply Matrix.ext; change ∀ i j, raw19969step4 i j = -(raw19969step3 i j); unfold raw19969step4 raw19969step3; decide +kernel
      have hl : raw19969step4Labels = raw19969step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19969step4 raw19969step4Labels = mixedMoment B raw19969step5 raw19969step5Labels := by
      have ha : raw19969step5 = raw19969step4 := by apply Matrix.ext; unfold raw19969step5 raw19969step4; decide +kernel
      have hl : raw19969step4Labels = labelEmbedding9 ∘ raw19969step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19969step4 raw19969step4Labels raw19969step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4274 node4274Labels := by rfl

def raw19970 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -4, 4]]
def raw19970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19970step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19970step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw19970step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19970step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -4, 4]]
def raw19970step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19970step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-4, 1, 3]]
def raw19970step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19970step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19970step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19970step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw19970step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19970 raw19970Labels = mixedMoment B node4274 node4274Labels := by
  calc
    mixedMoment B raw19970 raw19970Labels = mixedMoment B raw19970step0 raw19970step0Labels := by
      have hz : ∀ j, raw19970 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19970step0 = (fun i j => raw19970 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19970step0 raw19970; decide +kernel
      have hl : raw19970step0Labels = raw19970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19970 raw19970Labels permutation520 hz
    mixedMoment B raw19970step0 raw19970step0Labels = mixedMoment B raw19970step1 raw19970step1Labels := by
      have hz : ∀ j, raw19970step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19970step1 = (fun i j => raw19970step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19970step1 raw19970step0; decide +kernel
      have hl : raw19970step1Labels = raw19970step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19970step0 raw19970step0Labels permutation80 hz
    mixedMoment B raw19970step1 raw19970step1Labels = mixedMoment B raw19970step2 raw19970step2Labels := by
      have hz : ∀ j, raw19970step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19970step2 = (fun i j => raw19970step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19970step2 raw19970step1; decide +kernel
      have hl : raw19970step2Labels = raw19970step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19970step1 raw19970step1Labels permutation14 hz
    mixedMoment B raw19970step2 raw19970step2Labels = mixedMoment B raw19970step3 raw19970step3Labels := by
      have ha : raw19970step3 = (fun i j => raw19970step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19970step3 raw19970step2; decide +kernel
      have hl : raw19970step3Labels = raw19970step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19970step2 raw19970step2Labels permutation7 permutation6
    mixedMoment B raw19970step3 raw19970step3Labels = mixedMoment B raw19970step4 raw19970step4Labels := by
      have ha : raw19970step4 = -raw19970step3 := by apply Matrix.ext; change ∀ i j, raw19970step4 i j = -(raw19970step3 i j); unfold raw19970step4 raw19970step3; decide +kernel
      have hl : raw19970step4Labels = raw19970step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19970step4 raw19970step4Labels = mixedMoment B raw19970step5 raw19970step5Labels := by
      have ha : raw19970step5 = raw19970step4 := by apply Matrix.ext; unfold raw19970step5 raw19970step4; decide +kernel
      have hl : raw19970step4Labels = labelEmbedding9 ∘ raw19970step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19970step4 raw19970step4Labels raw19970step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4274 node4274Labels := by rfl

def raw19971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19971step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19971step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19971step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw19971step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19971step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw19971step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19971 raw19971Labels = mixedMoment B node4266 node4266Labels := by
  calc
    mixedMoment B raw19971 raw19971Labels = mixedMoment B raw19971step0 raw19971step0Labels := by
      have hz : ∀ j, raw19971 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19971step0 = (fun i j => raw19971 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19971step0 raw19971; decide +kernel
      have hl : raw19971step0Labels = raw19971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19971 raw19971Labels permutation434 hz
    mixedMoment B raw19971step0 raw19971step0Labels = mixedMoment B raw19971step1 raw19971step1Labels := by
      have hz : ∀ j, raw19971step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19971step1 = (fun i j => raw19971step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19971step1 raw19971step0; decide +kernel
      have hl : raw19971step1Labels = raw19971step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19971step0 raw19971step0Labels permutation80 hz
    mixedMoment B raw19971step1 raw19971step1Labels = mixedMoment B raw19971step2 raw19971step2Labels := by
      have ha : raw19971step2 = (fun i j => raw19971step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19971step2 raw19971step1; decide +kernel
      have hl : raw19971step2Labels = raw19971step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19971step1 raw19971step1Labels permutation31 permutation2
    mixedMoment B raw19971step2 raw19971step2Labels = mixedMoment B raw19971step3 raw19971step3Labels := by
      have ha : raw19971step3 = -raw19971step2 := by apply Matrix.ext; change ∀ i j, raw19971step3 i j = -(raw19971step2 i j); unfold raw19971step3 raw19971step2; decide +kernel
      have hl : raw19971step3Labels = raw19971step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4266 node4266Labels := by rfl

def raw19972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19972step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19972step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19972step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw19972step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19972step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw19972step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19972 raw19972Labels = mixedMoment B node4266 node4266Labels := by
  calc
    mixedMoment B raw19972 raw19972Labels = mixedMoment B raw19972step0 raw19972step0Labels := by
      have hz : ∀ j, raw19972 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19972step0 = (fun i j => raw19972 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19972step0 raw19972; decide +kernel
      have hl : raw19972step0Labels = raw19972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19972 raw19972Labels permutation434 hz
    mixedMoment B raw19972step0 raw19972step0Labels = mixedMoment B raw19972step1 raw19972step1Labels := by
      have hz : ∀ j, raw19972step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19972step1 = (fun i j => raw19972step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19972step1 raw19972step0; decide +kernel
      have hl : raw19972step1Labels = raw19972step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19972step0 raw19972step0Labels permutation56 hz
    mixedMoment B raw19972step1 raw19972step1Labels = mixedMoment B raw19972step2 raw19972step2Labels := by
      have ha : raw19972step2 = (fun i j => raw19972step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19972step2 raw19972step1; decide +kernel
      have hl : raw19972step2Labels = raw19972step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19972step1 raw19972step1Labels permutation31 permutation2
    mixedMoment B raw19972step2 raw19972step2Labels = mixedMoment B raw19972step3 raw19972step3Labels := by
      have ha : raw19972step3 = -raw19972step2 := by apply Matrix.ext; change ∀ i j, raw19972step3 i j = -(raw19972step2 i j); unfold raw19972step3 raw19972step2; decide +kernel
      have hl : raw19972step3Labels = raw19972step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4266 node4266Labels := by rfl

def raw19973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19973step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19973step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw19973step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19973step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw19973step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19973 raw19973Labels = mixedMoment B node4266 node4266Labels := by
  calc
    mixedMoment B raw19973 raw19973Labels = mixedMoment B raw19973step0 raw19973step0Labels := by
      have hz : ∀ j, raw19973 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19973step0 = (fun i j => raw19973 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19973step0 raw19973; decide +kernel
      have hl : raw19973step0Labels = raw19973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19973 raw19973Labels permutation346 hz
    mixedMoment B raw19973step0 raw19973step0Labels = mixedMoment B raw19973step1 raw19973step1Labels := by
      have hz : ∀ j, raw19973step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19973step1 = (fun i j => raw19973step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19973step1 raw19973step0; decide +kernel
      have hl : raw19973step1Labels = raw19973step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19973step0 raw19973step0Labels permutation56 hz
    mixedMoment B raw19973step1 raw19973step1Labels = mixedMoment B raw19973step2 raw19973step2Labels := by
      have ha : raw19973step2 = (fun i j => raw19973step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19973step2 raw19973step1; decide +kernel
      have hl : raw19973step2Labels = raw19973step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19973step1 raw19973step1Labels permutation31 permutation2
    mixedMoment B raw19973step2 raw19973step2Labels = mixedMoment B raw19973step3 raw19973step3Labels := by
      have ha : raw19973step3 = -raw19973step2 := by apply Matrix.ext; change ∀ i j, raw19973step3 i j = -(raw19973step2 i j); unfold raw19973step3 raw19973step2; decide +kernel
      have hl : raw19973step3Labels = raw19973step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4266 node4266Labels := by rfl

def raw19974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw19974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw19974step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19974step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw19974step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19974step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![4, 0, -4]]
def raw19974step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19974step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![4, -4]]
def raw19974step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw19974step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-3, 3]]
def raw19974step4Labels : Fin 2 → Fin 3 := ![0, 2]

def raw19974step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw19974step5Labels : Fin 2 → Fin 3 := ![0, 2]

def raw19974step6 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw19974step6Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19974 raw19974Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw19974 raw19974Labels = mixedMoment B raw19974step0 raw19974step0Labels := by
      have hz : ∀ j, raw19974 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19974step0 = (fun i j => raw19974 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19974step0 raw19974; decide +kernel
      have hl : raw19974step0Labels = raw19974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19974 raw19974Labels permutation434 hz
    mixedMoment B raw19974step0 raw19974step0Labels = mixedMoment B raw19974step1 raw19974step1Labels := by
      have hz : ∀ j, raw19974step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19974step1 = (fun i j => raw19974step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19974step1 raw19974step0; decide +kernel
      have hl : raw19974step1Labels = raw19974step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19974step0 raw19974step0Labels permutation80 hz
    mixedMoment B raw19974step1 raw19974step1Labels = mixedMoment B raw19974step2 raw19974step2Labels := by
      have hz : ∀ j, raw19974step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19974step2 = (fun i j => raw19974step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19974step2 raw19974step1; decide +kernel
      have hl : raw19974step2Labels = raw19974step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19974step1 raw19974step1Labels permutation14 hz
    mixedMoment B raw19974step2 raw19974step2Labels = mixedMoment B raw19974step3 raw19974step3Labels := by
      have hz : ∀ i, raw19974step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw19974step3 = (fun i j => raw19974step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw19974step3 raw19974step2; decide +kernel
      have hl : raw19974step3Labels = (fun j => raw19974step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19974step2 raw19974step2Labels permutation4 hz
    mixedMoment B raw19974step3 raw19974step3Labels = mixedMoment B raw19974step4 raw19974step4Labels := by
      have ha : raw19974step4 = (fun i j => raw19974step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw19974step4 raw19974step3; decide +kernel
      have hl : raw19974step4Labels = raw19974step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19974step3 raw19974step3Labels permutation7 permutation0
    mixedMoment B raw19974step4 raw19974step4Labels = mixedMoment B raw19974step5 raw19974step5Labels := by
      have ha : raw19974step5 = -raw19974step4 := by apply Matrix.ext; change ∀ i j, raw19974step5 i j = -(raw19974step4 i j); unfold raw19974step5 raw19974step4; decide +kernel
      have hl : raw19974step5Labels = raw19974step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19974step5 raw19974step5Labels = mixedMoment B raw19974step6 raw19974step6Labels := by
      have ha : raw19974step6 = raw19974step5 := by apply Matrix.ext; unfold raw19974step6 raw19974step5; decide +kernel
      have hl : raw19974step5Labels = labelEmbedding2 ∘ raw19974step6Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19974step5 raw19974step5Labels raw19974step6Labels labelEmbedding2 hl
    _ = mixedMoment B node4070 node4070Labels := by rfl

def raw19975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw19975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw19975step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw19975step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19975step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![3, 1, -4]]
def raw19975step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19975step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19975step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19975step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw19975step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19975 raw19975Labels = mixedMoment B node4501 node4501Labels := by
  calc
    mixedMoment B raw19975 raw19975Labels = mixedMoment B raw19975step0 raw19975step0Labels := by
      have hz : ∀ j, raw19975 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19975step0 = (fun i j => raw19975 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19975step0 raw19975; decide +kernel
      have hl : raw19975step0Labels = raw19975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19975 raw19975Labels permutation434 hz
    mixedMoment B raw19975step0 raw19975step0Labels = mixedMoment B raw19975step1 raw19975step1Labels := by
      have hz : ∀ j, raw19975step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19975step1 = (fun i j => raw19975step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19975step1 raw19975step0; decide +kernel
      have hl : raw19975step1Labels = raw19975step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19975step0 raw19975step0Labels permutation80 hz
    mixedMoment B raw19975step1 raw19975step1Labels = mixedMoment B raw19975step2 raw19975step2Labels := by
      have hz : ∀ j, raw19975step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19975step2 = (fun i j => raw19975step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19975step2 raw19975step1; decide +kernel
      have hl : raw19975step2Labels = raw19975step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19975step1 raw19975step1Labels permutation14 hz
    mixedMoment B raw19975step2 raw19975step2Labels = mixedMoment B raw19975step3 raw19975step3Labels := by
      have ha : raw19975step3 = (fun i j => raw19975step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19975step3 raw19975step2; decide +kernel
      have hl : raw19975step3Labels = raw19975step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19975step2 raw19975step2Labels permutation7 permutation7
    mixedMoment B raw19975step3 raw19975step3Labels = mixedMoment B raw19975step4 raw19975step4Labels := by
      have ha : raw19975step4 = raw19975step3 := by apply Matrix.ext; unfold raw19975step4 raw19975step3; decide +kernel
      have hl : raw19975step3Labels = labelEmbedding10 ∘ raw19975step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19975step3 raw19975step3Labels raw19975step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4501 node4501Labels := by rfl

def raw19976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19976step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19976step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw19976step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19976 raw19976Labels = mixedMoment B node4142 node4142Labels := by
  calc
    mixedMoment B raw19976 raw19976Labels = mixedMoment B raw19976step0 raw19976step0Labels := by
      have hz : ∀ j, raw19976 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19976step0 = (fun i j => raw19976 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19976step0 raw19976; decide +kernel
      have hl : raw19976step0Labels = raw19976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19976 raw19976Labels permutation434 hz
    mixedMoment B raw19976step0 raw19976step0Labels = mixedMoment B raw19976step1 raw19976step1Labels := by
      have hz : ∀ j, raw19976step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19976step1 = (fun i j => raw19976step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19976step1 raw19976step0; decide +kernel
      have hl : raw19976step1Labels = raw19976step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19976step0 raw19976step0Labels permutation80 hz
    mixedMoment B raw19976step1 raw19976step1Labels = mixedMoment B raw19976step2 raw19976step2Labels := by
      have ha : raw19976step2 = (fun i j => raw19976step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19976step2 raw19976step1; decide +kernel
      have hl : raw19976step2Labels = raw19976step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19976step1 raw19976step1Labels permutation10 permutation2
    _ = mixedMoment B node4142 node4142Labels := by rfl

def raw19977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19977step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19977step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19977step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19977 raw19977Labels = mixedMoment B node4198 node4198Labels := by
  calc
    mixedMoment B raw19977 raw19977Labels = mixedMoment B raw19977step0 raw19977step0Labels := by
      have hz : ∀ j, raw19977 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19977step0 = (fun i j => raw19977 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19977step0 raw19977; decide +kernel
      have hl : raw19977step0Labels = raw19977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19977 raw19977Labels permutation434 hz
    mixedMoment B raw19977step0 raw19977step0Labels = mixedMoment B raw19977step1 raw19977step1Labels := by
      have ha : raw19977step1 = (fun i j => raw19977step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19977step1 raw19977step0; decide +kernel
      have hl : raw19977step1Labels = raw19977step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19977step0 raw19977step0Labels permutation139 permutation2
    mixedMoment B raw19977step1 raw19977step1Labels = mixedMoment B raw19977step2 raw19977step2Labels := by
      have ha : raw19977step2 = -raw19977step1 := by apply Matrix.ext; change ∀ i j, raw19977step2 i j = -(raw19977step1 i j); unfold raw19977step2 raw19977step1; decide +kernel
      have hl : raw19977step2Labels = raw19977step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4198 node4198Labels := by rfl

def raw19978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19978step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19978step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19978step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19978step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19978 raw19978Labels = mixedMoment B node4198 node4198Labels := by
  calc
    mixedMoment B raw19978 raw19978Labels = mixedMoment B raw19978step0 raw19978step0Labels := by
      have hz : ∀ j, raw19978 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19978step0 = (fun i j => raw19978 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19978step0 raw19978; decide +kernel
      have hl : raw19978step0Labels = raw19978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19978 raw19978Labels permutation346 hz
    mixedMoment B raw19978step0 raw19978step0Labels = mixedMoment B raw19978step1 raw19978step1Labels := by
      have ha : raw19978step1 = (fun i j => raw19978step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19978step1 raw19978step0; decide +kernel
      have hl : raw19978step1Labels = raw19978step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19978step0 raw19978step0Labels permutation139 permutation2
    mixedMoment B raw19978step1 raw19978step1Labels = mixedMoment B raw19978step2 raw19978step2Labels := by
      have ha : raw19978step2 = -raw19978step1 := by apply Matrix.ext; change ∀ i j, raw19978step2 i j = -(raw19978step1 i j); unfold raw19978step2 raw19978step1; decide +kernel
      have hl : raw19978step2Labels = raw19978step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4198 node4198Labels := by rfl

def raw19979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw19979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw19979step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw19979step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19979step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-4, 1, 3]]
def raw19979step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19979step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![4, -1, -3]]
def raw19979step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19979 raw19979Labels = mixedMoment B node4222 node4222Labels := by
  calc
    mixedMoment B raw19979 raw19979Labels = mixedMoment B raw19979step0 raw19979step0Labels := by
      have hz : ∀ j, raw19979 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19979step0 = (fun i j => raw19979 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19979step0 raw19979; decide +kernel
      have hl : raw19979step0Labels = raw19979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19979 raw19979Labels permutation434 hz
    mixedMoment B raw19979step0 raw19979step0Labels = mixedMoment B raw19979step1 raw19979step1Labels := by
      have hz : ∀ j, raw19979step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19979step1 = (fun i j => raw19979step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19979step1 raw19979step0; decide +kernel
      have hl : raw19979step1Labels = raw19979step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19979step0 raw19979step0Labels permutation80 hz
    mixedMoment B raw19979step1 raw19979step1Labels = mixedMoment B raw19979step2 raw19979step2Labels := by
      have ha : raw19979step2 = (fun i j => raw19979step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19979step2 raw19979step1; decide +kernel
      have hl : raw19979step2Labels = raw19979step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19979step1 raw19979step1Labels permutation29 permutation2
    mixedMoment B raw19979step2 raw19979step2Labels = mixedMoment B raw19979step3 raw19979step3Labels := by
      have ha : raw19979step3 = -raw19979step2 := by apply Matrix.ext; change ∀ i j, raw19979step3 i j = -(raw19979step2 i j); unfold raw19979step3 raw19979step2; decide +kernel
      have hl : raw19979step3Labels = raw19979step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4222 node4222Labels := by rfl

def raw19980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw19980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw19980step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19980step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![3, 1, -4]]
def raw19980step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19980step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw19980step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19980 raw19980Labels = mixedMoment B node4421 node4421Labels := by
  calc
    mixedMoment B raw19980 raw19980Labels = mixedMoment B raw19980step0 raw19980step0Labels := by
      have hz : ∀ j, raw19980 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19980step0 = (fun i j => raw19980 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19980step0 raw19980; decide +kernel
      have hl : raw19980step0Labels = raw19980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19980 raw19980Labels permutation434 hz
    mixedMoment B raw19980step0 raw19980step0Labels = mixedMoment B raw19980step1 raw19980step1Labels := by
      have hz : ∀ j, raw19980step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19980step1 = (fun i j => raw19980step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19980step1 raw19980step0; decide +kernel
      have hl : raw19980step1Labels = raw19980step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19980step0 raw19980step0Labels permutation80 hz
    mixedMoment B raw19980step1 raw19980step1Labels = mixedMoment B raw19980step2 raw19980step2Labels := by
      have ha : raw19980step2 = (fun i j => raw19980step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19980step2 raw19980step1; decide +kernel
      have hl : raw19980step2Labels = raw19980step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19980step1 raw19980step1Labels permutation10 permutation2
    _ = mixedMoment B node4421 node4421Labels := by rfl

def raw19981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19981step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19981step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19981step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw19981step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19981 raw19981Labels = mixedMoment B node4142 node4142Labels := by
  calc
    mixedMoment B raw19981 raw19981Labels = mixedMoment B raw19981step0 raw19981step0Labels := by
      have hz : ∀ j, raw19981 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19981step0 = (fun i j => raw19981 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19981step0 raw19981; decide +kernel
      have hl : raw19981step0Labels = raw19981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19981 raw19981Labels permutation434 hz
    mixedMoment B raw19981step0 raw19981step0Labels = mixedMoment B raw19981step1 raw19981step1Labels := by
      have hz : ∀ j, raw19981step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19981step1 = (fun i j => raw19981step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19981step1 raw19981step0; decide +kernel
      have hl : raw19981step1Labels = raw19981step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19981step0 raw19981step0Labels permutation56 hz
    mixedMoment B raw19981step1 raw19981step1Labels = mixedMoment B raw19981step2 raw19981step2Labels := by
      have ha : raw19981step2 = (fun i j => raw19981step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19981step2 raw19981step1; decide +kernel
      have hl : raw19981step2Labels = raw19981step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19981step1 raw19981step1Labels permutation10 permutation2
    _ = mixedMoment B node4142 node4142Labels := by rfl

def raw19982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19982step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19982step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19982step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19982 raw19982Labels = mixedMoment B node4198 node4198Labels := by
  calc
    mixedMoment B raw19982 raw19982Labels = mixedMoment B raw19982step0 raw19982step0Labels := by
      have hz : ∀ j, raw19982 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19982step0 = (fun i j => raw19982 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19982step0 raw19982; decide +kernel
      have hl : raw19982step0Labels = raw19982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19982 raw19982Labels permutation434 hz
    mixedMoment B raw19982step0 raw19982step0Labels = mixedMoment B raw19982step1 raw19982step1Labels := by
      have ha : raw19982step1 = (fun i j => raw19982step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19982step1 raw19982step0; decide +kernel
      have hl : raw19982step1Labels = raw19982step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19982step0 raw19982step0Labels permutation145 permutation2
    mixedMoment B raw19982step1 raw19982step1Labels = mixedMoment B raw19982step2 raw19982step2Labels := by
      have ha : raw19982step2 = -raw19982step1 := by apply Matrix.ext; change ∀ i j, raw19982step2 i j = -(raw19982step1 i j); unfold raw19982step2 raw19982step1; decide +kernel
      have hl : raw19982step2Labels = raw19982step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4198 node4198Labels := by rfl

def raw19983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19983step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19983step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19983step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19983step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19983 raw19983Labels = mixedMoment B node4198 node4198Labels := by
  calc
    mixedMoment B raw19983 raw19983Labels = mixedMoment B raw19983step0 raw19983step0Labels := by
      have hz : ∀ j, raw19983 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19983step0 = (fun i j => raw19983 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19983step0 raw19983; decide +kernel
      have hl : raw19983step0Labels = raw19983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19983 raw19983Labels permutation265 hz
    mixedMoment B raw19983step0 raw19983step0Labels = mixedMoment B raw19983step1 raw19983step1Labels := by
      have ha : raw19983step1 = (fun i j => raw19983step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19983step1 raw19983step0; decide +kernel
      have hl : raw19983step1Labels = raw19983step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19983step0 raw19983step0Labels permutation139 permutation2
    mixedMoment B raw19983step1 raw19983step1Labels = mixedMoment B raw19983step2 raw19983step2Labels := by
      have ha : raw19983step2 = -raw19983step1 := by apply Matrix.ext; change ∀ i j, raw19983step2 i j = -(raw19983step1 i j); unfold raw19983step2 raw19983step1; decide +kernel
      have hl : raw19983step2Labels = raw19983step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4198 node4198Labels := by rfl

def raw19984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw19984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw19984step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19984step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw19984step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19984step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-4, 1, 3]]
def raw19984step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19984step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![4, -1, -3]]
def raw19984step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19984 raw19984Labels = mixedMoment B node4222 node4222Labels := by
  calc
    mixedMoment B raw19984 raw19984Labels = mixedMoment B raw19984step0 raw19984step0Labels := by
      have hz : ∀ j, raw19984 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19984step0 = (fun i j => raw19984 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19984step0 raw19984; decide +kernel
      have hl : raw19984step0Labels = raw19984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19984 raw19984Labels permutation434 hz
    mixedMoment B raw19984step0 raw19984step0Labels = mixedMoment B raw19984step1 raw19984step1Labels := by
      have hz : ∀ j, raw19984step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19984step1 = (fun i j => raw19984step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19984step1 raw19984step0; decide +kernel
      have hl : raw19984step1Labels = raw19984step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19984step0 raw19984step0Labels permutation56 hz
    mixedMoment B raw19984step1 raw19984step1Labels = mixedMoment B raw19984step2 raw19984step2Labels := by
      have ha : raw19984step2 = (fun i j => raw19984step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19984step2 raw19984step1; decide +kernel
      have hl : raw19984step2Labels = raw19984step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19984step1 raw19984step1Labels permutation29 permutation2
    mixedMoment B raw19984step2 raw19984step2Labels = mixedMoment B raw19984step3 raw19984step3Labels := by
      have ha : raw19984step3 = -raw19984step2 := by apply Matrix.ext; change ∀ i j, raw19984step3 i j = -(raw19984step2 i j); unfold raw19984step3 raw19984step2; decide +kernel
      have hl : raw19984step3Labels = raw19984step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4222 node4222Labels := by rfl

def raw19985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw19985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 1, -4]]
def raw19985step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19985step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![3, 1, -4]]
def raw19985step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19985step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw19985step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19985 raw19985Labels = mixedMoment B node4421 node4421Labels := by
  calc
    mixedMoment B raw19985 raw19985Labels = mixedMoment B raw19985step0 raw19985step0Labels := by
      have hz : ∀ j, raw19985 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19985step0 = (fun i j => raw19985 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19985step0 raw19985; decide +kernel
      have hl : raw19985step0Labels = raw19985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19985 raw19985Labels permutation434 hz
    mixedMoment B raw19985step0 raw19985step0Labels = mixedMoment B raw19985step1 raw19985step1Labels := by
      have hz : ∀ j, raw19985step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19985step1 = (fun i j => raw19985step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19985step1 raw19985step0; decide +kernel
      have hl : raw19985step1Labels = raw19985step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19985step0 raw19985step0Labels permutation56 hz
    mixedMoment B raw19985step1 raw19985step1Labels = mixedMoment B raw19985step2 raw19985step2Labels := by
      have ha : raw19985step2 = (fun i j => raw19985step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19985step2 raw19985step1; decide +kernel
      have hl : raw19985step2Labels = raw19985step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19985step1 raw19985step1Labels permutation10 permutation2
    _ = mixedMoment B node4421 node4421Labels := by rfl

def raw19986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19986step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19986step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19986step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw19986step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19986 raw19986Labels = mixedMoment B node4142 node4142Labels := by
  calc
    mixedMoment B raw19986 raw19986Labels = mixedMoment B raw19986step0 raw19986step0Labels := by
      have hz : ∀ j, raw19986 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19986step0 = (fun i j => raw19986 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19986step0 raw19986; decide +kernel
      have hl : raw19986step0Labels = raw19986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19986 raw19986Labels permutation346 hz
    mixedMoment B raw19986step0 raw19986step0Labels = mixedMoment B raw19986step1 raw19986step1Labels := by
      have hz : ∀ j, raw19986step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19986step1 = (fun i j => raw19986step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19986step1 raw19986step0; decide +kernel
      have hl : raw19986step1Labels = raw19986step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19986step0 raw19986step0Labels permutation56 hz
    mixedMoment B raw19986step1 raw19986step1Labels = mixedMoment B raw19986step2 raw19986step2Labels := by
      have ha : raw19986step2 = (fun i j => raw19986step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19986step2 raw19986step1; decide +kernel
      have hl : raw19986step2Labels = raw19986step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19986step1 raw19986step1Labels permutation10 permutation2
    _ = mixedMoment B node4142 node4142Labels := by rfl

def raw19987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19987step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19987step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19987step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19987step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19987 raw19987Labels = mixedMoment B node4198 node4198Labels := by
  calc
    mixedMoment B raw19987 raw19987Labels = mixedMoment B raw19987step0 raw19987step0Labels := by
      have hz : ∀ j, raw19987 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19987step0 = (fun i j => raw19987 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19987step0 raw19987; decide +kernel
      have hl : raw19987step0Labels = raw19987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19987 raw19987Labels permutation346 hz
    mixedMoment B raw19987step0 raw19987step0Labels = mixedMoment B raw19987step1 raw19987step1Labels := by
      have ha : raw19987step1 = (fun i j => raw19987step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19987step1 raw19987step0; decide +kernel
      have hl : raw19987step1Labels = raw19987step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19987step0 raw19987step0Labels permutation145 permutation2
    mixedMoment B raw19987step1 raw19987step1Labels = mixedMoment B raw19987step2 raw19987step2Labels := by
      have ha : raw19987step2 = -raw19987step1 := by apply Matrix.ext; change ∀ i j, raw19987step2 i j = -(raw19987step1 i j); unfold raw19987step2 raw19987step1; decide +kernel
      have hl : raw19987step2Labels = raw19987step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4198 node4198Labels := by rfl

def raw19988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw19988step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19988step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19988step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19988 raw19988Labels = mixedMoment B node4198 node4198Labels := by
  calc
    mixedMoment B raw19988 raw19988Labels = mixedMoment B raw19988step0 raw19988step0Labels := by
      have hz : ∀ j, raw19988 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19988step0 = (fun i j => raw19988 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19988step0 raw19988; decide +kernel
      have hl : raw19988step0Labels = raw19988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19988 raw19988Labels permutation265 hz
    mixedMoment B raw19988step0 raw19988step0Labels = mixedMoment B raw19988step1 raw19988step1Labels := by
      have ha : raw19988step1 = (fun i j => raw19988step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19988step1 raw19988step0; decide +kernel
      have hl : raw19988step1Labels = raw19988step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19988step0 raw19988step0Labels permutation145 permutation2
    mixedMoment B raw19988step1 raw19988step1Labels = mixedMoment B raw19988step2 raw19988step2Labels := by
      have ha : raw19988step2 = -raw19988step1 := by apply Matrix.ext; change ∀ i j, raw19988step2 i j = -(raw19988step1 i j); unfold raw19988step2 raw19988step1; decide +kernel
      have hl : raw19988step2Labels = raw19988step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4198 node4198Labels := by rfl

def raw19989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw19989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw19989step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw19989step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19989step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-4, 1, 3]]
def raw19989step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19989step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![4, -1, -3]]
def raw19989step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19989 raw19989Labels = mixedMoment B node4222 node4222Labels := by
  calc
    mixedMoment B raw19989 raw19989Labels = mixedMoment B raw19989step0 raw19989step0Labels := by
      have hz : ∀ j, raw19989 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19989step0 = (fun i j => raw19989 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19989step0 raw19989; decide +kernel
      have hl : raw19989step0Labels = raw19989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19989 raw19989Labels permutation346 hz
    mixedMoment B raw19989step0 raw19989step0Labels = mixedMoment B raw19989step1 raw19989step1Labels := by
      have hz : ∀ j, raw19989step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19989step1 = (fun i j => raw19989step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19989step1 raw19989step0; decide +kernel
      have hl : raw19989step1Labels = raw19989step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19989step0 raw19989step0Labels permutation56 hz
    mixedMoment B raw19989step1 raw19989step1Labels = mixedMoment B raw19989step2 raw19989step2Labels := by
      have ha : raw19989step2 = (fun i j => raw19989step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19989step2 raw19989step1; decide +kernel
      have hl : raw19989step2Labels = raw19989step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19989step1 raw19989step1Labels permutation29 permutation2
    mixedMoment B raw19989step2 raw19989step2Labels = mixedMoment B raw19989step3 raw19989step3Labels := by
      have ha : raw19989step3 = -raw19989step2 := by apply Matrix.ext; change ∀ i j, raw19989step3 i j = -(raw19989step2 i j); unfold raw19989step3 raw19989step2; decide +kernel
      have hl : raw19989step3Labels = raw19989step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4222 node4222Labels := by rfl

def raw19990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 1, -4]]
def raw19990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 1, -4]]
def raw19990step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![3, 1, -4]]
def raw19990step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19990step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw19990step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19990 raw19990Labels = mixedMoment B node4421 node4421Labels := by
  calc
    mixedMoment B raw19990 raw19990Labels = mixedMoment B raw19990step0 raw19990step0Labels := by
      have hz : ∀ j, raw19990 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19990step0 = (fun i j => raw19990 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19990step0 raw19990; decide +kernel
      have hl : raw19990step0Labels = raw19990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19990 raw19990Labels permutation346 hz
    mixedMoment B raw19990step0 raw19990step0Labels = mixedMoment B raw19990step1 raw19990step1Labels := by
      have hz : ∀ j, raw19990step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19990step1 = (fun i j => raw19990step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19990step1 raw19990step0; decide +kernel
      have hl : raw19990step1Labels = raw19990step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19990step0 raw19990step0Labels permutation56 hz
    mixedMoment B raw19990step1 raw19990step1Labels = mixedMoment B raw19990step2 raw19990step2Labels := by
      have ha : raw19990step2 = (fun i j => raw19990step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19990step2 raw19990step1; decide +kernel
      have hl : raw19990step2Labels = raw19990step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19990step1 raw19990step1Labels permutation10 permutation2
    _ = mixedMoment B node4421 node4421Labels := by rfl

def raw19991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw19991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw19991step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19991step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw19991step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19991step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def raw19991step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19991 raw19991Labels = mixedMoment B node4168 node4168Labels := by
  calc
    mixedMoment B raw19991 raw19991Labels = mixedMoment B raw19991step0 raw19991step0Labels := by
      have hz : ∀ j, raw19991 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19991step0 = (fun i j => raw19991 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19991step0 raw19991; decide +kernel
      have hl : raw19991step0Labels = raw19991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19991 raw19991Labels permutation434 hz
    mixedMoment B raw19991step0 raw19991step0Labels = mixedMoment B raw19991step1 raw19991step1Labels := by
      have hz : ∀ j, raw19991step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19991step1 = (fun i j => raw19991step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19991step1 raw19991step0; decide +kernel
      have hl : raw19991step1Labels = raw19991step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19991step0 raw19991step0Labels permutation80 hz
    mixedMoment B raw19991step1 raw19991step1Labels = mixedMoment B raw19991step2 raw19991step2Labels := by
      have hz : ∀ j, raw19991step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19991step2 = (fun i j => raw19991step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19991step2 raw19991step1; decide +kernel
      have hl : raw19991step2Labels = raw19991step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19991step1 raw19991step1Labels permutation14 hz
    _ = mixedMoment B node4168 node4168Labels := by rfl

def raw19992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw19992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw19992step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19992step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw19992step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19992step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19992step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19992step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19992step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19992 raw19992Labels = mixedMoment B node4235 node4235Labels := by
  calc
    mixedMoment B raw19992 raw19992Labels = mixedMoment B raw19992step0 raw19992step0Labels := by
      have hz : ∀ j, raw19992 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19992step0 = (fun i j => raw19992 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19992step0 raw19992; decide +kernel
      have hl : raw19992step0Labels = raw19992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19992 raw19992Labels permutation434 hz
    mixedMoment B raw19992step0 raw19992step0Labels = mixedMoment B raw19992step1 raw19992step1Labels := by
      have hz : ∀ j, raw19992step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19992step1 = (fun i j => raw19992step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19992step1 raw19992step0; decide +kernel
      have hl : raw19992step1Labels = raw19992step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19992step0 raw19992step0Labels permutation80 hz
    mixedMoment B raw19992step1 raw19992step1Labels = mixedMoment B raw19992step2 raw19992step2Labels := by
      have ha : raw19992step2 = (fun i j => raw19992step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19992step2 raw19992step1; decide +kernel
      have hl : raw19992step2Labels = raw19992step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19992step1 raw19992step1Labels permutation31 permutation2
    mixedMoment B raw19992step2 raw19992step2Labels = mixedMoment B raw19992step3 raw19992step3Labels := by
      have ha : raw19992step3 = -raw19992step2 := by apply Matrix.ext; change ∀ i j, raw19992step3 i j = -(raw19992step2 i j); unfold raw19992step3 raw19992step2; decide +kernel
      have hl : raw19992step3Labels = raw19992step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4235 node4235Labels := by rfl

def raw19993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw19993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw19993step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw19993step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19993step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19993step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19993step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19993step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19993 raw19993Labels = mixedMoment B node4235 node4235Labels := by
  calc
    mixedMoment B raw19993 raw19993Labels = mixedMoment B raw19993step0 raw19993step0Labels := by
      have hz : ∀ j, raw19993 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19993step0 = (fun i j => raw19993 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19993step0 raw19993; decide +kernel
      have hl : raw19993step0Labels = raw19993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19993 raw19993Labels permutation434 hz
    mixedMoment B raw19993step0 raw19993step0Labels = mixedMoment B raw19993step1 raw19993step1Labels := by
      have hz : ∀ j, raw19993step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19993step1 = (fun i j => raw19993step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19993step1 raw19993step0; decide +kernel
      have hl : raw19993step1Labels = raw19993step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19993step0 raw19993step0Labels permutation56 hz
    mixedMoment B raw19993step1 raw19993step1Labels = mixedMoment B raw19993step2 raw19993step2Labels := by
      have ha : raw19993step2 = (fun i j => raw19993step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19993step2 raw19993step1; decide +kernel
      have hl : raw19993step2Labels = raw19993step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19993step1 raw19993step1Labels permutation31 permutation2
    mixedMoment B raw19993step2 raw19993step2Labels = mixedMoment B raw19993step3 raw19993step3Labels := by
      have ha : raw19993step3 = -raw19993step2 := by apply Matrix.ext; change ∀ i j, raw19993step3 i j = -(raw19993step2 i j); unfold raw19993step3 raw19993step2; decide +kernel
      have hl : raw19993step3Labels = raw19993step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4235 node4235Labels := by rfl

def raw19994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw19994Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw19994step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw19994step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19994step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19994step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19994step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19994step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19994 raw19994Labels = mixedMoment B node4235 node4235Labels := by
  calc
    mixedMoment B raw19994 raw19994Labels = mixedMoment B raw19994step0 raw19994step0Labels := by
      have hz : ∀ j, raw19994 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19994step0 = (fun i j => raw19994 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19994step0 raw19994; decide +kernel
      have hl : raw19994step0Labels = raw19994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19994 raw19994Labels permutation346 hz
    mixedMoment B raw19994step0 raw19994step0Labels = mixedMoment B raw19994step1 raw19994step1Labels := by
      have hz : ∀ j, raw19994step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19994step1 = (fun i j => raw19994step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19994step1 raw19994step0; decide +kernel
      have hl : raw19994step1Labels = raw19994step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19994step0 raw19994step0Labels permutation56 hz
    mixedMoment B raw19994step1 raw19994step1Labels = mixedMoment B raw19994step2 raw19994step2Labels := by
      have ha : raw19994step2 = (fun i j => raw19994step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19994step2 raw19994step1; decide +kernel
      have hl : raw19994step2Labels = raw19994step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19994step1 raw19994step1Labels permutation31 permutation2
    mixedMoment B raw19994step2 raw19994step2Labels = mixedMoment B raw19994step3 raw19994step3Labels := by
      have ha : raw19994step3 = -raw19994step2 := by apply Matrix.ext; change ∀ i j, raw19994step3 i j = -(raw19994step2 i j); unfold raw19994step3 raw19994step2; decide +kernel
      have hl : raw19994step3Labels = raw19994step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4235 node4235Labels := by rfl

def raw19995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 1, -4]]
def raw19995Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 1, -4]]
def raw19995step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19995step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![3, 1, -4]]
def raw19995step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19995step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw19995step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19995 raw19995Labels = mixedMoment B node4493 node4493Labels := by
  calc
    mixedMoment B raw19995 raw19995Labels = mixedMoment B raw19995step0 raw19995step0Labels := by
      have hz : ∀ j, raw19995 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19995step0 = (fun i j => raw19995 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19995step0 raw19995; decide +kernel
      have hl : raw19995step0Labels = raw19995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19995 raw19995Labels permutation434 hz
    mixedMoment B raw19995step0 raw19995step0Labels = mixedMoment B raw19995step1 raw19995step1Labels := by
      have hz : ∀ j, raw19995step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19995step1 = (fun i j => raw19995step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19995step1 raw19995step0; decide +kernel
      have hl : raw19995step1Labels = raw19995step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19995step0 raw19995step0Labels permutation80 hz
    mixedMoment B raw19995step1 raw19995step1Labels = mixedMoment B raw19995step2 raw19995step2Labels := by
      have hz : ∀ j, raw19995step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19995step2 = (fun i j => raw19995step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19995step2 raw19995step1; decide +kernel
      have hl : raw19995step2Labels = raw19995step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19995step1 raw19995step1Labels permutation14 hz
    _ = mixedMoment B node4493 node4493Labels := by rfl

def raw19996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw19996Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw19996step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19996step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw19996step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19996step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![5, -1, -4]]
def raw19996step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19996step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-5, 2, 3]]
def raw19996step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19996step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![5, -2, -3]]
def raw19996step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19996 raw19996Labels = mixedMoment B node4112 node4112Labels := by
  calc
    mixedMoment B raw19996 raw19996Labels = mixedMoment B raw19996step0 raw19996step0Labels := by
      have hz : ∀ j, raw19996 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19996step0 = (fun i j => raw19996 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19996step0 raw19996; decide +kernel
      have hl : raw19996step0Labels = raw19996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19996 raw19996Labels permutation434 hz
    mixedMoment B raw19996step0 raw19996step0Labels = mixedMoment B raw19996step1 raw19996step1Labels := by
      have hz : ∀ j, raw19996step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19996step1 = (fun i j => raw19996step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19996step1 raw19996step0; decide +kernel
      have hl : raw19996step1Labels = raw19996step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19996step0 raw19996step0Labels permutation80 hz
    mixedMoment B raw19996step1 raw19996step1Labels = mixedMoment B raw19996step2 raw19996step2Labels := by
      have hz : ∀ j, raw19996step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw19996step2 = (fun i j => raw19996step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw19996step2 raw19996step1; decide +kernel
      have hl : raw19996step2Labels = raw19996step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19996step1 raw19996step1Labels permutation14 hz
    mixedMoment B raw19996step2 raw19996step2Labels = mixedMoment B raw19996step3 raw19996step3Labels := by
      have ha : raw19996step3 = (fun i j => raw19996step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19996step3 raw19996step2; decide +kernel
      have hl : raw19996step3Labels = raw19996step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19996step2 raw19996step2Labels permutation7 permutation2
    mixedMoment B raw19996step3 raw19996step3Labels = mixedMoment B raw19996step4 raw19996step4Labels := by
      have ha : raw19996step4 = -raw19996step3 := by apply Matrix.ext; change ∀ i j, raw19996step4 i j = -(raw19996step3 i j); unfold raw19996step4 raw19996step3; decide +kernel
      have hl : raw19996step4Labels = raw19996step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4112 node4112Labels := by rfl

def raw19997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw19997Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw19997step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw19997step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19997step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19997step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19997step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19997 raw19997Labels = mixedMoment B node4103 node4103Labels := by
  calc
    mixedMoment B raw19997 raw19997Labels = mixedMoment B raw19997step0 raw19997step0Labels := by
      have hz : ∀ j, raw19997 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19997step0 = (fun i j => raw19997 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19997step0 raw19997; decide +kernel
      have hl : raw19997step0Labels = raw19997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19997 raw19997Labels permutation434 hz
    mixedMoment B raw19997step0 raw19997step0Labels = mixedMoment B raw19997step1 raw19997step1Labels := by
      have hz : ∀ j, raw19997step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19997step1 = (fun i j => raw19997step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19997step1 raw19997step0; decide +kernel
      have hl : raw19997step1Labels = raw19997step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19997step0 raw19997step0Labels permutation80 hz
    mixedMoment B raw19997step1 raw19997step1Labels = mixedMoment B raw19997step2 raw19997step2Labels := by
      have ha : raw19997step2 = (fun i j => raw19997step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19997step2 raw19997step1; decide +kernel
      have hl : raw19997step2Labels = raw19997step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19997step1 raw19997step1Labels permutation31 permutation2
    mixedMoment B raw19997step2 raw19997step2Labels = mixedMoment B raw19997step3 raw19997step3Labels := by
      have ha : raw19997step3 = -raw19997step2 := by apply Matrix.ext; change ∀ i j, raw19997step3 i j = -(raw19997step2 i j); unfold raw19997step3 raw19997step2; decide +kernel
      have hl : raw19997step3Labels = raw19997step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4103 node4103Labels := by rfl

def raw19998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw19998Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw19998step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw19998step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19998step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19998step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19998step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19998 raw19998Labels = mixedMoment B node4103 node4103Labels := by
  calc
    mixedMoment B raw19998 raw19998Labels = mixedMoment B raw19998step0 raw19998step0Labels := by
      have hz : ∀ j, raw19998 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19998step0 = (fun i j => raw19998 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19998step0 raw19998; decide +kernel
      have hl : raw19998step0Labels = raw19998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19998 raw19998Labels permutation434 hz
    mixedMoment B raw19998step0 raw19998step0Labels = mixedMoment B raw19998step1 raw19998step1Labels := by
      have hz : ∀ j, raw19998step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19998step1 = (fun i j => raw19998step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19998step1 raw19998step0; decide +kernel
      have hl : raw19998step1Labels = raw19998step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19998step0 raw19998step0Labels permutation56 hz
    mixedMoment B raw19998step1 raw19998step1Labels = mixedMoment B raw19998step2 raw19998step2Labels := by
      have ha : raw19998step2 = (fun i j => raw19998step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19998step2 raw19998step1; decide +kernel
      have hl : raw19998step2Labels = raw19998step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19998step1 raw19998step1Labels permutation31 permutation2
    mixedMoment B raw19998step2 raw19998step2Labels = mixedMoment B raw19998step3 raw19998step3Labels := by
      have ha : raw19998step3 = -raw19998step2 := by apply Matrix.ext; change ∀ i j, raw19998step3 i j = -(raw19998step2 i j); unfold raw19998step3 raw19998step2; decide +kernel
      have hl : raw19998step3Labels = raw19998step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4103 node4103Labels := by rfl

def raw19999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw19999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw19999step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19999step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw19999step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19999step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw19999step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19999step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw19999step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19999 raw19999Labels = mixedMoment B node4103 node4103Labels := by
  calc
    mixedMoment B raw19999 raw19999Labels = mixedMoment B raw19999step0 raw19999step0Labels := by
      have hz : ∀ j, raw19999 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19999step0 = (fun i j => raw19999 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19999step0 raw19999; decide +kernel
      have hl : raw19999step0Labels = raw19999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19999 raw19999Labels permutation346 hz
    mixedMoment B raw19999step0 raw19999step0Labels = mixedMoment B raw19999step1 raw19999step1Labels := by
      have hz : ∀ j, raw19999step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw19999step1 = (fun i j => raw19999step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw19999step1 raw19999step0; decide +kernel
      have hl : raw19999step1Labels = raw19999step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19999step0 raw19999step0Labels permutation56 hz
    mixedMoment B raw19999step1 raw19999step1Labels = mixedMoment B raw19999step2 raw19999step2Labels := by
      have ha : raw19999step2 = (fun i j => raw19999step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19999step2 raw19999step1; decide +kernel
      have hl : raw19999step2Labels = raw19999step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19999step1 raw19999step1Labels permutation31 permutation2
    mixedMoment B raw19999step2 raw19999step2Labels = mixedMoment B raw19999step3 raw19999step3Labels := by
      have ha : raw19999step3 = -raw19999step2 := by apply Matrix.ext; change ∀ i j, raw19999step3 i j = -(raw19999step2 i j); unfold raw19999step3 raw19999step2; decide +kernel
      have hl : raw19999step3Labels = raw19999step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4103 node4103Labels := by rfl

def raw20000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![5, -1, -4]]
def raw20000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![5, -1, -4]]
def raw20000step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20000step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![5, -1, -4]]
def raw20000step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20000step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![5, -1, -4]]
def raw20000step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20000step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 0, 1], ![-4, 1, 3]]
def raw20000step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20000step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![4, -1, -3]]
def raw20000step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20000 raw20000Labels = mixedMoment B node4131 node4131Labels := by
  calc
    mixedMoment B raw20000 raw20000Labels = mixedMoment B raw20000step0 raw20000step0Labels := by
      have hz : ∀ j, raw20000 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20000step0 = (fun i j => raw20000 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20000step0 raw20000; decide +kernel
      have hl : raw20000step0Labels = raw20000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20000 raw20000Labels permutation434 hz
    mixedMoment B raw20000step0 raw20000step0Labels = mixedMoment B raw20000step1 raw20000step1Labels := by
      have hz : ∀ j, raw20000step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20000step1 = (fun i j => raw20000step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20000step1 raw20000step0; decide +kernel
      have hl : raw20000step1Labels = raw20000step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20000step0 raw20000step0Labels permutation80 hz
    mixedMoment B raw20000step1 raw20000step1Labels = mixedMoment B raw20000step2 raw20000step2Labels := by
      have hz : ∀ j, raw20000step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20000step2 = (fun i j => raw20000step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20000step2 raw20000step1; decide +kernel
      have hl : raw20000step2Labels = raw20000step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20000step1 raw20000step1Labels permutation14 hz
    mixedMoment B raw20000step2 raw20000step2Labels = mixedMoment B raw20000step3 raw20000step3Labels := by
      have ha : raw20000step3 = (fun i j => raw20000step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20000step3 raw20000step2; decide +kernel
      have hl : raw20000step3Labels = raw20000step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20000step2 raw20000step2Labels permutation7 permutation2
    mixedMoment B raw20000step3 raw20000step3Labels = mixedMoment B raw20000step4 raw20000step4Labels := by
      have ha : raw20000step4 = -raw20000step3 := by apply Matrix.ext; change ∀ i j, raw20000step4 i j = -(raw20000step3 i j); unfold raw20000step4 raw20000step3; decide +kernel
      have hl : raw20000step4Labels = raw20000step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4131 node4131Labels := by rfl

def raw20001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20001step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20001step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20001step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20001step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20001step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20001 raw20001Labels = mixedMoment B node809 node809Labels := by
  calc
    mixedMoment B raw20001 raw20001Labels = mixedMoment B raw20001step0 raw20001step0Labels := by
      have hz : ∀ j, raw20001 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20001step0 = (fun i j => raw20001 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20001step0 raw20001; decide +kernel
      have hl : raw20001step0Labels = raw20001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20001 raw20001Labels permutation434 hz
    mixedMoment B raw20001step0 raw20001step0Labels = mixedMoment B raw20001step1 raw20001step1Labels := by
      have hz : ∀ j, raw20001step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20001step1 = (fun i j => raw20001step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20001step1 raw20001step0; decide +kernel
      have hl : raw20001step1Labels = raw20001step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20001step0 raw20001step0Labels permutation80 hz
    mixedMoment B raw20001step1 raw20001step1Labels = mixedMoment B raw20001step2 raw20001step2Labels := by
      have ha : raw20001step2 = (fun i j => raw20001step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20001step2 raw20001step1; decide +kernel
      have hl : raw20001step2Labels = raw20001step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20001step1 raw20001step1Labels permutation29 permutation7
    mixedMoment B raw20001step2 raw20001step2Labels = mixedMoment B raw20001step3 raw20001step3Labels := by
      have ha : raw20001step3 = raw20001step2 := by apply Matrix.ext; unfold raw20001step3 raw20001step2; decide +kernel
      have hl : raw20001step2Labels = labelEmbedding1 ∘ raw20001step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20001step2 raw20001step2Labels raw20001step3Labels labelEmbedding1 hl
    _ = mixedMoment B node809 node809Labels := by rfl

def raw20002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20002Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20002step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20002step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20002step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20002step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20002step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20002step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20002 raw20002Labels = mixedMoment B node809 node809Labels := by
  calc
    mixedMoment B raw20002 raw20002Labels = mixedMoment B raw20002step0 raw20002step0Labels := by
      have hz : ∀ j, raw20002 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20002step0 = (fun i j => raw20002 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20002step0 raw20002; decide +kernel
      have hl : raw20002step0Labels = raw20002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20002 raw20002Labels permutation434 hz
    mixedMoment B raw20002step0 raw20002step0Labels = mixedMoment B raw20002step1 raw20002step1Labels := by
      have hz : ∀ j, raw20002step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20002step1 = (fun i j => raw20002step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20002step1 raw20002step0; decide +kernel
      have hl : raw20002step1Labels = raw20002step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20002step0 raw20002step0Labels permutation56 hz
    mixedMoment B raw20002step1 raw20002step1Labels = mixedMoment B raw20002step2 raw20002step2Labels := by
      have ha : raw20002step2 = (fun i j => raw20002step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20002step2 raw20002step1; decide +kernel
      have hl : raw20002step2Labels = raw20002step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20002step1 raw20002step1Labels permutation29 permutation7
    mixedMoment B raw20002step2 raw20002step2Labels = mixedMoment B raw20002step3 raw20002step3Labels := by
      have ha : raw20002step3 = raw20002step2 := by apply Matrix.ext; unfold raw20002step3 raw20002step2; decide +kernel
      have hl : raw20002step2Labels = labelEmbedding1 ∘ raw20002step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20002step2 raw20002step2Labels raw20002step3Labels labelEmbedding1 hl
    _ = mixedMoment B node809 node809Labels := by rfl

def raw20003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20003Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20003step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20003step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20003step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20003step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20003step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20003step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20003step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20003 raw20003Labels = mixedMoment B node809 node809Labels := by
  calc
    mixedMoment B raw20003 raw20003Labels = mixedMoment B raw20003step0 raw20003step0Labels := by
      have hz : ∀ j, raw20003 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20003step0 = (fun i j => raw20003 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20003step0 raw20003; decide +kernel
      have hl : raw20003step0Labels = raw20003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20003 raw20003Labels permutation346 hz
    mixedMoment B raw20003step0 raw20003step0Labels = mixedMoment B raw20003step1 raw20003step1Labels := by
      have hz : ∀ j, raw20003step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20003step1 = (fun i j => raw20003step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20003step1 raw20003step0; decide +kernel
      have hl : raw20003step1Labels = raw20003step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20003step0 raw20003step0Labels permutation56 hz
    mixedMoment B raw20003step1 raw20003step1Labels = mixedMoment B raw20003step2 raw20003step2Labels := by
      have ha : raw20003step2 = (fun i j => raw20003step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20003step2 raw20003step1; decide +kernel
      have hl : raw20003step2Labels = raw20003step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20003step1 raw20003step1Labels permutation29 permutation7
    mixedMoment B raw20003step2 raw20003step2Labels = mixedMoment B raw20003step3 raw20003step3Labels := by
      have ha : raw20003step3 = raw20003step2 := by apply Matrix.ext; unfold raw20003step3 raw20003step2; decide +kernel
      have hl : raw20003step2Labels = labelEmbedding1 ∘ raw20003step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20003step2 raw20003step2Labels raw20003step3Labels labelEmbedding1 hl
    _ = mixedMoment B node809 node809Labels := by rfl

def raw20004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20004Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20004step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20004step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20004step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20004step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![4, 0, -4]]
def raw20004step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20004step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![4, -4]]
def raw20004step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20004step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-3, 3]]
def raw20004step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20004step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw20004step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20004 raw20004Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw20004 raw20004Labels = mixedMoment B raw20004step0 raw20004step0Labels := by
      have hz : ∀ j, raw20004 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20004step0 = (fun i j => raw20004 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20004step0 raw20004; decide +kernel
      have hl : raw20004step0Labels = raw20004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20004 raw20004Labels permutation434 hz
    mixedMoment B raw20004step0 raw20004step0Labels = mixedMoment B raw20004step1 raw20004step1Labels := by
      have hz : ∀ j, raw20004step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20004step1 = (fun i j => raw20004step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20004step1 raw20004step0; decide +kernel
      have hl : raw20004step1Labels = raw20004step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20004step0 raw20004step0Labels permutation80 hz
    mixedMoment B raw20004step1 raw20004step1Labels = mixedMoment B raw20004step2 raw20004step2Labels := by
      have hz : ∀ j, raw20004step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20004step2 = (fun i j => raw20004step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20004step2 raw20004step1; decide +kernel
      have hl : raw20004step2Labels = raw20004step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20004step1 raw20004step1Labels permutation14 hz
    mixedMoment B raw20004step2 raw20004step2Labels = mixedMoment B raw20004step3 raw20004step3Labels := by
      have hz : ∀ i, raw20004step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw20004step3 = (fun i j => raw20004step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw20004step3 raw20004step2; decide +kernel
      have hl : raw20004step3Labels = (fun j => raw20004step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20004step2 raw20004step2Labels permutation4 hz
    mixedMoment B raw20004step3 raw20004step3Labels = mixedMoment B raw20004step4 raw20004step4Labels := by
      have ha : raw20004step4 = (fun i j => raw20004step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20004step4 raw20004step3; decide +kernel
      have hl : raw20004step4Labels = raw20004step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20004step3 raw20004step3Labels permutation7 permutation0
    mixedMoment B raw20004step4 raw20004step4Labels = mixedMoment B raw20004step5 raw20004step5Labels := by
      have ha : raw20004step5 = -raw20004step4 := by apply Matrix.ext; change ∀ i j, raw20004step5 i j = -(raw20004step4 i j); unfold raw20004step5 raw20004step4; decide +kernel
      have hl : raw20004step5Labels = raw20004step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

def raw20005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20005Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20005step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20005step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20005step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20005step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![3, 1, -4]]
def raw20005step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20005step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw20005step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20005step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw20005step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20005 raw20005Labels = mixedMoment B node1085 node1085Labels := by
  calc
    mixedMoment B raw20005 raw20005Labels = mixedMoment B raw20005step0 raw20005step0Labels := by
      have hz : ∀ j, raw20005 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20005step0 = (fun i j => raw20005 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20005step0 raw20005; decide +kernel
      have hl : raw20005step0Labels = raw20005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20005 raw20005Labels permutation434 hz
    mixedMoment B raw20005step0 raw20005step0Labels = mixedMoment B raw20005step1 raw20005step1Labels := by
      have hz : ∀ j, raw20005step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20005step1 = (fun i j => raw20005step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20005step1 raw20005step0; decide +kernel
      have hl : raw20005step1Labels = raw20005step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20005step0 raw20005step0Labels permutation80 hz
    mixedMoment B raw20005step1 raw20005step1Labels = mixedMoment B raw20005step2 raw20005step2Labels := by
      have hz : ∀ j, raw20005step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20005step2 = (fun i j => raw20005step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20005step2 raw20005step1; decide +kernel
      have hl : raw20005step2Labels = raw20005step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20005step1 raw20005step1Labels permutation14 hz
    mixedMoment B raw20005step2 raw20005step2Labels = mixedMoment B raw20005step3 raw20005step3Labels := by
      have ha : raw20005step3 = (fun i j => raw20005step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20005step3 raw20005step2; decide +kernel
      have hl : raw20005step3Labels = raw20005step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20005step2 raw20005step2Labels permutation7 permutation7
    mixedMoment B raw20005step3 raw20005step3Labels = mixedMoment B raw20005step4 raw20005step4Labels := by
      have ha : raw20005step4 = raw20005step3 := by apply Matrix.ext; unfold raw20005step4 raw20005step3; decide +kernel
      have hl : raw20005step3Labels = labelEmbedding1 ∘ raw20005step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20005step3 raw20005step3Labels raw20005step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1085 node1085Labels := by rfl

def raw20006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20006Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20006step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20006step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20006step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20006step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![3, 2, -5]]
def raw20006step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20006step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![3, 2, -5]]
def raw20006step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20006 raw20006Labels = mixedMoment B node765 node765Labels := by
  calc
    mixedMoment B raw20006 raw20006Labels = mixedMoment B raw20006step0 raw20006step0Labels := by
      have hz : ∀ j, raw20006 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20006step0 = (fun i j => raw20006 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20006step0 raw20006; decide +kernel
      have hl : raw20006step0Labels = raw20006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20006 raw20006Labels permutation434 hz
    mixedMoment B raw20006step0 raw20006step0Labels = mixedMoment B raw20006step1 raw20006step1Labels := by
      have hz : ∀ j, raw20006step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20006step1 = (fun i j => raw20006step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20006step1 raw20006step0; decide +kernel
      have hl : raw20006step1Labels = raw20006step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20006step0 raw20006step0Labels permutation80 hz
    mixedMoment B raw20006step1 raw20006step1Labels = mixedMoment B raw20006step2 raw20006step2Labels := by
      have ha : raw20006step2 = (fun i j => raw20006step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20006step2 raw20006step1; decide +kernel
      have hl : raw20006step2Labels = raw20006step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20006step1 raw20006step1Labels permutation29 permutation7
    mixedMoment B raw20006step2 raw20006step2Labels = mixedMoment B raw20006step3 raw20006step3Labels := by
      have ha : raw20006step3 = raw20006step2 := by apply Matrix.ext; unfold raw20006step3 raw20006step2; decide +kernel
      have hl : raw20006step2Labels = labelEmbedding1 ∘ raw20006step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20006step2 raw20006step2Labels raw20006step3Labels labelEmbedding1 hl
    _ = mixedMoment B node765 node765Labels := by rfl

def raw20007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20007Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20007step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20007step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20007step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20007 raw20007Labels = mixedMoment B node750 node750Labels := by
  calc
    mixedMoment B raw20007 raw20007Labels = mixedMoment B raw20007step0 raw20007step0Labels := by
      have hz : ∀ j, raw20007 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20007step0 = (fun i j => raw20007 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20007step0 raw20007; decide +kernel
      have hl : raw20007step0Labels = raw20007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20007 raw20007Labels permutation434 hz
    mixedMoment B raw20007step0 raw20007step0Labels = mixedMoment B raw20007step1 raw20007step1Labels := by
      have ha : raw20007step1 = (fun i j => raw20007step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20007step1 raw20007step0; decide +kernel
      have hl : raw20007step1Labels = raw20007step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20007step0 raw20007step0Labels permutation137 permutation7
    mixedMoment B raw20007step1 raw20007step1Labels = mixedMoment B raw20007step2 raw20007step2Labels := by
      have ha : raw20007step2 = raw20007step1 := by apply Matrix.ext; unfold raw20007step2 raw20007step1; decide +kernel
      have hl : raw20007step1Labels = labelEmbedding1 ∘ raw20007step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20007step1 raw20007step1Labels raw20007step2Labels labelEmbedding1 hl
    _ = mixedMoment B node750 node750Labels := by rfl

def raw20008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20008Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20008step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20008step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20008step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20008step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20008step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20008 raw20008Labels = mixedMoment B node750 node750Labels := by
  calc
    mixedMoment B raw20008 raw20008Labels = mixedMoment B raw20008step0 raw20008step0Labels := by
      have hz : ∀ j, raw20008 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20008step0 = (fun i j => raw20008 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20008step0 raw20008; decide +kernel
      have hl : raw20008step0Labels = raw20008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20008 raw20008Labels permutation346 hz
    mixedMoment B raw20008step0 raw20008step0Labels = mixedMoment B raw20008step1 raw20008step1Labels := by
      have ha : raw20008step1 = (fun i j => raw20008step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20008step1 raw20008step0; decide +kernel
      have hl : raw20008step1Labels = raw20008step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20008step0 raw20008step0Labels permutation137 permutation7
    mixedMoment B raw20008step1 raw20008step1Labels = mixedMoment B raw20008step2 raw20008step2Labels := by
      have ha : raw20008step2 = raw20008step1 := by apply Matrix.ext; unfold raw20008step2 raw20008step1; decide +kernel
      have hl : raw20008step1Labels = labelEmbedding1 ∘ raw20008step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20008step1 raw20008step1Labels raw20008step2Labels labelEmbedding1 hl
    _ = mixedMoment B node750 node750Labels := by rfl

def raw20009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20009Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20009step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20009step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20009step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20009step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![3, 1, -4]]
def raw20009step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20009step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![3, 1, -4]]
def raw20009step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20009 raw20009Labels = mixedMoment B node770 node770Labels := by
  calc
    mixedMoment B raw20009 raw20009Labels = mixedMoment B raw20009step0 raw20009step0Labels := by
      have hz : ∀ j, raw20009 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20009step0 = (fun i j => raw20009 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20009step0 raw20009; decide +kernel
      have hl : raw20009step0Labels = raw20009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20009 raw20009Labels permutation434 hz
    mixedMoment B raw20009step0 raw20009step0Labels = mixedMoment B raw20009step1 raw20009step1Labels := by
      have hz : ∀ j, raw20009step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20009step1 = (fun i j => raw20009step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20009step1 raw20009step0; decide +kernel
      have hl : raw20009step1Labels = raw20009step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20009step0 raw20009step0Labels permutation80 hz
    mixedMoment B raw20009step1 raw20009step1Labels = mixedMoment B raw20009step2 raw20009step2Labels := by
      have ha : raw20009step2 = (fun i j => raw20009step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20009step2 raw20009step1; decide +kernel
      have hl : raw20009step2Labels = raw20009step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20009step1 raw20009step1Labels permutation29 permutation7
    mixedMoment B raw20009step2 raw20009step2Labels = mixedMoment B raw20009step3 raw20009step3Labels := by
      have ha : raw20009step3 = raw20009step2 := by apply Matrix.ext; unfold raw20009step3 raw20009step2; decide +kernel
      have hl : raw20009step2Labels = labelEmbedding1 ∘ raw20009step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20009step2 raw20009step2Labels raw20009step3Labels labelEmbedding1 hl
    _ = mixedMoment B node770 node770Labels := by rfl

def raw20010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20010Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20010step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20010step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20010step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20010step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw20010step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20010step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw20010step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20010 raw20010Labels = mixedMoment B node1002 node1002Labels := by
  calc
    mixedMoment B raw20010 raw20010Labels = mixedMoment B raw20010step0 raw20010step0Labels := by
      have hz : ∀ j, raw20010 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20010step0 = (fun i j => raw20010 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20010step0 raw20010; decide +kernel
      have hl : raw20010step0Labels = raw20010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20010 raw20010Labels permutation434 hz
    mixedMoment B raw20010step0 raw20010step0Labels = mixedMoment B raw20010step1 raw20010step1Labels := by
      have hz : ∀ j, raw20010step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20010step1 = (fun i j => raw20010step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20010step1 raw20010step0; decide +kernel
      have hl : raw20010step1Labels = raw20010step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20010step0 raw20010step0Labels permutation80 hz
    mixedMoment B raw20010step1 raw20010step1Labels = mixedMoment B raw20010step2 raw20010step2Labels := by
      have ha : raw20010step2 = (fun i j => raw20010step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20010step2 raw20010step1; decide +kernel
      have hl : raw20010step2Labels = raw20010step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20010step1 raw20010step1Labels permutation29 permutation7
    mixedMoment B raw20010step2 raw20010step2Labels = mixedMoment B raw20010step3 raw20010step3Labels := by
      have ha : raw20010step3 = raw20010step2 := by apply Matrix.ext; unfold raw20010step3 raw20010step2; decide +kernel
      have hl : raw20010step2Labels = labelEmbedding1 ∘ raw20010step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20010step2 raw20010step2Labels raw20010step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1002 node1002Labels := by rfl

def raw20011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20011Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20011step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20011step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20011step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20011step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![3, 2, -5]]
def raw20011step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20011step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![3, 2, -5]]
def raw20011step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20011 raw20011Labels = mixedMoment B node765 node765Labels := by
  calc
    mixedMoment B raw20011 raw20011Labels = mixedMoment B raw20011step0 raw20011step0Labels := by
      have hz : ∀ j, raw20011 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20011step0 = (fun i j => raw20011 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20011step0 raw20011; decide +kernel
      have hl : raw20011step0Labels = raw20011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20011 raw20011Labels permutation434 hz
    mixedMoment B raw20011step0 raw20011step0Labels = mixedMoment B raw20011step1 raw20011step1Labels := by
      have hz : ∀ j, raw20011step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20011step1 = (fun i j => raw20011step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20011step1 raw20011step0; decide +kernel
      have hl : raw20011step1Labels = raw20011step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20011step0 raw20011step0Labels permutation56 hz
    mixedMoment B raw20011step1 raw20011step1Labels = mixedMoment B raw20011step2 raw20011step2Labels := by
      have ha : raw20011step2 = (fun i j => raw20011step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20011step2 raw20011step1; decide +kernel
      have hl : raw20011step2Labels = raw20011step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20011step1 raw20011step1Labels permutation29 permutation7
    mixedMoment B raw20011step2 raw20011step2Labels = mixedMoment B raw20011step3 raw20011step3Labels := by
      have ha : raw20011step3 = raw20011step2 := by apply Matrix.ext; unfold raw20011step3 raw20011step2; decide +kernel
      have hl : raw20011step2Labels = labelEmbedding1 ∘ raw20011step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20011step2 raw20011step2Labels raw20011step3Labels labelEmbedding1 hl
    _ = mixedMoment B node765 node765Labels := by rfl

def raw20012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20012Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20012step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20012step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20012step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20012step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20012 raw20012Labels = mixedMoment B node750 node750Labels := by
  calc
    mixedMoment B raw20012 raw20012Labels = mixedMoment B raw20012step0 raw20012step0Labels := by
      have hz : ∀ j, raw20012 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20012step0 = (fun i j => raw20012 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20012step0 raw20012; decide +kernel
      have hl : raw20012step0Labels = raw20012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20012 raw20012Labels permutation434 hz
    mixedMoment B raw20012step0 raw20012step0Labels = mixedMoment B raw20012step1 raw20012step1Labels := by
      have ha : raw20012step1 = (fun i j => raw20012step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20012step1 raw20012step0; decide +kernel
      have hl : raw20012step1Labels = raw20012step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20012step0 raw20012step0Labels permutation143 permutation7
    mixedMoment B raw20012step1 raw20012step1Labels = mixedMoment B raw20012step2 raw20012step2Labels := by
      have ha : raw20012step2 = raw20012step1 := by apply Matrix.ext; unfold raw20012step2 raw20012step1; decide +kernel
      have hl : raw20012step1Labels = labelEmbedding1 ∘ raw20012step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20012step1 raw20012step1Labels raw20012step2Labels labelEmbedding1 hl
    _ = mixedMoment B node750 node750Labels := by rfl

def raw20013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20013Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20013step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20013step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20013step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20013step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20013 raw20013Labels = mixedMoment B node750 node750Labels := by
  calc
    mixedMoment B raw20013 raw20013Labels = mixedMoment B raw20013step0 raw20013step0Labels := by
      have hz : ∀ j, raw20013 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20013step0 = (fun i j => raw20013 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20013step0 raw20013; decide +kernel
      have hl : raw20013step0Labels = raw20013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20013 raw20013Labels permutation265 hz
    mixedMoment B raw20013step0 raw20013step0Labels = mixedMoment B raw20013step1 raw20013step1Labels := by
      have ha : raw20013step1 = (fun i j => raw20013step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20013step1 raw20013step0; decide +kernel
      have hl : raw20013step1Labels = raw20013step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20013step0 raw20013step0Labels permutation137 permutation7
    mixedMoment B raw20013step1 raw20013step1Labels = mixedMoment B raw20013step2 raw20013step2Labels := by
      have ha : raw20013step2 = raw20013step1 := by apply Matrix.ext; unfold raw20013step2 raw20013step1; decide +kernel
      have hl : raw20013step1Labels = labelEmbedding1 ∘ raw20013step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20013step1 raw20013step1Labels raw20013step2Labels labelEmbedding1 hl
    _ = mixedMoment B node750 node750Labels := by rfl

def raw20014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20014Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20014step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20014step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20014step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20014step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![3, 1, -4]]
def raw20014step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20014step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![3, 1, -4]]
def raw20014step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20014 raw20014Labels = mixedMoment B node770 node770Labels := by
  calc
    mixedMoment B raw20014 raw20014Labels = mixedMoment B raw20014step0 raw20014step0Labels := by
      have hz : ∀ j, raw20014 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20014step0 = (fun i j => raw20014 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20014step0 raw20014; decide +kernel
      have hl : raw20014step0Labels = raw20014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20014 raw20014Labels permutation434 hz
    mixedMoment B raw20014step0 raw20014step0Labels = mixedMoment B raw20014step1 raw20014step1Labels := by
      have hz : ∀ j, raw20014step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20014step1 = (fun i j => raw20014step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20014step1 raw20014step0; decide +kernel
      have hl : raw20014step1Labels = raw20014step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20014step0 raw20014step0Labels permutation56 hz
    mixedMoment B raw20014step1 raw20014step1Labels = mixedMoment B raw20014step2 raw20014step2Labels := by
      have ha : raw20014step2 = (fun i j => raw20014step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20014step2 raw20014step1; decide +kernel
      have hl : raw20014step2Labels = raw20014step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20014step1 raw20014step1Labels permutation29 permutation7
    mixedMoment B raw20014step2 raw20014step2Labels = mixedMoment B raw20014step3 raw20014step3Labels := by
      have ha : raw20014step3 = raw20014step2 := by apply Matrix.ext; unfold raw20014step3 raw20014step2; decide +kernel
      have hl : raw20014step2Labels = labelEmbedding1 ∘ raw20014step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20014step2 raw20014step2Labels raw20014step3Labels labelEmbedding1 hl
    _ = mixedMoment B node770 node770Labels := by rfl

def raw20015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20015Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20015step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20015step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20015step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20015step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw20015step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20015step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw20015step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20015 raw20015Labels = mixedMoment B node1002 node1002Labels := by
  calc
    mixedMoment B raw20015 raw20015Labels = mixedMoment B raw20015step0 raw20015step0Labels := by
      have hz : ∀ j, raw20015 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20015step0 = (fun i j => raw20015 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20015step0 raw20015; decide +kernel
      have hl : raw20015step0Labels = raw20015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20015 raw20015Labels permutation434 hz
    mixedMoment B raw20015step0 raw20015step0Labels = mixedMoment B raw20015step1 raw20015step1Labels := by
      have hz : ∀ j, raw20015step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20015step1 = (fun i j => raw20015step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20015step1 raw20015step0; decide +kernel
      have hl : raw20015step1Labels = raw20015step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20015step0 raw20015step0Labels permutation56 hz
    mixedMoment B raw20015step1 raw20015step1Labels = mixedMoment B raw20015step2 raw20015step2Labels := by
      have ha : raw20015step2 = (fun i j => raw20015step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20015step2 raw20015step1; decide +kernel
      have hl : raw20015step2Labels = raw20015step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20015step1 raw20015step1Labels permutation29 permutation7
    mixedMoment B raw20015step2 raw20015step2Labels = mixedMoment B raw20015step3 raw20015step3Labels := by
      have ha : raw20015step3 = raw20015step2 := by apply Matrix.ext; unfold raw20015step3 raw20015step2; decide +kernel
      have hl : raw20015step2Labels = labelEmbedding1 ∘ raw20015step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20015step2 raw20015step2Labels raw20015step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1002 node1002Labels := by rfl

def raw20016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20016Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20016step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20016step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20016step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![3, 2, -5]]
def raw20016step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20016step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![3, 2, -5]]
def raw20016step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20016 raw20016Labels = mixedMoment B node765 node765Labels := by
  calc
    mixedMoment B raw20016 raw20016Labels = mixedMoment B raw20016step0 raw20016step0Labels := by
      have hz : ∀ j, raw20016 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20016step0 = (fun i j => raw20016 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20016step0 raw20016; decide +kernel
      have hl : raw20016step0Labels = raw20016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20016 raw20016Labels permutation346 hz
    mixedMoment B raw20016step0 raw20016step0Labels = mixedMoment B raw20016step1 raw20016step1Labels := by
      have hz : ∀ j, raw20016step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20016step1 = (fun i j => raw20016step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20016step1 raw20016step0; decide +kernel
      have hl : raw20016step1Labels = raw20016step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20016step0 raw20016step0Labels permutation56 hz
    mixedMoment B raw20016step1 raw20016step1Labels = mixedMoment B raw20016step2 raw20016step2Labels := by
      have ha : raw20016step2 = (fun i j => raw20016step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20016step2 raw20016step1; decide +kernel
      have hl : raw20016step2Labels = raw20016step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20016step1 raw20016step1Labels permutation29 permutation7
    mixedMoment B raw20016step2 raw20016step2Labels = mixedMoment B raw20016step3 raw20016step3Labels := by
      have ha : raw20016step3 = raw20016step2 := by apply Matrix.ext; unfold raw20016step3 raw20016step2; decide +kernel
      have hl : raw20016step2Labels = labelEmbedding1 ∘ raw20016step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20016step2 raw20016step2Labels raw20016step3Labels labelEmbedding1 hl
    _ = mixedMoment B node765 node765Labels := by rfl

def raw20017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20017Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20017step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20017step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20017step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20017 raw20017Labels = mixedMoment B node750 node750Labels := by
  calc
    mixedMoment B raw20017 raw20017Labels = mixedMoment B raw20017step0 raw20017step0Labels := by
      have hz : ∀ j, raw20017 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20017step0 = (fun i j => raw20017 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20017step0 raw20017; decide +kernel
      have hl : raw20017step0Labels = raw20017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20017 raw20017Labels permutation346 hz
    mixedMoment B raw20017step0 raw20017step0Labels = mixedMoment B raw20017step1 raw20017step1Labels := by
      have ha : raw20017step1 = (fun i j => raw20017step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20017step1 raw20017step0; decide +kernel
      have hl : raw20017step1Labels = raw20017step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20017step0 raw20017step0Labels permutation143 permutation7
    mixedMoment B raw20017step1 raw20017step1Labels = mixedMoment B raw20017step2 raw20017step2Labels := by
      have ha : raw20017step2 = raw20017step1 := by apply Matrix.ext; unfold raw20017step2 raw20017step1; decide +kernel
      have hl : raw20017step1Labels = labelEmbedding1 ∘ raw20017step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20017step1 raw20017step1Labels raw20017step2Labels labelEmbedding1 hl
    _ = mixedMoment B node750 node750Labels := by rfl

def raw20018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20018Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20018step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20018step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20018step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20018 raw20018Labels = mixedMoment B node750 node750Labels := by
  calc
    mixedMoment B raw20018 raw20018Labels = mixedMoment B raw20018step0 raw20018step0Labels := by
      have hz : ∀ j, raw20018 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20018step0 = (fun i j => raw20018 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20018step0 raw20018; decide +kernel
      have hl : raw20018step0Labels = raw20018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20018 raw20018Labels permutation265 hz
    mixedMoment B raw20018step0 raw20018step0Labels = mixedMoment B raw20018step1 raw20018step1Labels := by
      have ha : raw20018step1 = (fun i j => raw20018step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20018step1 raw20018step0; decide +kernel
      have hl : raw20018step1Labels = raw20018step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20018step0 raw20018step0Labels permutation143 permutation7
    mixedMoment B raw20018step1 raw20018step1Labels = mixedMoment B raw20018step2 raw20018step2Labels := by
      have ha : raw20018step2 = raw20018step1 := by apply Matrix.ext; unfold raw20018step2 raw20018step1; decide +kernel
      have hl : raw20018step1Labels = labelEmbedding1 ∘ raw20018step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20018step1 raw20018step1Labels raw20018step2Labels labelEmbedding1 hl
    _ = mixedMoment B node750 node750Labels := by rfl

def raw20019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20019Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20019step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20019step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20019step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20019step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![3, 1, -4]]
def raw20019step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20019step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![3, 1, -4]]
def raw20019step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20019 raw20019Labels = mixedMoment B node770 node770Labels := by
  calc
    mixedMoment B raw20019 raw20019Labels = mixedMoment B raw20019step0 raw20019step0Labels := by
      have hz : ∀ j, raw20019 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20019step0 = (fun i j => raw20019 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20019step0 raw20019; decide +kernel
      have hl : raw20019step0Labels = raw20019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20019 raw20019Labels permutation346 hz
    mixedMoment B raw20019step0 raw20019step0Labels = mixedMoment B raw20019step1 raw20019step1Labels := by
      have hz : ∀ j, raw20019step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20019step1 = (fun i j => raw20019step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20019step1 raw20019step0; decide +kernel
      have hl : raw20019step1Labels = raw20019step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20019step0 raw20019step0Labels permutation56 hz
    mixedMoment B raw20019step1 raw20019step1Labels = mixedMoment B raw20019step2 raw20019step2Labels := by
      have ha : raw20019step2 = (fun i j => raw20019step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20019step2 raw20019step1; decide +kernel
      have hl : raw20019step2Labels = raw20019step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20019step1 raw20019step1Labels permutation29 permutation7
    mixedMoment B raw20019step2 raw20019step2Labels = mixedMoment B raw20019step3 raw20019step3Labels := by
      have ha : raw20019step3 = raw20019step2 := by apply Matrix.ext; unfold raw20019step3 raw20019step2; decide +kernel
      have hl : raw20019step2Labels = labelEmbedding1 ∘ raw20019step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20019step2 raw20019step2Labels raw20019step3Labels labelEmbedding1 hl
    _ = mixedMoment B node770 node770Labels := by rfl

def raw20020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20020Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20020step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20020step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20020step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20020step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw20020step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20020step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw20020step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20020 raw20020Labels = mixedMoment B node1002 node1002Labels := by
  calc
    mixedMoment B raw20020 raw20020Labels = mixedMoment B raw20020step0 raw20020step0Labels := by
      have hz : ∀ j, raw20020 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20020step0 = (fun i j => raw20020 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20020step0 raw20020; decide +kernel
      have hl : raw20020step0Labels = raw20020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20020 raw20020Labels permutation346 hz
    mixedMoment B raw20020step0 raw20020step0Labels = mixedMoment B raw20020step1 raw20020step1Labels := by
      have hz : ∀ j, raw20020step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20020step1 = (fun i j => raw20020step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20020step1 raw20020step0; decide +kernel
      have hl : raw20020step1Labels = raw20020step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20020step0 raw20020step0Labels permutation56 hz
    mixedMoment B raw20020step1 raw20020step1Labels = mixedMoment B raw20020step2 raw20020step2Labels := by
      have ha : raw20020step2 = (fun i j => raw20020step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20020step2 raw20020step1; decide +kernel
      have hl : raw20020step2Labels = raw20020step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20020step1 raw20020step1Labels permutation29 permutation7
    mixedMoment B raw20020step2 raw20020step2Labels = mixedMoment B raw20020step3 raw20020step3Labels := by
      have ha : raw20020step3 = raw20020step2 := by apply Matrix.ext; unfold raw20020step3 raw20020step2; decide +kernel
      have hl : raw20020step2Labels = labelEmbedding1 ∘ raw20020step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20020step2 raw20020step2Labels raw20020step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1002 node1002Labels := by rfl

def raw20021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20021Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20021step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20021step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20021step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20021step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def raw20021step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20021step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![3, 2, -5]]
def raw20021step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20021step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![3, 2, -5]]
def raw20021step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20021 raw20021Labels = mixedMoment B node845 node845Labels := by
  calc
    mixedMoment B raw20021 raw20021Labels = mixedMoment B raw20021step0 raw20021step0Labels := by
      have hz : ∀ j, raw20021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20021step0 = (fun i j => raw20021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20021step0 raw20021; decide +kernel
      have hl : raw20021step0Labels = raw20021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20021 raw20021Labels permutation434 hz
    mixedMoment B raw20021step0 raw20021step0Labels = mixedMoment B raw20021step1 raw20021step1Labels := by
      have hz : ∀ j, raw20021step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20021step1 = (fun i j => raw20021step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20021step1 raw20021step0; decide +kernel
      have hl : raw20021step1Labels = raw20021step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20021step0 raw20021step0Labels permutation80 hz
    mixedMoment B raw20021step1 raw20021step1Labels = mixedMoment B raw20021step2 raw20021step2Labels := by
      have hz : ∀ j, raw20021step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20021step2 = (fun i j => raw20021step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20021step2 raw20021step1; decide +kernel
      have hl : raw20021step2Labels = raw20021step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20021step1 raw20021step1Labels permutation14 hz
    mixedMoment B raw20021step2 raw20021step2Labels = mixedMoment B raw20021step3 raw20021step3Labels := by
      have ha : raw20021step3 = (fun i j => raw20021step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20021step3 raw20021step2; decide +kernel
      have hl : raw20021step3Labels = raw20021step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20021step2 raw20021step2Labels permutation7 permutation7
    mixedMoment B raw20021step3 raw20021step3Labels = mixedMoment B raw20021step4 raw20021step4Labels := by
      have ha : raw20021step4 = raw20021step3 := by apply Matrix.ext; unfold raw20021step4 raw20021step3; decide +kernel
      have hl : raw20021step3Labels = labelEmbedding1 ∘ raw20021step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20021step3 raw20021step3Labels raw20021step4Labels labelEmbedding1 hl
    _ = mixedMoment B node845 node845Labels := by rfl

def raw20022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20022Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20022step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20022step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20022step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20022step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![3, 1, -4]]
def raw20022step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20022step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![3, 1, -4]]
def raw20022step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20022 raw20022Labels = mixedMoment B node801 node801Labels := by
  calc
    mixedMoment B raw20022 raw20022Labels = mixedMoment B raw20022step0 raw20022step0Labels := by
      have hz : ∀ j, raw20022 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20022step0 = (fun i j => raw20022 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20022step0 raw20022; decide +kernel
      have hl : raw20022step0Labels = raw20022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20022 raw20022Labels permutation434 hz
    mixedMoment B raw20022step0 raw20022step0Labels = mixedMoment B raw20022step1 raw20022step1Labels := by
      have hz : ∀ j, raw20022step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20022step1 = (fun i j => raw20022step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20022step1 raw20022step0; decide +kernel
      have hl : raw20022step1Labels = raw20022step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20022step0 raw20022step0Labels permutation80 hz
    mixedMoment B raw20022step1 raw20022step1Labels = mixedMoment B raw20022step2 raw20022step2Labels := by
      have ha : raw20022step2 = (fun i j => raw20022step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20022step2 raw20022step1; decide +kernel
      have hl : raw20022step2Labels = raw20022step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20022step1 raw20022step1Labels permutation29 permutation7
    mixedMoment B raw20022step2 raw20022step2Labels = mixedMoment B raw20022step3 raw20022step3Labels := by
      have ha : raw20022step3 = raw20022step2 := by apply Matrix.ext; unfold raw20022step3 raw20022step2; decide +kernel
      have hl : raw20022step2Labels = labelEmbedding1 ∘ raw20022step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20022step2 raw20022step2Labels raw20022step3Labels labelEmbedding1 hl
    _ = mixedMoment B node801 node801Labels := by rfl

def raw20023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20023Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20023step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20023step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20023step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20023step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![3, 1, -4]]
def raw20023step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20023step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![3, 1, -4]]
def raw20023step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20023 raw20023Labels = mixedMoment B node801 node801Labels := by
  calc
    mixedMoment B raw20023 raw20023Labels = mixedMoment B raw20023step0 raw20023step0Labels := by
      have hz : ∀ j, raw20023 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20023step0 = (fun i j => raw20023 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20023step0 raw20023; decide +kernel
      have hl : raw20023step0Labels = raw20023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20023 raw20023Labels permutation434 hz
    mixedMoment B raw20023step0 raw20023step0Labels = mixedMoment B raw20023step1 raw20023step1Labels := by
      have hz : ∀ j, raw20023step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20023step1 = (fun i j => raw20023step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20023step1 raw20023step0; decide +kernel
      have hl : raw20023step1Labels = raw20023step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20023step0 raw20023step0Labels permutation56 hz
    mixedMoment B raw20023step1 raw20023step1Labels = mixedMoment B raw20023step2 raw20023step2Labels := by
      have ha : raw20023step2 = (fun i j => raw20023step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20023step2 raw20023step1; decide +kernel
      have hl : raw20023step2Labels = raw20023step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20023step1 raw20023step1Labels permutation29 permutation7
    mixedMoment B raw20023step2 raw20023step2Labels = mixedMoment B raw20023step3 raw20023step3Labels := by
      have ha : raw20023step3 = raw20023step2 := by apply Matrix.ext; unfold raw20023step3 raw20023step2; decide +kernel
      have hl : raw20023step2Labels = labelEmbedding1 ∘ raw20023step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20023step2 raw20023step2Labels raw20023step3Labels labelEmbedding1 hl
    _ = mixedMoment B node801 node801Labels := by rfl

def raw20024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20024Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20024step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20024step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20024step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20024step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![3, 1, -4]]
def raw20024step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20024step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![3, 1, -4]]
def raw20024step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20024 raw20024Labels = mixedMoment B node801 node801Labels := by
  calc
    mixedMoment B raw20024 raw20024Labels = mixedMoment B raw20024step0 raw20024step0Labels := by
      have hz : ∀ j, raw20024 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20024step0 = (fun i j => raw20024 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20024step0 raw20024; decide +kernel
      have hl : raw20024step0Labels = raw20024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20024 raw20024Labels permutation346 hz
    mixedMoment B raw20024step0 raw20024step0Labels = mixedMoment B raw20024step1 raw20024step1Labels := by
      have hz : ∀ j, raw20024step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20024step1 = (fun i j => raw20024step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20024step1 raw20024step0; decide +kernel
      have hl : raw20024step1Labels = raw20024step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20024step0 raw20024step0Labels permutation56 hz
    mixedMoment B raw20024step1 raw20024step1Labels = mixedMoment B raw20024step2 raw20024step2Labels := by
      have ha : raw20024step2 = (fun i j => raw20024step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20024step2 raw20024step1; decide +kernel
      have hl : raw20024step2Labels = raw20024step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20024step1 raw20024step1Labels permutation29 permutation7
    mixedMoment B raw20024step2 raw20024step2Labels = mixedMoment B raw20024step3 raw20024step3Labels := by
      have ha : raw20024step3 = raw20024step2 := by apply Matrix.ext; unfold raw20024step3 raw20024step2; decide +kernel
      have hl : raw20024step2Labels = labelEmbedding1 ∘ raw20024step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20024step2 raw20024step2Labels raw20024step3Labels labelEmbedding1 hl
    _ = mixedMoment B node801 node801Labels := by rfl

def raw20025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 1, -4]]
def raw20025Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 1, -4]]
def raw20025step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20025step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![3, 1, -4]]
def raw20025step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20025step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw20025step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20025step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw20025step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20025step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw20025step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20025 raw20025Labels = mixedMoment B node1077 node1077Labels := by
  calc
    mixedMoment B raw20025 raw20025Labels = mixedMoment B raw20025step0 raw20025step0Labels := by
      have hz : ∀ j, raw20025 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20025step0 = (fun i j => raw20025 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20025step0 raw20025; decide +kernel
      have hl : raw20025step0Labels = raw20025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20025 raw20025Labels permutation434 hz
    mixedMoment B raw20025step0 raw20025step0Labels = mixedMoment B raw20025step1 raw20025step1Labels := by
      have hz : ∀ j, raw20025step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20025step1 = (fun i j => raw20025step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20025step1 raw20025step0; decide +kernel
      have hl : raw20025step1Labels = raw20025step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20025step0 raw20025step0Labels permutation80 hz
    mixedMoment B raw20025step1 raw20025step1Labels = mixedMoment B raw20025step2 raw20025step2Labels := by
      have hz : ∀ j, raw20025step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20025step2 = (fun i j => raw20025step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20025step2 raw20025step1; decide +kernel
      have hl : raw20025step2Labels = raw20025step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20025step1 raw20025step1Labels permutation14 hz
    mixedMoment B raw20025step2 raw20025step2Labels = mixedMoment B raw20025step3 raw20025step3Labels := by
      have ha : raw20025step3 = (fun i j => raw20025step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20025step3 raw20025step2; decide +kernel
      have hl : raw20025step3Labels = raw20025step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20025step2 raw20025step2Labels permutation7 permutation7
    mixedMoment B raw20025step3 raw20025step3Labels = mixedMoment B raw20025step4 raw20025step4Labels := by
      have ha : raw20025step4 = raw20025step3 := by apply Matrix.ext; unfold raw20025step4 raw20025step3; decide +kernel
      have hl : raw20025step3Labels = labelEmbedding1 ∘ raw20025step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20025step3 raw20025step3Labels raw20025step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1077 node1077Labels := by rfl

def raw20026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20026Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20026step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20026step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20026step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![5, -1, -4]]
def raw20026step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20026step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![3, 2, -5]]
def raw20026step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20026step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![3, 2, -5]]
def raw20026step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20026 raw20026Labels = mixedMoment B node686 node686Labels := by
  calc
    mixedMoment B raw20026 raw20026Labels = mixedMoment B raw20026step0 raw20026step0Labels := by
      have hz : ∀ j, raw20026 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20026step0 = (fun i j => raw20026 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20026step0 raw20026; decide +kernel
      have hl : raw20026step0Labels = raw20026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20026 raw20026Labels permutation434 hz
    mixedMoment B raw20026step0 raw20026step0Labels = mixedMoment B raw20026step1 raw20026step1Labels := by
      have hz : ∀ j, raw20026step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20026step1 = (fun i j => raw20026step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20026step1 raw20026step0; decide +kernel
      have hl : raw20026step1Labels = raw20026step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20026step0 raw20026step0Labels permutation80 hz
    mixedMoment B raw20026step1 raw20026step1Labels = mixedMoment B raw20026step2 raw20026step2Labels := by
      have hz : ∀ j, raw20026step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20026step2 = (fun i j => raw20026step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20026step2 raw20026step1; decide +kernel
      have hl : raw20026step2Labels = raw20026step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20026step1 raw20026step1Labels permutation14 hz
    mixedMoment B raw20026step2 raw20026step2Labels = mixedMoment B raw20026step3 raw20026step3Labels := by
      have ha : raw20026step3 = (fun i j => raw20026step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20026step3 raw20026step2; decide +kernel
      have hl : raw20026step3Labels = raw20026step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20026step2 raw20026step2Labels permutation7 permutation7
    mixedMoment B raw20026step3 raw20026step3Labels = mixedMoment B raw20026step4 raw20026step4Labels := by
      have ha : raw20026step4 = raw20026step3 := by apply Matrix.ext; unfold raw20026step4 raw20026step3; decide +kernel
      have hl : raw20026step3Labels = labelEmbedding1 ∘ raw20026step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20026step3 raw20026step3Labels raw20026step4Labels labelEmbedding1 hl
    _ = mixedMoment B node686 node686Labels := by rfl

def raw20027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20027Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20027step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20027step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20027step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20027step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20027step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20027step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20027 raw20027Labels = mixedMoment B node665 node665Labels := by
  calc
    mixedMoment B raw20027 raw20027Labels = mixedMoment B raw20027step0 raw20027step0Labels := by
      have hz : ∀ j, raw20027 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20027step0 = (fun i j => raw20027 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20027step0 raw20027; decide +kernel
      have hl : raw20027step0Labels = raw20027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20027 raw20027Labels permutation434 hz
    mixedMoment B raw20027step0 raw20027step0Labels = mixedMoment B raw20027step1 raw20027step1Labels := by
      have hz : ∀ j, raw20027step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20027step1 = (fun i j => raw20027step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20027step1 raw20027step0; decide +kernel
      have hl : raw20027step1Labels = raw20027step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20027step0 raw20027step0Labels permutation80 hz
    mixedMoment B raw20027step1 raw20027step1Labels = mixedMoment B raw20027step2 raw20027step2Labels := by
      have ha : raw20027step2 = (fun i j => raw20027step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20027step2 raw20027step1; decide +kernel
      have hl : raw20027step2Labels = raw20027step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20027step1 raw20027step1Labels permutation29 permutation7
    mixedMoment B raw20027step2 raw20027step2Labels = mixedMoment B raw20027step3 raw20027step3Labels := by
      have ha : raw20027step3 = raw20027step2 := by apply Matrix.ext; unfold raw20027step3 raw20027step2; decide +kernel
      have hl : raw20027step2Labels = labelEmbedding1 ∘ raw20027step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20027step2 raw20027step2Labels raw20027step3Labels labelEmbedding1 hl
    _ = mixedMoment B node665 node665Labels := by rfl

def raw20028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20028Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20028step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20028step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20028step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20028step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20028step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20028step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20028step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20028 raw20028Labels = mixedMoment B node665 node665Labels := by
  calc
    mixedMoment B raw20028 raw20028Labels = mixedMoment B raw20028step0 raw20028step0Labels := by
      have hz : ∀ j, raw20028 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20028step0 = (fun i j => raw20028 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20028step0 raw20028; decide +kernel
      have hl : raw20028step0Labels = raw20028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20028 raw20028Labels permutation434 hz
    mixedMoment B raw20028step0 raw20028step0Labels = mixedMoment B raw20028step1 raw20028step1Labels := by
      have hz : ∀ j, raw20028step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20028step1 = (fun i j => raw20028step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20028step1 raw20028step0; decide +kernel
      have hl : raw20028step1Labels = raw20028step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20028step0 raw20028step0Labels permutation56 hz
    mixedMoment B raw20028step1 raw20028step1Labels = mixedMoment B raw20028step2 raw20028step2Labels := by
      have ha : raw20028step2 = (fun i j => raw20028step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20028step2 raw20028step1; decide +kernel
      have hl : raw20028step2Labels = raw20028step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20028step1 raw20028step1Labels permutation29 permutation7
    mixedMoment B raw20028step2 raw20028step2Labels = mixedMoment B raw20028step3 raw20028step3Labels := by
      have ha : raw20028step3 = raw20028step2 := by apply Matrix.ext; unfold raw20028step3 raw20028step2; decide +kernel
      have hl : raw20028step2Labels = labelEmbedding1 ∘ raw20028step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20028step2 raw20028step2Labels raw20028step3Labels labelEmbedding1 hl
    _ = mixedMoment B node665 node665Labels := by rfl

def raw20029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20029Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20029step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20029step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20029step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20029step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20029step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20029step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw20029step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20029 raw20029Labels = mixedMoment B node665 node665Labels := by
  calc
    mixedMoment B raw20029 raw20029Labels = mixedMoment B raw20029step0 raw20029step0Labels := by
      have hz : ∀ j, raw20029 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20029step0 = (fun i j => raw20029 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20029step0 raw20029; decide +kernel
      have hl : raw20029step0Labels = raw20029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20029 raw20029Labels permutation346 hz
    mixedMoment B raw20029step0 raw20029step0Labels = mixedMoment B raw20029step1 raw20029step1Labels := by
      have hz : ∀ j, raw20029step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20029step1 = (fun i j => raw20029step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20029step1 raw20029step0; decide +kernel
      have hl : raw20029step1Labels = raw20029step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20029step0 raw20029step0Labels permutation56 hz
    mixedMoment B raw20029step1 raw20029step1Labels = mixedMoment B raw20029step2 raw20029step2Labels := by
      have ha : raw20029step2 = (fun i j => raw20029step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20029step2 raw20029step1; decide +kernel
      have hl : raw20029step2Labels = raw20029step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20029step1 raw20029step1Labels permutation29 permutation7
    mixedMoment B raw20029step2 raw20029step2Labels = mixedMoment B raw20029step3 raw20029step3Labels := by
      have ha : raw20029step3 = raw20029step2 := by apply Matrix.ext; unfold raw20029step3 raw20029step2; decide +kernel
      have hl : raw20029step2Labels = labelEmbedding1 ∘ raw20029step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20029step2 raw20029step2Labels raw20029step3Labels labelEmbedding1 hl
    _ = mixedMoment B node665 node665Labels := by rfl

def raw20030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![5, -1, -4]]
def raw20030Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![5, -1, -4]]
def raw20030step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20030step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![5, -1, -4]]
def raw20030step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20030step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![5, -1, -4]]
def raw20030step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20030step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![3, 1, -4]]
def raw20030step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20030step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![3, 1, -4]]
def raw20030step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20030 raw20030Labels = mixedMoment B node691 node691Labels := by
  calc
    mixedMoment B raw20030 raw20030Labels = mixedMoment B raw20030step0 raw20030step0Labels := by
      have hz : ∀ j, raw20030 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20030step0 = (fun i j => raw20030 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20030step0 raw20030; decide +kernel
      have hl : raw20030step0Labels = raw20030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20030 raw20030Labels permutation434 hz
    mixedMoment B raw20030step0 raw20030step0Labels = mixedMoment B raw20030step1 raw20030step1Labels := by
      have hz : ∀ j, raw20030step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20030step1 = (fun i j => raw20030step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20030step1 raw20030step0; decide +kernel
      have hl : raw20030step1Labels = raw20030step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20030step0 raw20030step0Labels permutation80 hz
    mixedMoment B raw20030step1 raw20030step1Labels = mixedMoment B raw20030step2 raw20030step2Labels := by
      have hz : ∀ j, raw20030step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20030step2 = (fun i j => raw20030step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20030step2 raw20030step1; decide +kernel
      have hl : raw20030step2Labels = raw20030step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20030step1 raw20030step1Labels permutation14 hz
    mixedMoment B raw20030step2 raw20030step2Labels = mixedMoment B raw20030step3 raw20030step3Labels := by
      have ha : raw20030step3 = (fun i j => raw20030step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20030step3 raw20030step2; decide +kernel
      have hl : raw20030step3Labels = raw20030step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20030step2 raw20030step2Labels permutation7 permutation7
    mixedMoment B raw20030step3 raw20030step3Labels = mixedMoment B raw20030step4 raw20030step4Labels := by
      have ha : raw20030step4 = raw20030step3 := by apply Matrix.ext; unfold raw20030step4 raw20030step3; decide +kernel
      have hl : raw20030step3Labels = labelEmbedding1 ∘ raw20030step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20030step3 raw20030step3Labels raw20030step4Labels labelEmbedding1 hl
    _ = mixedMoment B node691 node691Labels := by rfl

def raw20031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20031Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20031step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20031step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20031step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20031step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![4, 0, -4]]
def raw20031step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20031step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-4, 1, 3]]
def raw20031step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20031step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![4, -1, -3]]
def raw20031step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20031 raw20031Labels = mixedMoment B node817 node817Labels := by
  calc
    mixedMoment B raw20031 raw20031Labels = mixedMoment B raw20031step0 raw20031step0Labels := by
      have hz : ∀ j, raw20031 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20031step0 = (fun i j => raw20031 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20031step0 raw20031; decide +kernel
      have hl : raw20031step0Labels = raw20031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20031 raw20031Labels permutation434 hz
    mixedMoment B raw20031step0 raw20031step0Labels = mixedMoment B raw20031step1 raw20031step1Labels := by
      have hz : ∀ j, raw20031step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20031step1 = (fun i j => raw20031step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20031step1 raw20031step0; decide +kernel
      have hl : raw20031step1Labels = raw20031step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20031step0 raw20031step0Labels permutation80 hz
    mixedMoment B raw20031step1 raw20031step1Labels = mixedMoment B raw20031step2 raw20031step2Labels := by
      have hz : ∀ j, raw20031step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20031step2 = (fun i j => raw20031step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20031step2 raw20031step1; decide +kernel
      have hl : raw20031step2Labels = raw20031step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20031step1 raw20031step1Labels permutation14 hz
    mixedMoment B raw20031step2 raw20031step2Labels = mixedMoment B raw20031step3 raw20031step3Labels := by
      have ha : raw20031step3 = (fun i j => raw20031step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20031step3 raw20031step2; decide +kernel
      have hl : raw20031step3Labels = raw20031step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20031step2 raw20031step2Labels permutation7 permutation2
    mixedMoment B raw20031step3 raw20031step3Labels = mixedMoment B raw20031step4 raw20031step4Labels := by
      have ha : raw20031step4 = -raw20031step3 := by apply Matrix.ext; change ∀ i j, raw20031step4 i j = -(raw20031step3 i j); unfold raw20031step4 raw20031step3; decide +kernel
      have hl : raw20031step4Labels = raw20031step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node817 node817Labels := by rfl

def raw20032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20032Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20032step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20032step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20032step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20032step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw20032step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20032 raw20032Labels = mixedMoment B node570 node570Labels := by
  calc
    mixedMoment B raw20032 raw20032Labels = mixedMoment B raw20032step0 raw20032step0Labels := by
      have hz : ∀ j, raw20032 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20032step0 = (fun i j => raw20032 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20032step0 raw20032; decide +kernel
      have hl : raw20032step0Labels = raw20032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20032 raw20032Labels permutation434 hz
    mixedMoment B raw20032step0 raw20032step0Labels = mixedMoment B raw20032step1 raw20032step1Labels := by
      have hz : ∀ j, raw20032step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20032step1 = (fun i j => raw20032step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20032step1 raw20032step0; decide +kernel
      have hl : raw20032step1Labels = raw20032step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20032step0 raw20032step0Labels permutation80 hz
    mixedMoment B raw20032step1 raw20032step1Labels = mixedMoment B raw20032step2 raw20032step2Labels := by
      have ha : raw20032step2 = (fun i j => raw20032step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20032step2 raw20032step1; decide +kernel
      have hl : raw20032step2Labels = raw20032step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20032step1 raw20032step1Labels permutation10 permutation2
    _ = mixedMoment B node570 node570Labels := by rfl

def raw20033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20033Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20033step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20033step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20033step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20033step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw20033step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20033 raw20033Labels = mixedMoment B node570 node570Labels := by
  calc
    mixedMoment B raw20033 raw20033Labels = mixedMoment B raw20033step0 raw20033step0Labels := by
      have hz : ∀ j, raw20033 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20033step0 = (fun i j => raw20033 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20033step0 raw20033; decide +kernel
      have hl : raw20033step0Labels = raw20033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20033 raw20033Labels permutation434 hz
    mixedMoment B raw20033step0 raw20033step0Labels = mixedMoment B raw20033step1 raw20033step1Labels := by
      have hz : ∀ j, raw20033step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20033step1 = (fun i j => raw20033step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20033step1 raw20033step0; decide +kernel
      have hl : raw20033step1Labels = raw20033step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20033step0 raw20033step0Labels permutation56 hz
    mixedMoment B raw20033step1 raw20033step1Labels = mixedMoment B raw20033step2 raw20033step2Labels := by
      have ha : raw20033step2 = (fun i j => raw20033step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20033step2 raw20033step1; decide +kernel
      have hl : raw20033step2Labels = raw20033step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20033step1 raw20033step1Labels permutation10 permutation2
    _ = mixedMoment B node570 node570Labels := by rfl

def raw20034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20034Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20034step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20034step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20034step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20034step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![4, 0, -4]]
def raw20034step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20034 raw20034Labels = mixedMoment B node570 node570Labels := by
  calc
    mixedMoment B raw20034 raw20034Labels = mixedMoment B raw20034step0 raw20034step0Labels := by
      have hz : ∀ j, raw20034 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20034step0 = (fun i j => raw20034 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20034step0 raw20034; decide +kernel
      have hl : raw20034step0Labels = raw20034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20034 raw20034Labels permutation346 hz
    mixedMoment B raw20034step0 raw20034step0Labels = mixedMoment B raw20034step1 raw20034step1Labels := by
      have hz : ∀ j, raw20034step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20034step1 = (fun i j => raw20034step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20034step1 raw20034step0; decide +kernel
      have hl : raw20034step1Labels = raw20034step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20034step0 raw20034step0Labels permutation56 hz
    mixedMoment B raw20034step1 raw20034step1Labels = mixedMoment B raw20034step2 raw20034step2Labels := by
      have ha : raw20034step2 = (fun i j => raw20034step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20034step2 raw20034step1; decide +kernel
      have hl : raw20034step2Labels = raw20034step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20034step1 raw20034step1Labels permutation10 permutation2
    _ = mixedMoment B node570 node570Labels := by rfl

def raw20035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20035step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20035step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20035step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![4, 0, -4]]
def raw20035step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20035 raw20035Labels = mixedMoment B node596 node596Labels := by
  calc
    mixedMoment B raw20035 raw20035Labels = mixedMoment B raw20035step0 raw20035step0Labels := by
      have hz : ∀ j, raw20035 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20035step0 = (fun i j => raw20035 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20035step0 raw20035; decide +kernel
      have hl : raw20035step0Labels = raw20035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20035 raw20035Labels permutation434 hz
    mixedMoment B raw20035step0 raw20035step0Labels = mixedMoment B raw20035step1 raw20035step1Labels := by
      have hz : ∀ j, raw20035step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20035step1 = (fun i j => raw20035step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20035step1 raw20035step0; decide +kernel
      have hl : raw20035step1Labels = raw20035step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20035step0 raw20035step0Labels permutation80 hz
    mixedMoment B raw20035step1 raw20035step1Labels = mixedMoment B raw20035step2 raw20035step2Labels := by
      have hz : ∀ j, raw20035step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20035step2 = (fun i j => raw20035step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20035step2 raw20035step1; decide +kernel
      have hl : raw20035step2Labels = raw20035step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20035step1 raw20035step1Labels permutation14 hz
    _ = mixedMoment B node596 node596Labels := by rfl

def raw20036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20036Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20036step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20036step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20036step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20036step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![5, -1, -4]]
def raw20036step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20036step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-5, 2, 3]]
def raw20036step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20036step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![5, -2, -3]]
def raw20036step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20036 raw20036Labels = mixedMoment B node549 node549Labels := by
  calc
    mixedMoment B raw20036 raw20036Labels = mixedMoment B raw20036step0 raw20036step0Labels := by
      have hz : ∀ j, raw20036 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20036step0 = (fun i j => raw20036 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20036step0 raw20036; decide +kernel
      have hl : raw20036step0Labels = raw20036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20036 raw20036Labels permutation434 hz
    mixedMoment B raw20036step0 raw20036step0Labels = mixedMoment B raw20036step1 raw20036step1Labels := by
      have hz : ∀ j, raw20036step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20036step1 = (fun i j => raw20036step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20036step1 raw20036step0; decide +kernel
      have hl : raw20036step1Labels = raw20036step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20036step0 raw20036step0Labels permutation80 hz
    mixedMoment B raw20036step1 raw20036step1Labels = mixedMoment B raw20036step2 raw20036step2Labels := by
      have hz : ∀ j, raw20036step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20036step2 = (fun i j => raw20036step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20036step2 raw20036step1; decide +kernel
      have hl : raw20036step2Labels = raw20036step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20036step1 raw20036step1Labels permutation14 hz
    mixedMoment B raw20036step2 raw20036step2Labels = mixedMoment B raw20036step3 raw20036step3Labels := by
      have ha : raw20036step3 = (fun i j => raw20036step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20036step3 raw20036step2; decide +kernel
      have hl : raw20036step3Labels = raw20036step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20036step2 raw20036step2Labels permutation7 permutation2
    mixedMoment B raw20036step3 raw20036step3Labels = mixedMoment B raw20036step4 raw20036step4Labels := by
      have ha : raw20036step4 = -raw20036step3 := by apply Matrix.ext; change ∀ i j, raw20036step4 i j = -(raw20036step3 i j); unfold raw20036step4 raw20036step3; decide +kernel
      have hl : raw20036step4Labels = raw20036step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node549 node549Labels := by rfl

def raw20037 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![0, 0], ![-1, 1], ![4, -4]]
def raw20037Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20037step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![-1, 1], ![4, -4]]
def raw20037step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20037step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![4, -4]]
def raw20037step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20037step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![4, -4]]
def raw20037step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20037step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-3, 3]]
def raw20037step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20037step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw20037step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20037 raw20037Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw20037 raw20037Labels = mixedMoment B raw20037step0 raw20037step0Labels := by
      have hz : ∀ j, raw20037 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20037step0 = (fun i j => raw20037 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20037step0 raw20037; decide +kernel
      have hl : raw20037step0Labels = raw20037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20037 raw20037Labels permutation434 hz
    mixedMoment B raw20037step0 raw20037step0Labels = mixedMoment B raw20037step1 raw20037step1Labels := by
      have hz : ∀ j, raw20037step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20037step1 = (fun i j => raw20037step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20037step1 raw20037step0; decide +kernel
      have hl : raw20037step1Labels = raw20037step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20037step0 raw20037step0Labels permutation80 hz
    mixedMoment B raw20037step1 raw20037step1Labels = mixedMoment B raw20037step2 raw20037step2Labels := by
      have hz : ∀ j, raw20037step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20037step2 = (fun i j => raw20037step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20037step2 raw20037step1; decide +kernel
      have hl : raw20037step2Labels = raw20037step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20037step1 raw20037step1Labels permutation14 hz
    mixedMoment B raw20037step2 raw20037step2Labels = mixedMoment B raw20037step3 raw20037step3Labels := by
      have ha : raw20037step3 = (fun i j => raw20037step2 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20037step3 raw20037step2; decide +kernel
      have hl : raw20037step3Labels = raw20037step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20037step2 raw20037step2Labels permutation7 permutation0
    mixedMoment B raw20037step3 raw20037step3Labels = mixedMoment B raw20037step4 raw20037step4Labels := by
      have ha : raw20037step4 = -raw20037step3 := by apply Matrix.ext; change ∀ i j, raw20037step4 i j = -(raw20037step3 i j); unfold raw20037step4 raw20037step3; decide +kernel
      have hl : raw20037step4Labels = raw20037step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4070 node4070Labels := by rfl

def raw20038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20038Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20038step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20038step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw20038step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20038step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw20038step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20038 raw20038Labels = mixedMoment B node701 node701Labels := by
  calc
    mixedMoment B raw20038 raw20038Labels = mixedMoment B raw20038step0 raw20038step0Labels := by
      have hz : ∀ j, raw20038 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20038step0 = (fun i j => raw20038 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20038step0 raw20038; decide +kernel
      have hl : raw20038step0Labels = raw20038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20038 raw20038Labels permutation434 hz
    mixedMoment B raw20038step0 raw20038step0Labels = mixedMoment B raw20038step1 raw20038step1Labels := by
      have ha : raw20038step1 = (fun i j => raw20038step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20038step1 raw20038step0; decide +kernel
      have hl : raw20038step1Labels = raw20038step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20038step0 raw20038step0Labels permutation139 permutation2
    mixedMoment B raw20038step1 raw20038step1Labels = mixedMoment B raw20038step2 raw20038step2Labels := by
      have ha : raw20038step2 = -raw20038step1 := by apply Matrix.ext; change ∀ i j, raw20038step2 i j = -(raw20038step1 i j); unfold raw20038step2 raw20038step1; decide +kernel
      have hl : raw20038step2Labels = raw20038step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node701 node701Labels := by rfl

def raw20039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20039Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20039step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20039step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw20039step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20039step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw20039step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20039 raw20039Labels = mixedMoment B node701 node701Labels := by
  calc
    mixedMoment B raw20039 raw20039Labels = mixedMoment B raw20039step0 raw20039step0Labels := by
      have hz : ∀ j, raw20039 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20039step0 = (fun i j => raw20039 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20039step0 raw20039; decide +kernel
      have hl : raw20039step0Labels = raw20039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20039 raw20039Labels permutation346 hz
    mixedMoment B raw20039step0 raw20039step0Labels = mixedMoment B raw20039step1 raw20039step1Labels := by
      have ha : raw20039step1 = (fun i j => raw20039step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20039step1 raw20039step0; decide +kernel
      have hl : raw20039step1Labels = raw20039step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20039step0 raw20039step0Labels permutation139 permutation2
    mixedMoment B raw20039step1 raw20039step1Labels = mixedMoment B raw20039step2 raw20039step2Labels := by
      have ha : raw20039step2 = -raw20039step1 := by apply Matrix.ext; change ∀ i j, raw20039step2 i j = -(raw20039step1 i j); unfold raw20039step2 raw20039step1; decide +kernel
      have hl : raw20039step2Labels = raw20039step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node701 node701Labels := by rfl

def raw20040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20040Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20040step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20040step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![4, 0, -4]]
def raw20040step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20040step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-4, 1, 3]]
def raw20040step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20040step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![4, -1, -3]]
def raw20040step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20040 raw20040Labels = mixedMoment B node723 node723Labels := by
  calc
    mixedMoment B raw20040 raw20040Labels = mixedMoment B raw20040step0 raw20040step0Labels := by
      have hz : ∀ j, raw20040 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20040step0 = (fun i j => raw20040 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20040step0 raw20040; decide +kernel
      have hl : raw20040step0Labels = raw20040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20040 raw20040Labels permutation434 hz
    mixedMoment B raw20040step0 raw20040step0Labels = mixedMoment B raw20040step1 raw20040step1Labels := by
      have hz : ∀ j, raw20040step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20040step1 = (fun i j => raw20040step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20040step1 raw20040step0; decide +kernel
      have hl : raw20040step1Labels = raw20040step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20040step0 raw20040step0Labels permutation80 hz
    mixedMoment B raw20040step1 raw20040step1Labels = mixedMoment B raw20040step2 raw20040step2Labels := by
      have ha : raw20040step2 = (fun i j => raw20040step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20040step2 raw20040step1; decide +kernel
      have hl : raw20040step2Labels = raw20040step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20040step1 raw20040step1Labels permutation29 permutation2
    mixedMoment B raw20040step2 raw20040step2Labels = mixedMoment B raw20040step3 raw20040step3Labels := by
      have ha : raw20040step3 = -raw20040step2 := by apply Matrix.ext; change ∀ i j, raw20040step3 i j = -(raw20040step2 i j); unfold raw20040step3 raw20040step2; decide +kernel
      have hl : raw20040step3Labels = raw20040step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node723 node723Labels := by rfl

def raw20041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20041Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20041step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![3, 1, -4]]
def raw20041step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20041step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw20041step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20041 raw20041Labels = mixedMoment B node1002 node1002Labels := by
  calc
    mixedMoment B raw20041 raw20041Labels = mixedMoment B raw20041step0 raw20041step0Labels := by
      have hz : ∀ j, raw20041 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20041step0 = (fun i j => raw20041 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20041step0 raw20041; decide +kernel
      have hl : raw20041step0Labels = raw20041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20041 raw20041Labels permutation434 hz
    mixedMoment B raw20041step0 raw20041step0Labels = mixedMoment B raw20041step1 raw20041step1Labels := by
      have hz : ∀ j, raw20041step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20041step1 = (fun i j => raw20041step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20041step1 raw20041step0; decide +kernel
      have hl : raw20041step1Labels = raw20041step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20041step0 raw20041step0Labels permutation80 hz
    mixedMoment B raw20041step1 raw20041step1Labels = mixedMoment B raw20041step2 raw20041step2Labels := by
      have ha : raw20041step2 = (fun i j => raw20041step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20041step2 raw20041step1; decide +kernel
      have hl : raw20041step2Labels = raw20041step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20041step1 raw20041step1Labels permutation10 permutation2
    _ = mixedMoment B node1002 node1002Labels := by rfl

def raw20042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20042Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20042step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20042step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20042step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw20042step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20042step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20042step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20042 raw20042Labels = mixedMoment B node809 node809Labels := by
  calc
    mixedMoment B raw20042 raw20042Labels = mixedMoment B raw20042step0 raw20042step0Labels := by
      have hz : ∀ j, raw20042 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20042step0 = (fun i j => raw20042 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20042step0 raw20042; decide +kernel
      have hl : raw20042step0Labels = raw20042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20042 raw20042Labels permutation434 hz
    mixedMoment B raw20042step0 raw20042step0Labels = mixedMoment B raw20042step1 raw20042step1Labels := by
      have hz : ∀ j, raw20042step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20042step1 = (fun i j => raw20042step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20042step1 raw20042step0; decide +kernel
      have hl : raw20042step1Labels = raw20042step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20042step0 raw20042step0Labels permutation80 hz
    mixedMoment B raw20042step1 raw20042step1Labels = mixedMoment B raw20042step2 raw20042step2Labels := by
      have ha : raw20042step2 = (fun i j => raw20042step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20042step2 raw20042step1; decide +kernel
      have hl : raw20042step2Labels = raw20042step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20042step1 raw20042step1Labels permutation31 permutation2
    mixedMoment B raw20042step2 raw20042step2Labels = mixedMoment B raw20042step3 raw20042step3Labels := by
      have ha : raw20042step3 = -raw20042step2 := by apply Matrix.ext; change ∀ i j, raw20042step3 i j = -(raw20042step2 i j); unfold raw20042step3 raw20042step2; decide +kernel
      have hl : raw20042step3Labels = raw20042step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node809 node809Labels := by rfl

def raw20043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20043Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20043step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw20043step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20043step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw20043step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20043 raw20043Labels = mixedMoment B node701 node701Labels := by
  calc
    mixedMoment B raw20043 raw20043Labels = mixedMoment B raw20043step0 raw20043step0Labels := by
      have hz : ∀ j, raw20043 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20043step0 = (fun i j => raw20043 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20043step0 raw20043; decide +kernel
      have hl : raw20043step0Labels = raw20043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20043 raw20043Labels permutation434 hz
    mixedMoment B raw20043step0 raw20043step0Labels = mixedMoment B raw20043step1 raw20043step1Labels := by
      have ha : raw20043step1 = (fun i j => raw20043step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20043step1 raw20043step0; decide +kernel
      have hl : raw20043step1Labels = raw20043step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20043step0 raw20043step0Labels permutation145 permutation2
    mixedMoment B raw20043step1 raw20043step1Labels = mixedMoment B raw20043step2 raw20043step2Labels := by
      have ha : raw20043step2 = -raw20043step1 := by apply Matrix.ext; change ∀ i j, raw20043step2 i j = -(raw20043step1 i j); unfold raw20043step2 raw20043step1; decide +kernel
      have hl : raw20043step2Labels = raw20043step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node701 node701Labels := by rfl

def raw20044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20044Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![4, 0, -4]]
def raw20044step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw20044step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20044step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw20044step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20044 raw20044Labels = mixedMoment B node701 node701Labels := by
  calc
    mixedMoment B raw20044 raw20044Labels = mixedMoment B raw20044step0 raw20044step0Labels := by
      have hz : ∀ j, raw20044 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20044step0 = (fun i j => raw20044 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20044step0 raw20044; decide +kernel
      have hl : raw20044step0Labels = raw20044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20044 raw20044Labels permutation346 hz
    mixedMoment B raw20044step0 raw20044step0Labels = mixedMoment B raw20044step1 raw20044step1Labels := by
      have ha : raw20044step1 = (fun i j => raw20044step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20044step1 raw20044step0; decide +kernel
      have hl : raw20044step1Labels = raw20044step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20044step0 raw20044step0Labels permutation145 permutation2
    mixedMoment B raw20044step1 raw20044step1Labels = mixedMoment B raw20044step2 raw20044step2Labels := by
      have ha : raw20044step2 = -raw20044step1 := by apply Matrix.ext; change ∀ i j, raw20044step2 i j = -(raw20044step1 i j); unfold raw20044step2 raw20044step1; decide +kernel
      have hl : raw20044step2Labels = raw20044step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node701 node701Labels := by rfl

def raw20045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20045Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20045step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20045step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20045step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20045step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw20045step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20045step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw20045step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20045 raw20045Labels = mixedMoment B node735 node735Labels := by
  calc
    mixedMoment B raw20045 raw20045Labels = mixedMoment B raw20045step0 raw20045step0Labels := by
      have hz : ∀ j, raw20045 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20045step0 = (fun i j => raw20045 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20045step0 raw20045; decide +kernel
      have hl : raw20045step0Labels = raw20045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20045 raw20045Labels permutation434 hz
    mixedMoment B raw20045step0 raw20045step0Labels = mixedMoment B raw20045step1 raw20045step1Labels := by
      have hz : ∀ j, raw20045step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20045step1 = (fun i j => raw20045step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20045step1 raw20045step0; decide +kernel
      have hl : raw20045step1Labels = raw20045step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20045step0 raw20045step0Labels permutation80 hz
    mixedMoment B raw20045step1 raw20045step1Labels = mixedMoment B raw20045step2 raw20045step2Labels := by
      have ha : raw20045step2 = (fun i j => raw20045step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20045step2 raw20045step1; decide +kernel
      have hl : raw20045step2Labels = raw20045step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20045step1 raw20045step1Labels permutation31 permutation2
    mixedMoment B raw20045step2 raw20045step2Labels = mixedMoment B raw20045step3 raw20045step3Labels := by
      have ha : raw20045step3 = -raw20045step2 := by apply Matrix.ext; change ∀ i j, raw20045step3 i j = -(raw20045step2 i j); unfold raw20045step3 raw20045step2; decide +kernel
      have hl : raw20045step3Labels = raw20045step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node735 node735Labels := by rfl

def raw20046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20046Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20046step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20046step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![5, -1, -4]]
def raw20046step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20046step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw20046step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20046step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw20046step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20046 raw20046Labels = mixedMoment B node540 node540Labels := by
  calc
    mixedMoment B raw20046 raw20046Labels = mixedMoment B raw20046step0 raw20046step0Labels := by
      have hz : ∀ j, raw20046 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20046step0 = (fun i j => raw20046 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20046step0 raw20046; decide +kernel
      have hl : raw20046step0Labels = raw20046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20046 raw20046Labels permutation434 hz
    mixedMoment B raw20046step0 raw20046step0Labels = mixedMoment B raw20046step1 raw20046step1Labels := by
      have hz : ∀ j, raw20046step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20046step1 = (fun i j => raw20046step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20046step1 raw20046step0; decide +kernel
      have hl : raw20046step1Labels = raw20046step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20046step0 raw20046step0Labels permutation80 hz
    mixedMoment B raw20046step1 raw20046step1Labels = mixedMoment B raw20046step2 raw20046step2Labels := by
      have ha : raw20046step2 = (fun i j => raw20046step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20046step2 raw20046step1; decide +kernel
      have hl : raw20046step2Labels = raw20046step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20046step1 raw20046step1Labels permutation31 permutation2
    mixedMoment B raw20046step2 raw20046step2Labels = mixedMoment B raw20046step3 raw20046step3Labels := by
      have ha : raw20046step3 = -raw20046step2 := by apply Matrix.ext; change ∀ i j, raw20046step3 i j = -(raw20046step2 i j); unfold raw20046step3 raw20046step2; decide +kernel
      have hl : raw20046step3Labels = raw20046step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node540 node540Labels := by rfl

def raw20047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20047Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20047step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20047step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20047step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20047step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw20047step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20047step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw20047step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20047 raw20047Labels = mixedMoment B node735 node735Labels := by
  calc
    mixedMoment B raw20047 raw20047Labels = mixedMoment B raw20047step0 raw20047step0Labels := by
      have hz : ∀ j, raw20047 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20047step0 = (fun i j => raw20047 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20047step0 raw20047; decide +kernel
      have hl : raw20047step0Labels = raw20047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20047 raw20047Labels permutation434 hz
    mixedMoment B raw20047step0 raw20047step0Labels = mixedMoment B raw20047step1 raw20047step1Labels := by
      have hz : ∀ j, raw20047step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20047step1 = (fun i j => raw20047step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20047step1 raw20047step0; decide +kernel
      have hl : raw20047step1Labels = raw20047step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20047step0 raw20047step0Labels permutation56 hz
    mixedMoment B raw20047step1 raw20047step1Labels = mixedMoment B raw20047step2 raw20047step2Labels := by
      have ha : raw20047step2 = (fun i j => raw20047step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20047step2 raw20047step1; decide +kernel
      have hl : raw20047step2Labels = raw20047step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20047step1 raw20047step1Labels permutation31 permutation2
    mixedMoment B raw20047step2 raw20047step2Labels = mixedMoment B raw20047step3 raw20047step3Labels := by
      have ha : raw20047step3 = -raw20047step2 := by apply Matrix.ext; change ∀ i j, raw20047step3 i j = -(raw20047step2 i j); unfold raw20047step3 raw20047step2; decide +kernel
      have hl : raw20047step3Labels = raw20047step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node735 node735Labels := by rfl

def raw20048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20048Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20048step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20048step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![4, 0, -4]]
def raw20048step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20048step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -2, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw20048step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20048step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw20048step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20048 raw20048Labels = mixedMoment B node735 node735Labels := by
  calc
    mixedMoment B raw20048 raw20048Labels = mixedMoment B raw20048step0 raw20048step0Labels := by
      have hz : ∀ j, raw20048 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20048step0 = (fun i j => raw20048 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20048step0 raw20048; decide +kernel
      have hl : raw20048step0Labels = raw20048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20048 raw20048Labels permutation346 hz
    mixedMoment B raw20048step0 raw20048step0Labels = mixedMoment B raw20048step1 raw20048step1Labels := by
      have hz : ∀ j, raw20048step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20048step1 = (fun i j => raw20048step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20048step1 raw20048step0; decide +kernel
      have hl : raw20048step1Labels = raw20048step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20048step0 raw20048step0Labels permutation56 hz
    mixedMoment B raw20048step1 raw20048step1Labels = mixedMoment B raw20048step2 raw20048step2Labels := by
      have ha : raw20048step2 = (fun i j => raw20048step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20048step2 raw20048step1; decide +kernel
      have hl : raw20048step2Labels = raw20048step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20048step1 raw20048step1Labels permutation31 permutation2
    mixedMoment B raw20048step2 raw20048step2Labels = mixedMoment B raw20048step3 raw20048step3Labels := by
      have ha : raw20048step3 = -raw20048step2 := by apply Matrix.ext; change ∀ i j, raw20048step3 i j = -(raw20048step2 i j); unfold raw20048step3 raw20048step2; decide +kernel
      have hl : raw20048step3Labels = raw20048step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node735 node735Labels := by rfl

def raw20049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 1, -4]]
def raw20049Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, 1, -4]]
def raw20049step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20049step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![3, 1, -4]]
def raw20049step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20049step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw20049step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20049 raw20049Labels = mixedMoment B node1077 node1077Labels := by
  calc
    mixedMoment B raw20049 raw20049Labels = mixedMoment B raw20049step0 raw20049step0Labels := by
      have hz : ∀ j, raw20049 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20049step0 = (fun i j => raw20049 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20049step0 raw20049; decide +kernel
      have hl : raw20049step0Labels = raw20049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20049 raw20049Labels permutation434 hz
    mixedMoment B raw20049step0 raw20049step0Labels = mixedMoment B raw20049step1 raw20049step1Labels := by
      have hz : ∀ j, raw20049step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20049step1 = (fun i j => raw20049step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20049step1 raw20049step0; decide +kernel
      have hl : raw20049step1Labels = raw20049step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20049step0 raw20049step0Labels permutation80 hz
    mixedMoment B raw20049step1 raw20049step1Labels = mixedMoment B raw20049step2 raw20049step2Labels := by
      have hz : ∀ j, raw20049step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20049step2 = (fun i j => raw20049step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20049step2 raw20049step1; decide +kernel
      have hl : raw20049step2Labels = raw20049step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20049step1 raw20049step1Labels permutation14 hz
    _ = mixedMoment B node1077 node1077Labels := by rfl

def raw20050 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw20050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw20050step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20050step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw20050step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20050step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![4, 0, -4]]
def raw20050step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20050step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![4, 0, -4]]
def raw20050step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20050 raw20050Labels = mixedMoment B node4215 node4215Labels := by
  calc
    mixedMoment B raw20050 raw20050Labels = mixedMoment B raw20050step0 raw20050step0Labels := by
      have hz : ∀ j, raw20050 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20050step0 = (fun i j => raw20050 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20050step0 raw20050; decide +kernel
      have hl : raw20050step0Labels = raw20050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20050 raw20050Labels permutation434 hz
    mixedMoment B raw20050step0 raw20050step0Labels = mixedMoment B raw20050step1 raw20050step1Labels := by
      have hz : ∀ j, raw20050step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20050step1 = (fun i j => raw20050step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20050step1 raw20050step0; decide +kernel
      have hl : raw20050step1Labels = raw20050step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20050step0 raw20050step0Labels permutation80 hz
    mixedMoment B raw20050step1 raw20050step1Labels = mixedMoment B raw20050step2 raw20050step2Labels := by
      have ha : raw20050step2 = (fun i j => raw20050step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20050step2 raw20050step1; decide +kernel
      have hl : raw20050step2Labels = raw20050step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20050step1 raw20050step1Labels permutation29 permutation4
    mixedMoment B raw20050step2 raw20050step2Labels = mixedMoment B raw20050step3 raw20050step3Labels := by
      have ha : raw20050step3 = raw20050step2 := by apply Matrix.ext; unfold raw20050step3 raw20050step2; decide +kernel
      have hl : raw20050step2Labels = labelEmbedding7 ∘ raw20050step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20050step2 raw20050step2Labels raw20050step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4215 node4215Labels := by rfl

def raw20051 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw20051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw20051step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw20051step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20051step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw20051step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20051 raw20051Labels = mixedMoment B node4208 node4208Labels := by
  calc
    mixedMoment B raw20051 raw20051Labels = mixedMoment B raw20051step0 raw20051step0Labels := by
      have hz : ∀ j, raw20051 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20051step0 = (fun i j => raw20051 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20051step0 raw20051; decide +kernel
      have hl : raw20051step0Labels = raw20051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20051 raw20051Labels permutation434 hz
    mixedMoment B raw20051step0 raw20051step0Labels = mixedMoment B raw20051step1 raw20051step1Labels := by
      have ha : raw20051step1 = (fun i j => raw20051step0 (permutation137 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20051step1 raw20051step0; decide +kernel
      have hl : raw20051step1Labels = raw20051step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20051step0 raw20051step0Labels permutation137 permutation4
    mixedMoment B raw20051step1 raw20051step1Labels = mixedMoment B raw20051step2 raw20051step2Labels := by
      have ha : raw20051step2 = raw20051step1 := by apply Matrix.ext; unfold raw20051step2 raw20051step1; decide +kernel
      have hl : raw20051step1Labels = labelEmbedding7 ∘ raw20051step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20051step1 raw20051step1Labels raw20051step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4208 node4208Labels := by rfl

def raw20052 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw20052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw20052step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw20052step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw20052step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20052 raw20052Labels = mixedMoment B node4208 node4208Labels := by
  calc
    mixedMoment B raw20052 raw20052Labels = mixedMoment B raw20052step0 raw20052step0Labels := by
      have hz : ∀ j, raw20052 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20052step0 = (fun i j => raw20052 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20052step0 raw20052; decide +kernel
      have hl : raw20052step0Labels = raw20052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20052 raw20052Labels permutation346 hz
    mixedMoment B raw20052step0 raw20052step0Labels = mixedMoment B raw20052step1 raw20052step1Labels := by
      have ha : raw20052step1 = (fun i j => raw20052step0 (permutation137 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20052step1 raw20052step0; decide +kernel
      have hl : raw20052step1Labels = raw20052step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20052step0 raw20052step0Labels permutation137 permutation4
    mixedMoment B raw20052step1 raw20052step1Labels = mixedMoment B raw20052step2 raw20052step2Labels := by
      have ha : raw20052step2 = raw20052step1 := by apply Matrix.ext; unfold raw20052step2 raw20052step1; decide +kernel
      have hl : raw20052step1Labels = labelEmbedding7 ∘ raw20052step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20052step1 raw20052step1Labels raw20052step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4208 node4208Labels := by rfl

def raw20053 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw20053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw20053step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw20053step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20053step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -2, 0], ![3, 1, -4]]
def raw20053step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20053step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -2, 0], ![3, 1, -4]]
def raw20053step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20053 raw20053Labels = mixedMoment B node4226 node4226Labels := by
  calc
    mixedMoment B raw20053 raw20053Labels = mixedMoment B raw20053step0 raw20053step0Labels := by
      have hz : ∀ j, raw20053 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20053step0 = (fun i j => raw20053 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20053step0 raw20053; decide +kernel
      have hl : raw20053step0Labels = raw20053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20053 raw20053Labels permutation434 hz
    mixedMoment B raw20053step0 raw20053step0Labels = mixedMoment B raw20053step1 raw20053step1Labels := by
      have hz : ∀ j, raw20053step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20053step1 = (fun i j => raw20053step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20053step1 raw20053step0; decide +kernel
      have hl : raw20053step1Labels = raw20053step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20053step0 raw20053step0Labels permutation80 hz
    mixedMoment B raw20053step1 raw20053step1Labels = mixedMoment B raw20053step2 raw20053step2Labels := by
      have ha : raw20053step2 = (fun i j => raw20053step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20053step2 raw20053step1; decide +kernel
      have hl : raw20053step2Labels = raw20053step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20053step1 raw20053step1Labels permutation29 permutation4
    mixedMoment B raw20053step2 raw20053step2Labels = mixedMoment B raw20053step3 raw20053step3Labels := by
      have ha : raw20053step3 = raw20053step2 := by apply Matrix.ext; unfold raw20053step3 raw20053step2; decide +kernel
      have hl : raw20053step2Labels = labelEmbedding7 ∘ raw20053step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20053step2 raw20053step2Labels raw20053step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4226 node4226Labels := by rfl

def raw20054 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw20054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw20054step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20054step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw20054step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20054step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![4, 0, -4]]
def raw20054step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20054step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![4, 0, -4]]
def raw20054step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20054 raw20054Labels = mixedMoment B node4215 node4215Labels := by
  calc
    mixedMoment B raw20054 raw20054Labels = mixedMoment B raw20054step0 raw20054step0Labels := by
      have hz : ∀ j, raw20054 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20054step0 = (fun i j => raw20054 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20054step0 raw20054; decide +kernel
      have hl : raw20054step0Labels = raw20054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20054 raw20054Labels permutation434 hz
    mixedMoment B raw20054step0 raw20054step0Labels = mixedMoment B raw20054step1 raw20054step1Labels := by
      have hz : ∀ j, raw20054step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20054step1 = (fun i j => raw20054step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20054step1 raw20054step0; decide +kernel
      have hl : raw20054step1Labels = raw20054step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20054step0 raw20054step0Labels permutation56 hz
    mixedMoment B raw20054step1 raw20054step1Labels = mixedMoment B raw20054step2 raw20054step2Labels := by
      have ha : raw20054step2 = (fun i j => raw20054step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20054step2 raw20054step1; decide +kernel
      have hl : raw20054step2Labels = raw20054step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20054step1 raw20054step1Labels permutation29 permutation4
    mixedMoment B raw20054step2 raw20054step2Labels = mixedMoment B raw20054step3 raw20054step3Labels := by
      have ha : raw20054step3 = raw20054step2 := by apply Matrix.ext; unfold raw20054step3 raw20054step2; decide +kernel
      have hl : raw20054step2Labels = labelEmbedding7 ∘ raw20054step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20054step2 raw20054step2Labels raw20054step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4215 node4215Labels := by rfl

def raw20055 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw20055Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw20055step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw20055step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20055step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw20055step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20055 raw20055Labels = mixedMoment B node4208 node4208Labels := by
  calc
    mixedMoment B raw20055 raw20055Labels = mixedMoment B raw20055step0 raw20055step0Labels := by
      have hz : ∀ j, raw20055 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20055step0 = (fun i j => raw20055 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20055step0 raw20055; decide +kernel
      have hl : raw20055step0Labels = raw20055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20055 raw20055Labels permutation434 hz
    mixedMoment B raw20055step0 raw20055step0Labels = mixedMoment B raw20055step1 raw20055step1Labels := by
      have ha : raw20055step1 = (fun i j => raw20055step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20055step1 raw20055step0; decide +kernel
      have hl : raw20055step1Labels = raw20055step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20055step0 raw20055step0Labels permutation143 permutation4
    mixedMoment B raw20055step1 raw20055step1Labels = mixedMoment B raw20055step2 raw20055step2Labels := by
      have ha : raw20055step2 = raw20055step1 := by apply Matrix.ext; unfold raw20055step2 raw20055step1; decide +kernel
      have hl : raw20055step1Labels = labelEmbedding7 ∘ raw20055step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20055step1 raw20055step1Labels raw20055step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4208 node4208Labels := by rfl

def raw20056 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw20056Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw20056step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw20056step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20056step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw20056step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20056 raw20056Labels = mixedMoment B node4208 node4208Labels := by
  calc
    mixedMoment B raw20056 raw20056Labels = mixedMoment B raw20056step0 raw20056step0Labels := by
      have hz : ∀ j, raw20056 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20056step0 = (fun i j => raw20056 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20056step0 raw20056; decide +kernel
      have hl : raw20056step0Labels = raw20056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20056 raw20056Labels permutation265 hz
    mixedMoment B raw20056step0 raw20056step0Labels = mixedMoment B raw20056step1 raw20056step1Labels := by
      have ha : raw20056step1 = (fun i j => raw20056step0 (permutation137 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20056step1 raw20056step0; decide +kernel
      have hl : raw20056step1Labels = raw20056step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20056step0 raw20056step0Labels permutation137 permutation4
    mixedMoment B raw20056step1 raw20056step1Labels = mixedMoment B raw20056step2 raw20056step2Labels := by
      have ha : raw20056step2 = raw20056step1 := by apply Matrix.ext; unfold raw20056step2 raw20056step1; decide +kernel
      have hl : raw20056step1Labels = labelEmbedding7 ∘ raw20056step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20056step1 raw20056step1Labels raw20056step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4208 node4208Labels := by rfl

def raw20057 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw20057Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw20057step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20057step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw20057step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20057step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -2, 0], ![3, 1, -4]]
def raw20057step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20057step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -2, 0], ![3, 1, -4]]
def raw20057step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20057 raw20057Labels = mixedMoment B node4226 node4226Labels := by
  calc
    mixedMoment B raw20057 raw20057Labels = mixedMoment B raw20057step0 raw20057step0Labels := by
      have hz : ∀ j, raw20057 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20057step0 = (fun i j => raw20057 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20057step0 raw20057; decide +kernel
      have hl : raw20057step0Labels = raw20057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20057 raw20057Labels permutation434 hz
    mixedMoment B raw20057step0 raw20057step0Labels = mixedMoment B raw20057step1 raw20057step1Labels := by
      have hz : ∀ j, raw20057step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20057step1 = (fun i j => raw20057step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20057step1 raw20057step0; decide +kernel
      have hl : raw20057step1Labels = raw20057step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20057step0 raw20057step0Labels permutation56 hz
    mixedMoment B raw20057step1 raw20057step1Labels = mixedMoment B raw20057step2 raw20057step2Labels := by
      have ha : raw20057step2 = (fun i j => raw20057step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20057step2 raw20057step1; decide +kernel
      have hl : raw20057step2Labels = raw20057step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20057step1 raw20057step1Labels permutation29 permutation4
    mixedMoment B raw20057step2 raw20057step2Labels = mixedMoment B raw20057step3 raw20057step3Labels := by
      have ha : raw20057step3 = raw20057step2 := by apply Matrix.ext; unfold raw20057step3 raw20057step2; decide +kernel
      have hl : raw20057step2Labels = labelEmbedding7 ∘ raw20057step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20057step2 raw20057step2Labels raw20057step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4226 node4226Labels := by rfl

def raw20058 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw20058Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw20058step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20058step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw20058step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20058step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![4, 0, -4]]
def raw20058step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20058step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![4, 0, -4]]
def raw20058step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20058 raw20058Labels = mixedMoment B node4215 node4215Labels := by
  calc
    mixedMoment B raw20058 raw20058Labels = mixedMoment B raw20058step0 raw20058step0Labels := by
      have hz : ∀ j, raw20058 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20058step0 = (fun i j => raw20058 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20058step0 raw20058; decide +kernel
      have hl : raw20058step0Labels = raw20058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20058 raw20058Labels permutation346 hz
    mixedMoment B raw20058step0 raw20058step0Labels = mixedMoment B raw20058step1 raw20058step1Labels := by
      have hz : ∀ j, raw20058step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20058step1 = (fun i j => raw20058step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20058step1 raw20058step0; decide +kernel
      have hl : raw20058step1Labels = raw20058step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20058step0 raw20058step0Labels permutation56 hz
    mixedMoment B raw20058step1 raw20058step1Labels = mixedMoment B raw20058step2 raw20058step2Labels := by
      have ha : raw20058step2 = (fun i j => raw20058step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20058step2 raw20058step1; decide +kernel
      have hl : raw20058step2Labels = raw20058step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20058step1 raw20058step1Labels permutation29 permutation4
    mixedMoment B raw20058step2 raw20058step2Labels = mixedMoment B raw20058step3 raw20058step3Labels := by
      have ha : raw20058step3 = raw20058step2 := by apply Matrix.ext; unfold raw20058step3 raw20058step2; decide +kernel
      have hl : raw20058step2Labels = labelEmbedding7 ∘ raw20058step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20058step2 raw20058step2Labels raw20058step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4215 node4215Labels := by rfl

def raw20059 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw20059Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw20059step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw20059step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20059step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw20059step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20059 raw20059Labels = mixedMoment B node4208 node4208Labels := by
  calc
    mixedMoment B raw20059 raw20059Labels = mixedMoment B raw20059step0 raw20059step0Labels := by
      have hz : ∀ j, raw20059 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20059step0 = (fun i j => raw20059 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20059step0 raw20059; decide +kernel
      have hl : raw20059step0Labels = raw20059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20059 raw20059Labels permutation346 hz
    mixedMoment B raw20059step0 raw20059step0Labels = mixedMoment B raw20059step1 raw20059step1Labels := by
      have ha : raw20059step1 = (fun i j => raw20059step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20059step1 raw20059step0; decide +kernel
      have hl : raw20059step1Labels = raw20059step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20059step0 raw20059step0Labels permutation143 permutation4
    mixedMoment B raw20059step1 raw20059step1Labels = mixedMoment B raw20059step2 raw20059step2Labels := by
      have ha : raw20059step2 = raw20059step1 := by apply Matrix.ext; unfold raw20059step2 raw20059step1; decide +kernel
      have hl : raw20059step1Labels = labelEmbedding7 ∘ raw20059step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20059step1 raw20059step1Labels raw20059step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4208 node4208Labels := by rfl

def raw20060 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw20060Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -4, 4]]
def raw20060step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw20060step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20060step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw20060step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20060 raw20060Labels = mixedMoment B node4208 node4208Labels := by
  calc
    mixedMoment B raw20060 raw20060Labels = mixedMoment B raw20060step0 raw20060step0Labels := by
      have hz : ∀ j, raw20060 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20060step0 = (fun i j => raw20060 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20060step0 raw20060; decide +kernel
      have hl : raw20060step0Labels = raw20060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20060 raw20060Labels permutation265 hz
    mixedMoment B raw20060step0 raw20060step0Labels = mixedMoment B raw20060step1 raw20060step1Labels := by
      have ha : raw20060step1 = (fun i j => raw20060step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20060step1 raw20060step0; decide +kernel
      have hl : raw20060step1Labels = raw20060step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20060step0 raw20060step0Labels permutation143 permutation4
    mixedMoment B raw20060step1 raw20060step1Labels = mixedMoment B raw20060step2 raw20060step2Labels := by
      have ha : raw20060step2 = raw20060step1 := by apply Matrix.ext; unfold raw20060step2 raw20060step1; decide +kernel
      have hl : raw20060step1Labels = labelEmbedding7 ∘ raw20060step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20060step1 raw20060step1Labels raw20060step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4208 node4208Labels := by rfl

def raw20061 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw20061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw20061step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20061step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -4, 4]]
def raw20061step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20061step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -2, 0], ![3, 1, -4]]
def raw20061step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20061step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -2, 0], ![3, 1, -4]]
def raw20061step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20061 raw20061Labels = mixedMoment B node4226 node4226Labels := by
  calc
    mixedMoment B raw20061 raw20061Labels = mixedMoment B raw20061step0 raw20061step0Labels := by
      have hz : ∀ j, raw20061 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20061step0 = (fun i j => raw20061 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20061step0 raw20061; decide +kernel
      have hl : raw20061step0Labels = raw20061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20061 raw20061Labels permutation346 hz
    mixedMoment B raw20061step0 raw20061step0Labels = mixedMoment B raw20061step1 raw20061step1Labels := by
      have hz : ∀ j, raw20061step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20061step1 = (fun i j => raw20061step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20061step1 raw20061step0; decide +kernel
      have hl : raw20061step1Labels = raw20061step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20061step0 raw20061step0Labels permutation56 hz
    mixedMoment B raw20061step1 raw20061step1Labels = mixedMoment B raw20061step2 raw20061step2Labels := by
      have ha : raw20061step2 = (fun i j => raw20061step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20061step2 raw20061step1; decide +kernel
      have hl : raw20061step2Labels = raw20061step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20061step1 raw20061step1Labels permutation29 permutation4
    mixedMoment B raw20061step2 raw20061step2Labels = mixedMoment B raw20061step3 raw20061step3Labels := by
      have ha : raw20061step3 = raw20061step2 := by apply Matrix.ext; unfold raw20061step3 raw20061step2; decide +kernel
      have hl : raw20061step2Labels = labelEmbedding7 ∘ raw20061step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20061step2 raw20061step2Labels raw20061step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4226 node4226Labels := by rfl

def raw20062 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -5, 4]]
def raw20062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -5, 4]]
def raw20062step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20062step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -5, 4]]
def raw20062step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20062step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -5, 4]]
def raw20062step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20062step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![4, 0, -4]]
def raw20062step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20062step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![4, 0, -4]]
def raw20062step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20062 raw20062Labels = mixedMoment B node4124 node4124Labels := by
  calc
    mixedMoment B raw20062 raw20062Labels = mixedMoment B raw20062step0 raw20062step0Labels := by
      have hz : ∀ j, raw20062 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20062step0 = (fun i j => raw20062 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20062step0 raw20062; decide +kernel
      have hl : raw20062step0Labels = raw20062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20062 raw20062Labels permutation434 hz
    mixedMoment B raw20062step0 raw20062step0Labels = mixedMoment B raw20062step1 raw20062step1Labels := by
      have hz : ∀ j, raw20062step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20062step1 = (fun i j => raw20062step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20062step1 raw20062step0; decide +kernel
      have hl : raw20062step1Labels = raw20062step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20062step0 raw20062step0Labels permutation80 hz
    mixedMoment B raw20062step1 raw20062step1Labels = mixedMoment B raw20062step2 raw20062step2Labels := by
      have hz : ∀ j, raw20062step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20062step2 = (fun i j => raw20062step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20062step2 raw20062step1; decide +kernel
      have hl : raw20062step2Labels = raw20062step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20062step1 raw20062step1Labels permutation14 hz
    mixedMoment B raw20062step2 raw20062step2Labels = mixedMoment B raw20062step3 raw20062step3Labels := by
      have ha : raw20062step3 = (fun i j => raw20062step2 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20062step3 raw20062step2; decide +kernel
      have hl : raw20062step3Labels = raw20062step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20062step2 raw20062step2Labels permutation7 permutation4
    mixedMoment B raw20062step3 raw20062step3Labels = mixedMoment B raw20062step4 raw20062step4Labels := by
      have ha : raw20062step4 = raw20062step3 := by apply Matrix.ext; unfold raw20062step4 raw20062step3; decide +kernel
      have hl : raw20062step3Labels = labelEmbedding7 ∘ raw20062step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20062step3 raw20062step3Labels raw20062step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4124 node4124Labels := by rfl

def raw20063 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -5, 4]]
def raw20063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -5, 4]]
def raw20063step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20063step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -5, 4]]
def raw20063step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20063step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw20063step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20063step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw20063step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20063 raw20063Labels = mixedMoment B node4116 node4116Labels := by
  calc
    mixedMoment B raw20063 raw20063Labels = mixedMoment B raw20063step0 raw20063step0Labels := by
      have hz : ∀ j, raw20063 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20063step0 = (fun i j => raw20063 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20063step0 raw20063; decide +kernel
      have hl : raw20063step0Labels = raw20063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20063 raw20063Labels permutation434 hz
    mixedMoment B raw20063step0 raw20063step0Labels = mixedMoment B raw20063step1 raw20063step1Labels := by
      have hz : ∀ j, raw20063step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20063step1 = (fun i j => raw20063step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20063step1 raw20063step0; decide +kernel
      have hl : raw20063step1Labels = raw20063step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20063step0 raw20063step0Labels permutation80 hz
    mixedMoment B raw20063step1 raw20063step1Labels = mixedMoment B raw20063step2 raw20063step2Labels := by
      have ha : raw20063step2 = (fun i j => raw20063step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20063step2 raw20063step1; decide +kernel
      have hl : raw20063step2Labels = raw20063step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20063step1 raw20063step1Labels permutation29 permutation4
    mixedMoment B raw20063step2 raw20063step2Labels = mixedMoment B raw20063step3 raw20063step3Labels := by
      have ha : raw20063step3 = raw20063step2 := by apply Matrix.ext; unfold raw20063step3 raw20063step2; decide +kernel
      have hl : raw20063step2Labels = labelEmbedding7 ∘ raw20063step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20063step2 raw20063step2Labels raw20063step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4116 node4116Labels := by rfl

def raw20064 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -5, 4]]
def raw20064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -5, 4]]
def raw20064step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20064step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -5, 4]]
def raw20064step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20064step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw20064step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20064step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw20064step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20064 raw20064Labels = mixedMoment B node4116 node4116Labels := by
  calc
    mixedMoment B raw20064 raw20064Labels = mixedMoment B raw20064step0 raw20064step0Labels := by
      have hz : ∀ j, raw20064 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20064step0 = (fun i j => raw20064 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20064step0 raw20064; decide +kernel
      have hl : raw20064step0Labels = raw20064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20064 raw20064Labels permutation434 hz
    mixedMoment B raw20064step0 raw20064step0Labels = mixedMoment B raw20064step1 raw20064step1Labels := by
      have hz : ∀ j, raw20064step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20064step1 = (fun i j => raw20064step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20064step1 raw20064step0; decide +kernel
      have hl : raw20064step1Labels = raw20064step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20064step0 raw20064step0Labels permutation56 hz
    mixedMoment B raw20064step1 raw20064step1Labels = mixedMoment B raw20064step2 raw20064step2Labels := by
      have ha : raw20064step2 = (fun i j => raw20064step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20064step2 raw20064step1; decide +kernel
      have hl : raw20064step2Labels = raw20064step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20064step1 raw20064step1Labels permutation29 permutation4
    mixedMoment B raw20064step2 raw20064step2Labels = mixedMoment B raw20064step3 raw20064step3Labels := by
      have ha : raw20064step3 = raw20064step2 := by apply Matrix.ext; unfold raw20064step3 raw20064step2; decide +kernel
      have hl : raw20064step2Labels = labelEmbedding7 ∘ raw20064step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20064step2 raw20064step2Labels raw20064step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4116 node4116Labels := by rfl

def raw20065 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -5, 4]]
def raw20065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -5, 4]]
def raw20065step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20065step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -5, 4]]
def raw20065step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20065step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw20065step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20065step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw20065step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20065 raw20065Labels = mixedMoment B node4116 node4116Labels := by
  calc
    mixedMoment B raw20065 raw20065Labels = mixedMoment B raw20065step0 raw20065step0Labels := by
      have hz : ∀ j, raw20065 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20065step0 = (fun i j => raw20065 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20065step0 raw20065; decide +kernel
      have hl : raw20065step0Labels = raw20065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20065 raw20065Labels permutation346 hz
    mixedMoment B raw20065step0 raw20065step0Labels = mixedMoment B raw20065step1 raw20065step1Labels := by
      have hz : ∀ j, raw20065step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20065step1 = (fun i j => raw20065step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20065step1 raw20065step0; decide +kernel
      have hl : raw20065step1Labels = raw20065step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20065step0 raw20065step0Labels permutation56 hz
    mixedMoment B raw20065step1 raw20065step1Labels = mixedMoment B raw20065step2 raw20065step2Labels := by
      have ha : raw20065step2 = (fun i j => raw20065step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20065step2 raw20065step1; decide +kernel
      have hl : raw20065step2Labels = raw20065step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20065step1 raw20065step1Labels permutation29 permutation4
    mixedMoment B raw20065step2 raw20065step2Labels = mixedMoment B raw20065step3 raw20065step3Labels := by
      have ha : raw20065step3 = raw20065step2 := by apply Matrix.ext; unfold raw20065step3 raw20065step2; decide +kernel
      have hl : raw20065step2Labels = labelEmbedding7 ∘ raw20065step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20065step2 raw20065step2Labels raw20065step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4116 node4116Labels := by rfl

def raw20066 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -5, 4]]
def raw20066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -5, 4]]
def raw20066step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20066step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 2, 0], ![1, -5, 4]]
def raw20066step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20066step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 2, 0], ![1, -5, 4]]
def raw20066step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20066step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, -2, 0], ![3, 1, -4]]
def raw20066step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw20066step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, -2, 0], ![3, 1, -4]]
def raw20066step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20066 raw20066Labels = mixedMoment B node4135 node4135Labels := by
  calc
    mixedMoment B raw20066 raw20066Labels = mixedMoment B raw20066step0 raw20066step0Labels := by
      have hz : ∀ j, raw20066 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20066step0 = (fun i j => raw20066 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20066step0 raw20066; decide +kernel
      have hl : raw20066step0Labels = raw20066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20066 raw20066Labels permutation434 hz
    mixedMoment B raw20066step0 raw20066step0Labels = mixedMoment B raw20066step1 raw20066step1Labels := by
      have hz : ∀ j, raw20066step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20066step1 = (fun i j => raw20066step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20066step1 raw20066step0; decide +kernel
      have hl : raw20066step1Labels = raw20066step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20066step0 raw20066step0Labels permutation80 hz
    mixedMoment B raw20066step1 raw20066step1Labels = mixedMoment B raw20066step2 raw20066step2Labels := by
      have hz : ∀ j, raw20066step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20066step2 = (fun i j => raw20066step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20066step2 raw20066step1; decide +kernel
      have hl : raw20066step2Labels = raw20066step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20066step1 raw20066step1Labels permutation14 hz
    mixedMoment B raw20066step2 raw20066step2Labels = mixedMoment B raw20066step3 raw20066step3Labels := by
      have ha : raw20066step3 = (fun i j => raw20066step2 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20066step3 raw20066step2; decide +kernel
      have hl : raw20066step3Labels = raw20066step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20066step2 raw20066step2Labels permutation7 permutation4
    mixedMoment B raw20066step3 raw20066step3Labels = mixedMoment B raw20066step4 raw20066step4Labels := by
      have ha : raw20066step4 = raw20066step3 := by apply Matrix.ext; unfold raw20066step4 raw20066step3; decide +kernel
      have hl : raw20066step3Labels = labelEmbedding7 ∘ raw20066step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20066step3 raw20066step3Labels raw20066step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4135 node4135Labels := by rfl

def raw20067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20067Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20067step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20067step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20067step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20067step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20067step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]
def raw20067step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20067 raw20067Labels = mixedMoment B node4060 node4060Labels := by
  calc
    mixedMoment B raw20067 raw20067Labels = mixedMoment B raw20067step0 raw20067step0Labels := by
      have hz : ∀ j, raw20067 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20067step0 = (fun i j => raw20067 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20067step0 raw20067; decide +kernel
      have hl : raw20067step0Labels = raw20067Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20067 raw20067Labels permutation520 hz
    mixedMoment B raw20067step0 raw20067step0Labels = mixedMoment B raw20067step1 raw20067step1Labels := by
      have hz : ∀ j, raw20067step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw20067step1 = (fun i j => raw20067step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw20067step1 raw20067step0; decide +kernel
      have hl : raw20067step1Labels = raw20067step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20067step0 raw20067step0Labels permutation104 hz
    mixedMoment B raw20067step1 raw20067step1Labels = mixedMoment B raw20067step2 raw20067step2Labels := by
      have hz : ∀ j, raw20067step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw20067step2 = (fun i j => raw20067step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw20067step2 raw20067step1; decide +kernel
      have hl : raw20067step2Labels = raw20067step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20067step1 raw20067step1Labels permutation20 hz
    mixedMoment B raw20067step2 raw20067step2Labels = mixedMoment B raw20067step3 raw20067step3Labels := by
      have hz : ∀ i, raw20067step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20067step3 = (fun i j => raw20067step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20067step3 raw20067step2; decide +kernel
      have hl : raw20067step3Labels = (fun j => raw20067step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20067step2 raw20067step2Labels permutation6 hz
    _ = mixedMoment B node4060 node4060Labels := by rfl

def raw20068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20068Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20068step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20068step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20068step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![4, -4]]
def raw20068step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20068step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw20068step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20068 raw20068Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20068 raw20068Labels = mixedMoment B raw20068step0 raw20068step0Labels := by
      have hz : ∀ j, raw20068 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20068step0 = (fun i j => raw20068 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20068step0 raw20068; decide +kernel
      have hl : raw20068step0Labels = raw20068Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20068 raw20068Labels permutation520 hz
    mixedMoment B raw20068step0 raw20068step0Labels = mixedMoment B raw20068step1 raw20068step1Labels := by
      have hz : ∀ j, raw20068step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw20068step1 = (fun i j => raw20068step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw20068step1 raw20068step0; decide +kernel
      have hl : raw20068step1Labels = raw20068step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20068step0 raw20068step0Labels permutation104 hz
    mixedMoment B raw20068step1 raw20068step1Labels = mixedMoment B raw20068step2 raw20068step2Labels := by
      have hz : ∀ i, raw20068step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20068step2 = (fun i j => raw20068step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20068step2 raw20068step1; decide +kernel
      have hl : raw20068step2Labels = (fun j => raw20068step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20068step1 raw20068step1Labels permutation6 hz
    mixedMoment B raw20068step2 raw20068step2Labels = mixedMoment B raw20068step3 raw20068step3Labels := by
      have ha : raw20068step3 = (fun i j => raw20068step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20068step3 raw20068step2; decide +kernel
      have hl : raw20068step3Labels = raw20068step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20068step2 raw20068step2Labels permutation10 permutation0
    _ = mixedMoment B node4066 node4066Labels := by rfl

def raw20069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20069Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20069step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20069step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20069step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20069step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![4, -4]]
def raw20069step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20069step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw20069step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20069 raw20069Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20069 raw20069Labels = mixedMoment B raw20069step0 raw20069step0Labels := by
      have hz : ∀ j, raw20069 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20069step0 = (fun i j => raw20069 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20069step0 raw20069; decide +kernel
      have hl : raw20069step0Labels = raw20069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20069 raw20069Labels permutation520 hz
    mixedMoment B raw20069step0 raw20069step0Labels = mixedMoment B raw20069step1 raw20069step1Labels := by
      have hz : ∀ j, raw20069step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20069step1 = (fun i j => raw20069step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20069step1 raw20069step0; decide +kernel
      have hl : raw20069step1Labels = raw20069step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20069step0 raw20069step0Labels permutation80 hz
    mixedMoment B raw20069step1 raw20069step1Labels = mixedMoment B raw20069step2 raw20069step2Labels := by
      have hz : ∀ i, raw20069step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20069step2 = (fun i j => raw20069step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20069step2 raw20069step1; decide +kernel
      have hl : raw20069step2Labels = (fun j => raw20069step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20069step1 raw20069step1Labels permutation6 hz
    mixedMoment B raw20069step2 raw20069step2Labels = mixedMoment B raw20069step3 raw20069step3Labels := by
      have ha : raw20069step3 = (fun i j => raw20069step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20069step3 raw20069step2; decide +kernel
      have hl : raw20069step3Labels = raw20069step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20069step2 raw20069step2Labels permutation10 permutation0
    _ = mixedMoment B node4066 node4066Labels := by rfl

def raw20070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20070Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20070step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20070step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20070step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20070step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![4, -4]]
def raw20070step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20070step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw20070step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20070 raw20070Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20070 raw20070Labels = mixedMoment B raw20070step0 raw20070step0Labels := by
      have hz : ∀ j, raw20070 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20070step0 = (fun i j => raw20070 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20070step0 raw20070; decide +kernel
      have hl : raw20070step0Labels = raw20070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20070 raw20070Labels permutation434 hz
    mixedMoment B raw20070step0 raw20070step0Labels = mixedMoment B raw20070step1 raw20070step1Labels := by
      have hz : ∀ j, raw20070step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20070step1 = (fun i j => raw20070step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20070step1 raw20070step0; decide +kernel
      have hl : raw20070step1Labels = raw20070step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20070step0 raw20070step0Labels permutation80 hz
    mixedMoment B raw20070step1 raw20070step1Labels = mixedMoment B raw20070step2 raw20070step2Labels := by
      have hz : ∀ i, raw20070step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20070step2 = (fun i j => raw20070step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20070step2 raw20070step1; decide +kernel
      have hl : raw20070step2Labels = (fun j => raw20070step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20070step1 raw20070step1Labels permutation6 hz
    mixedMoment B raw20070step2 raw20070step2Labels = mixedMoment B raw20070step3 raw20070step3Labels := by
      have ha : raw20070step3 = (fun i j => raw20070step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20070step3 raw20070step2; decide +kernel
      have hl : raw20070step3Labels = raw20070step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20070step2 raw20070step2Labels permutation10 permutation0
    _ = mixedMoment B node4066 node4066Labels := by rfl

def raw20071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20071Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20071step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20071step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20071step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20071step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20071step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20071step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]
def raw20071step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20071 raw20071Labels = mixedMoment B node4060 node4060Labels := by
  calc
    mixedMoment B raw20071 raw20071Labels = mixedMoment B raw20071step0 raw20071step0Labels := by
      have hz : ∀ j, raw20071 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20071step0 = (fun i j => raw20071 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20071step0 raw20071; decide +kernel
      have hl : raw20071step0Labels = raw20071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20071 raw20071Labels permutation520 hz
    mixedMoment B raw20071step0 raw20071step0Labels = mixedMoment B raw20071step1 raw20071step1Labels := by
      have hz : ∀ j, raw20071step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw20071step1 = (fun i j => raw20071step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw20071step1 raw20071step0; decide +kernel
      have hl : raw20071step1Labels = raw20071step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20071step0 raw20071step0Labels permutation104 hz
    mixedMoment B raw20071step1 raw20071step1Labels = mixedMoment B raw20071step2 raw20071step2Labels := by
      have hz : ∀ j, raw20071step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20071step2 = (fun i j => raw20071step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20071step2 raw20071step1; decide +kernel
      have hl : raw20071step2Labels = raw20071step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20071step1 raw20071step1Labels permutation14 hz
    mixedMoment B raw20071step2 raw20071step2Labels = mixedMoment B raw20071step3 raw20071step3Labels := by
      have hz : ∀ i, raw20071step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20071step3 = (fun i j => raw20071step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20071step3 raw20071step2; decide +kernel
      have hl : raw20071step3Labels = (fun j => raw20071step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20071step2 raw20071step2Labels permutation6 hz
    _ = mixedMoment B node4060 node4060Labels := by rfl

def raw20072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20072Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20072step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20072step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20072step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20072step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw20072step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20072 raw20072Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20072 raw20072Labels = mixedMoment B raw20072step0 raw20072step0Labels := by
      have hz : ∀ j, raw20072 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20072step0 = (fun i j => raw20072 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20072step0 raw20072; decide +kernel
      have hl : raw20072step0Labels = raw20072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20072 raw20072Labels permutation520 hz
    mixedMoment B raw20072step0 raw20072step0Labels = mixedMoment B raw20072step1 raw20072step1Labels := by
      have hz : ∀ j, raw20072step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw20072step1 = (fun i j => raw20072step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw20072step1 raw20072step0; decide +kernel
      have hl : raw20072step1Labels = raw20072step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20072step0 raw20072step0Labels permutation104 hz
    mixedMoment B raw20072step1 raw20072step1Labels = mixedMoment B raw20072step2 raw20072step2Labels := by
      have hz : ∀ i, raw20072step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20072step2 = (fun i j => raw20072step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20072step2 raw20072step1; decide +kernel
      have hl : raw20072step2Labels = (fun j => raw20072step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20072step1 raw20072step1Labels permutation6 hz
    _ = mixedMoment B node4066 node4066Labels := by rfl

def raw20073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20073Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20073step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20073step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20073step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20073step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![4, -4]]
def raw20073step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20073step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw20073step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20073 raw20073Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20073 raw20073Labels = mixedMoment B raw20073step0 raw20073step0Labels := by
      have hz : ∀ j, raw20073 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20073step0 = (fun i j => raw20073 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20073step0 raw20073; decide +kernel
      have hl : raw20073step0Labels = raw20073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20073 raw20073Labels permutation520 hz
    mixedMoment B raw20073step0 raw20073step0Labels = mixedMoment B raw20073step1 raw20073step1Labels := by
      have hz : ∀ j, raw20073step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20073step1 = (fun i j => raw20073step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20073step1 raw20073step0; decide +kernel
      have hl : raw20073step1Labels = raw20073step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20073step0 raw20073step0Labels permutation56 hz
    mixedMoment B raw20073step1 raw20073step1Labels = mixedMoment B raw20073step2 raw20073step2Labels := by
      have hz : ∀ i, raw20073step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20073step2 = (fun i j => raw20073step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20073step2 raw20073step1; decide +kernel
      have hl : raw20073step2Labels = (fun j => raw20073step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20073step1 raw20073step1Labels permutation6 hz
    mixedMoment B raw20073step2 raw20073step2Labels = mixedMoment B raw20073step3 raw20073step3Labels := by
      have ha : raw20073step3 = (fun i j => raw20073step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20073step3 raw20073step2; decide +kernel
      have hl : raw20073step3Labels = raw20073step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20073step2 raw20073step2Labels permutation10 permutation0
    _ = mixedMoment B node4066 node4066Labels := by rfl

def raw20074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20074Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20074step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20074step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20074step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20074step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![4, -4]]
def raw20074step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20074step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw20074step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20074 raw20074Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20074 raw20074Labels = mixedMoment B raw20074step0 raw20074step0Labels := by
      have hz : ∀ j, raw20074 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20074step0 = (fun i j => raw20074 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20074step0 raw20074; decide +kernel
      have hl : raw20074step0Labels = raw20074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20074 raw20074Labels permutation434 hz
    mixedMoment B raw20074step0 raw20074step0Labels = mixedMoment B raw20074step1 raw20074step1Labels := by
      have hz : ∀ j, raw20074step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20074step1 = (fun i j => raw20074step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20074step1 raw20074step0; decide +kernel
      have hl : raw20074step1Labels = raw20074step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20074step0 raw20074step0Labels permutation56 hz
    mixedMoment B raw20074step1 raw20074step1Labels = mixedMoment B raw20074step2 raw20074step2Labels := by
      have hz : ∀ i, raw20074step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20074step2 = (fun i j => raw20074step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20074step2 raw20074step1; decide +kernel
      have hl : raw20074step2Labels = (fun j => raw20074step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20074step1 raw20074step1Labels permutation6 hz
    mixedMoment B raw20074step2 raw20074step2Labels = mixedMoment B raw20074step3 raw20074step3Labels := by
      have ha : raw20074step3 = (fun i j => raw20074step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20074step3 raw20074step2; decide +kernel
      have hl : raw20074step3Labels = raw20074step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20074step2 raw20074step2Labels permutation10 permutation0
    _ = mixedMoment B node4066 node4066Labels := by rfl

def raw20075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20075Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20075step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20075step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20075step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20075step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20075step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20075step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]
def raw20075step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20075 raw20075Labels = mixedMoment B node4060 node4060Labels := by
  calc
    mixedMoment B raw20075 raw20075Labels = mixedMoment B raw20075step0 raw20075step0Labels := by
      have hz : ∀ j, raw20075 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20075step0 = (fun i j => raw20075 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20075step0 raw20075; decide +kernel
      have hl : raw20075step0Labels = raw20075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20075 raw20075Labels permutation520 hz
    mixedMoment B raw20075step0 raw20075step0Labels = mixedMoment B raw20075step1 raw20075step1Labels := by
      have hz : ∀ j, raw20075step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20075step1 = (fun i j => raw20075step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20075step1 raw20075step0; decide +kernel
      have hl : raw20075step1Labels = raw20075step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20075step0 raw20075step0Labels permutation80 hz
    mixedMoment B raw20075step1 raw20075step1Labels = mixedMoment B raw20075step2 raw20075step2Labels := by
      have hz : ∀ j, raw20075step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20075step2 = (fun i j => raw20075step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20075step2 raw20075step1; decide +kernel
      have hl : raw20075step2Labels = raw20075step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20075step1 raw20075step1Labels permutation14 hz
    mixedMoment B raw20075step2 raw20075step2Labels = mixedMoment B raw20075step3 raw20075step3Labels := by
      have hz : ∀ i, raw20075step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20075step3 = (fun i j => raw20075step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20075step3 raw20075step2; decide +kernel
      have hl : raw20075step3Labels = (fun j => raw20075step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20075step2 raw20075step2Labels permutation6 hz
    _ = mixedMoment B node4060 node4060Labels := by rfl

def raw20076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20076Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20076step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20076step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20076step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20076step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw20076step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20076 raw20076Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20076 raw20076Labels = mixedMoment B raw20076step0 raw20076step0Labels := by
      have hz : ∀ j, raw20076 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20076step0 = (fun i j => raw20076 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20076step0 raw20076; decide +kernel
      have hl : raw20076step0Labels = raw20076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20076 raw20076Labels permutation520 hz
    mixedMoment B raw20076step0 raw20076step0Labels = mixedMoment B raw20076step1 raw20076step1Labels := by
      have hz : ∀ j, raw20076step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20076step1 = (fun i j => raw20076step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20076step1 raw20076step0; decide +kernel
      have hl : raw20076step1Labels = raw20076step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20076step0 raw20076step0Labels permutation80 hz
    mixedMoment B raw20076step1 raw20076step1Labels = mixedMoment B raw20076step2 raw20076step2Labels := by
      have hz : ∀ i, raw20076step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20076step2 = (fun i j => raw20076step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20076step2 raw20076step1; decide +kernel
      have hl : raw20076step2Labels = (fun j => raw20076step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20076step1 raw20076step1Labels permutation6 hz
    _ = mixedMoment B node4066 node4066Labels := by rfl

def raw20077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![4, -4, 0]]
def raw20077Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20077step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20077step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20077step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20077step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw20077step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20077 raw20077Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20077 raw20077Labels = mixedMoment B raw20077step0 raw20077step0Labels := by
      have hz : ∀ j, raw20077 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20077step0 = (fun i j => raw20077 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20077step0 raw20077; decide +kernel
      have hl : raw20077step0Labels = raw20077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20077 raw20077Labels permutation520 hz
    mixedMoment B raw20077step0 raw20077step0Labels = mixedMoment B raw20077step1 raw20077step1Labels := by
      have hz : ∀ j, raw20077step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20077step1 = (fun i j => raw20077step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20077step1 raw20077step0; decide +kernel
      have hl : raw20077step1Labels = raw20077step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20077step0 raw20077step0Labels permutation56 hz
    mixedMoment B raw20077step1 raw20077step1Labels = mixedMoment B raw20077step2 raw20077step2Labels := by
      have hz : ∀ i, raw20077step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20077step2 = (fun i j => raw20077step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20077step2 raw20077step1; decide +kernel
      have hl : raw20077step2Labels = (fun j => raw20077step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20077step1 raw20077step1Labels permutation6 hz
    _ = mixedMoment B node4066 node4066Labels := by rfl

def raw20078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20078Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20078step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20078step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![4, -4, 0]]
def raw20078step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20078step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![4, -4]]
def raw20078step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20078step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw20078step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20078 raw20078Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20078 raw20078Labels = mixedMoment B raw20078step0 raw20078step0Labels := by
      have hz : ∀ j, raw20078 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20078step0 = (fun i j => raw20078 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20078step0 raw20078; decide +kernel
      have hl : raw20078step0Labels = raw20078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20078 raw20078Labels permutation346 hz
    mixedMoment B raw20078step0 raw20078step0Labels = mixedMoment B raw20078step1 raw20078step1Labels := by
      have hz : ∀ j, raw20078step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20078step1 = (fun i j => raw20078step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20078step1 raw20078step0; decide +kernel
      have hl : raw20078step1Labels = raw20078step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20078step0 raw20078step0Labels permutation56 hz
    mixedMoment B raw20078step1 raw20078step1Labels = mixedMoment B raw20078step2 raw20078step2Labels := by
      have hz : ∀ i, raw20078step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20078step2 = (fun i j => raw20078step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20078step2 raw20078step1; decide +kernel
      have hl : raw20078step2Labels = (fun j => raw20078step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20078step1 raw20078step1Labels permutation6 hz
    mixedMoment B raw20078step2 raw20078step2Labels = mixedMoment B raw20078step3 raw20078step3Labels := by
      have ha : raw20078step3 = (fun i j => raw20078step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20078step3 raw20078step2; decide +kernel
      have hl : raw20078step3Labels = raw20078step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20078step2 raw20078step2Labels permutation10 permutation0
    _ = mixedMoment B node4066 node4066Labels := by rfl

def raw20079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20079Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20079step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20079step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20079step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20079step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20079step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20079step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]
def raw20079step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20079 raw20079Labels = mixedMoment B node4060 node4060Labels := by
  calc
    mixedMoment B raw20079 raw20079Labels = mixedMoment B raw20079step0 raw20079step0Labels := by
      have hz : ∀ j, raw20079 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20079step0 = (fun i j => raw20079 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20079step0 raw20079; decide +kernel
      have hl : raw20079step0Labels = raw20079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20079 raw20079Labels permutation434 hz
    mixedMoment B raw20079step0 raw20079step0Labels = mixedMoment B raw20079step1 raw20079step1Labels := by
      have hz : ∀ j, raw20079step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20079step1 = (fun i j => raw20079step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20079step1 raw20079step0; decide +kernel
      have hl : raw20079step1Labels = raw20079step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20079step0 raw20079step0Labels permutation80 hz
    mixedMoment B raw20079step1 raw20079step1Labels = mixedMoment B raw20079step2 raw20079step2Labels := by
      have hz : ∀ j, raw20079step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20079step2 = (fun i j => raw20079step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20079step2 raw20079step1; decide +kernel
      have hl : raw20079step2Labels = raw20079step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20079step1 raw20079step1Labels permutation14 hz
    mixedMoment B raw20079step2 raw20079step2Labels = mixedMoment B raw20079step3 raw20079step3Labels := by
      have hz : ∀ i, raw20079step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20079step3 = (fun i j => raw20079step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20079step3 raw20079step2; decide +kernel
      have hl : raw20079step3Labels = (fun j => raw20079step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20079step2 raw20079step2Labels permutation6 hz
    _ = mixedMoment B node4060 node4060Labels := by rfl

def raw20080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20080Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20080step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20080step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20080step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20080step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw20080step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20080 raw20080Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20080 raw20080Labels = mixedMoment B raw20080step0 raw20080step0Labels := by
      have hz : ∀ j, raw20080 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20080step0 = (fun i j => raw20080 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20080step0 raw20080; decide +kernel
      have hl : raw20080step0Labels = raw20080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20080 raw20080Labels permutation434 hz
    mixedMoment B raw20080step0 raw20080step0Labels = mixedMoment B raw20080step1 raw20080step1Labels := by
      have hz : ∀ j, raw20080step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20080step1 = (fun i j => raw20080step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20080step1 raw20080step0; decide +kernel
      have hl : raw20080step1Labels = raw20080step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20080step0 raw20080step0Labels permutation80 hz
    mixedMoment B raw20080step1 raw20080step1Labels = mixedMoment B raw20080step2 raw20080step2Labels := by
      have hz : ∀ i, raw20080step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20080step2 = (fun i j => raw20080step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20080step2 raw20080step1; decide +kernel
      have hl : raw20080step2Labels = (fun j => raw20080step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20080step1 raw20080step1Labels permutation6 hz
    _ = mixedMoment B node4066 node4066Labels := by rfl

def raw20081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20081Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20081step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20081step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20081step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20081step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw20081step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20081 raw20081Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20081 raw20081Labels = mixedMoment B raw20081step0 raw20081step0Labels := by
      have hz : ∀ j, raw20081 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20081step0 = (fun i j => raw20081 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20081step0 raw20081; decide +kernel
      have hl : raw20081step0Labels = raw20081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20081 raw20081Labels permutation434 hz
    mixedMoment B raw20081step0 raw20081step0Labels = mixedMoment B raw20081step1 raw20081step1Labels := by
      have hz : ∀ j, raw20081step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20081step1 = (fun i j => raw20081step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20081step1 raw20081step0; decide +kernel
      have hl : raw20081step1Labels = raw20081step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20081step0 raw20081step0Labels permutation56 hz
    mixedMoment B raw20081step1 raw20081step1Labels = mixedMoment B raw20081step2 raw20081step2Labels := by
      have hz : ∀ i, raw20081step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20081step2 = (fun i j => raw20081step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20081step2 raw20081step1; decide +kernel
      have hl : raw20081step2Labels = (fun j => raw20081step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20081step1 raw20081step1Labels permutation6 hz
    _ = mixedMoment B node4066 node4066Labels := by rfl

def raw20082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20082Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20082step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20082step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw20082step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20082step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![4, -4]]
def raw20082step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20082 raw20082Labels = mixedMoment B node4066 node4066Labels := by
  calc
    mixedMoment B raw20082 raw20082Labels = mixedMoment B raw20082step0 raw20082step0Labels := by
      have hz : ∀ j, raw20082 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20082step0 = (fun i j => raw20082 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20082step0 raw20082; decide +kernel
      have hl : raw20082step0Labels = raw20082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20082 raw20082Labels permutation346 hz
    mixedMoment B raw20082step0 raw20082step0Labels = mixedMoment B raw20082step1 raw20082step1Labels := by
      have hz : ∀ j, raw20082step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20082step1 = (fun i j => raw20082step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20082step1 raw20082step0; decide +kernel
      have hl : raw20082step1Labels = raw20082step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20082step0 raw20082step0Labels permutation56 hz
    mixedMoment B raw20082step1 raw20082step1Labels = mixedMoment B raw20082step2 raw20082step2Labels := by
      have hz : ∀ i, raw20082step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20082step2 = (fun i j => raw20082step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20082step2 raw20082step1; decide +kernel
      have hl : raw20082step2Labels = (fun j => raw20082step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20082step1 raw20082step1Labels permutation6 hz
    _ = mixedMoment B node4066 node4066Labels := by rfl

def raw20083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -5, 0]]
def raw20083Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -5, 0]]
def raw20083step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![5, -5, 0]]
def raw20083step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20083step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![5, -5, 0]]
def raw20083step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20083step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 5, 0], ![5, -5, 0]]
def raw20083step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20083step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-5, 5], ![5, -5]]
def raw20083step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20083 raw20083Labels = mixedMoment B node4062 node4062Labels := by
  calc
    mixedMoment B raw20083 raw20083Labels = mixedMoment B raw20083step0 raw20083step0Labels := by
      have hz : ∀ j, raw20083 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20083step0 = (fun i j => raw20083 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20083step0 raw20083; decide +kernel
      have hl : raw20083step0Labels = raw20083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20083 raw20083Labels permutation520 hz
    mixedMoment B raw20083step0 raw20083step0Labels = mixedMoment B raw20083step1 raw20083step1Labels := by
      have hz : ∀ j, raw20083step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw20083step1 = (fun i j => raw20083step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw20083step1 raw20083step0; decide +kernel
      have hl : raw20083step1Labels = raw20083step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20083step0 raw20083step0Labels permutation104 hz
    mixedMoment B raw20083step1 raw20083step1Labels = mixedMoment B raw20083step2 raw20083step2Labels := by
      have hz : ∀ j, raw20083step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw20083step2 = (fun i j => raw20083step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw20083step2 raw20083step1; decide +kernel
      have hl : raw20083step2Labels = raw20083step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20083step1 raw20083step1Labels permutation20 hz
    mixedMoment B raw20083step2 raw20083step2Labels = mixedMoment B raw20083step3 raw20083step3Labels := by
      have hz : ∀ j, raw20083step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw20083step3 = (fun i j => raw20083step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw20083step3 raw20083step2; decide +kernel
      have hl : raw20083step3Labels = raw20083step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20083step2 raw20083step2Labels permutation4 hz
    mixedMoment B raw20083step3 raw20083step3Labels = mixedMoment B raw20083step4 raw20083step4Labels := by
      have hz : ∀ i, raw20083step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20083step4 = (fun i j => raw20083step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20083step4 raw20083step3; decide +kernel
      have hl : raw20083step4Labels = (fun j => raw20083step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20083step3 raw20083step3Labels permutation6 hz
    _ = mixedMoment B node4062 node4062Labels := by rfl

def raw20084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![5, -5, 0]]
def raw20084Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![5, -5, 0]]
def raw20084step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20084step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![5, -5, 0]]
def raw20084step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20084step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![5, -5, 0]]
def raw20084step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20084step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![5, -5]]
def raw20084step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20084step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![5, -5], ![-1, 1], ![-4, 4]]
def raw20084step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20084step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]
def raw20084step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20084 raw20084Labels = mixedMoment B node4060 node4060Labels := by
  calc
    mixedMoment B raw20084 raw20084Labels = mixedMoment B raw20084step0 raw20084step0Labels := by
      have hz : ∀ j, raw20084 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20084step0 = (fun i j => raw20084 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20084step0 raw20084; decide +kernel
      have hl : raw20084step0Labels = raw20084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20084 raw20084Labels permutation520 hz
    mixedMoment B raw20084step0 raw20084step0Labels = mixedMoment B raw20084step1 raw20084step1Labels := by
      have hz : ∀ j, raw20084step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw20084step1 = (fun i j => raw20084step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw20084step1 raw20084step0; decide +kernel
      have hl : raw20084step1Labels = raw20084step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20084step0 raw20084step0Labels permutation104 hz
    mixedMoment B raw20084step1 raw20084step1Labels = mixedMoment B raw20084step2 raw20084step2Labels := by
      have hz : ∀ j, raw20084step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw20084step2 = (fun i j => raw20084step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw20084step2 raw20084step1; decide +kernel
      have hl : raw20084step2Labels = raw20084step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20084step1 raw20084step1Labels permutation20 hz
    mixedMoment B raw20084step2 raw20084step2Labels = mixedMoment B raw20084step3 raw20084step3Labels := by
      have hz : ∀ i, raw20084step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20084step3 = (fun i j => raw20084step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20084step3 raw20084step2; decide +kernel
      have hl : raw20084step3Labels = (fun j => raw20084step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20084step2 raw20084step2Labels permutation6 hz
    mixedMoment B raw20084step3 raw20084step3Labels = mixedMoment B raw20084step4 raw20084step4Labels := by
      have ha : raw20084step4 = (fun i j => raw20084step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20084step4 raw20084step3; decide +kernel
      have hl : raw20084step4Labels = raw20084step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20084step3 raw20084step3Labels permutation7 permutation0
    mixedMoment B raw20084step4 raw20084step4Labels = mixedMoment B raw20084step5 raw20084step5Labels := by
      have ha : raw20084step5 = -raw20084step4 := by apply Matrix.ext; change ∀ i j, raw20084step5 i j = -(raw20084step4 i j); unfold raw20084step5 raw20084step4; decide +kernel
      have hl : raw20084step5Labels = raw20084step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4060 node4060Labels := by rfl

def raw20085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![5, -5, 0]]
def raw20085Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![5, -5, 0]]
def raw20085step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20085step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -5, 0]]
def raw20085step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20085step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![5, -5, 0]]
def raw20085step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20085step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![5, -5]]
def raw20085step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20085step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![5, -5], ![-1, 1], ![-4, 4]]
def raw20085step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20085step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]
def raw20085step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20085 raw20085Labels = mixedMoment B node4060 node4060Labels := by
  calc
    mixedMoment B raw20085 raw20085Labels = mixedMoment B raw20085step0 raw20085step0Labels := by
      have hz : ∀ j, raw20085 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20085step0 = (fun i j => raw20085 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20085step0 raw20085; decide +kernel
      have hl : raw20085step0Labels = raw20085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20085 raw20085Labels permutation520 hz
    mixedMoment B raw20085step0 raw20085step0Labels = mixedMoment B raw20085step1 raw20085step1Labels := by
      have hz : ∀ j, raw20085step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw20085step1 = (fun i j => raw20085step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw20085step1 raw20085step0; decide +kernel
      have hl : raw20085step1Labels = raw20085step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20085step0 raw20085step0Labels permutation104 hz
    mixedMoment B raw20085step1 raw20085step1Labels = mixedMoment B raw20085step2 raw20085step2Labels := by
      have hz : ∀ j, raw20085step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20085step2 = (fun i j => raw20085step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20085step2 raw20085step1; decide +kernel
      have hl : raw20085step2Labels = raw20085step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20085step1 raw20085step1Labels permutation14 hz
    mixedMoment B raw20085step2 raw20085step2Labels = mixedMoment B raw20085step3 raw20085step3Labels := by
      have hz : ∀ i, raw20085step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20085step3 = (fun i j => raw20085step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20085step3 raw20085step2; decide +kernel
      have hl : raw20085step3Labels = (fun j => raw20085step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20085step2 raw20085step2Labels permutation6 hz
    mixedMoment B raw20085step3 raw20085step3Labels = mixedMoment B raw20085step4 raw20085step4Labels := by
      have ha : raw20085step4 = (fun i j => raw20085step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20085step4 raw20085step3; decide +kernel
      have hl : raw20085step4Labels = raw20085step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20085step3 raw20085step3Labels permutation7 permutation0
    mixedMoment B raw20085step4 raw20085step4Labels = mixedMoment B raw20085step5 raw20085step5Labels := by
      have ha : raw20085step5 = -raw20085step4 := by apply Matrix.ext; change ∀ i j, raw20085step5 i j = -(raw20085step4 i j); unfold raw20085step5 raw20085step4; decide +kernel
      have hl : raw20085step5Labels = raw20085step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4060 node4060Labels := by rfl

def raw20086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![5, -5, 0]]
def raw20086Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -5, 0]]
def raw20086step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20086step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -5, 0]]
def raw20086step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20086step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![5, -5, 0]]
def raw20086step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20086step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![5, -5]]
def raw20086step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20086step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![5, -5], ![-1, 1], ![-4, 4]]
def raw20086step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20086step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]
def raw20086step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20086 raw20086Labels = mixedMoment B node4060 node4060Labels := by
  calc
    mixedMoment B raw20086 raw20086Labels = mixedMoment B raw20086step0 raw20086step0Labels := by
      have hz : ∀ j, raw20086 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20086step0 = (fun i j => raw20086 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20086step0 raw20086; decide +kernel
      have hl : raw20086step0Labels = raw20086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20086 raw20086Labels permutation520 hz
    mixedMoment B raw20086step0 raw20086step0Labels = mixedMoment B raw20086step1 raw20086step1Labels := by
      have hz : ∀ j, raw20086step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20086step1 = (fun i j => raw20086step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20086step1 raw20086step0; decide +kernel
      have hl : raw20086step1Labels = raw20086step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20086step0 raw20086step0Labels permutation80 hz
    mixedMoment B raw20086step1 raw20086step1Labels = mixedMoment B raw20086step2 raw20086step2Labels := by
      have hz : ∀ j, raw20086step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20086step2 = (fun i j => raw20086step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20086step2 raw20086step1; decide +kernel
      have hl : raw20086step2Labels = raw20086step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20086step1 raw20086step1Labels permutation14 hz
    mixedMoment B raw20086step2 raw20086step2Labels = mixedMoment B raw20086step3 raw20086step3Labels := by
      have hz : ∀ i, raw20086step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20086step3 = (fun i j => raw20086step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20086step3 raw20086step2; decide +kernel
      have hl : raw20086step3Labels = (fun j => raw20086step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20086step2 raw20086step2Labels permutation6 hz
    mixedMoment B raw20086step3 raw20086step3Labels = mixedMoment B raw20086step4 raw20086step4Labels := by
      have ha : raw20086step4 = (fun i j => raw20086step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20086step4 raw20086step3; decide +kernel
      have hl : raw20086step4Labels = raw20086step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20086step3 raw20086step3Labels permutation7 permutation0
    mixedMoment B raw20086step4 raw20086step4Labels = mixedMoment B raw20086step5 raw20086step5Labels := by
      have ha : raw20086step5 = -raw20086step4 := by apply Matrix.ext; change ∀ i j, raw20086step5 i j = -(raw20086step4 i j); unfold raw20086step5 raw20086step4; decide +kernel
      have hl : raw20086step5Labels = raw20086step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4060 node4060Labels := by rfl

def raw20087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -5, 0]]
def raw20087Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -5, 0]]
def raw20087step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20087step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![5, -5, 0]]
def raw20087step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20087step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![5, -5, 0]]
def raw20087step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20087step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![5, -5]]
def raw20087step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20087step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![5, -5], ![-1, 1], ![-4, 4]]
def raw20087step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20087step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![4, -4]]
def raw20087step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20087 raw20087Labels = mixedMoment B node4060 node4060Labels := by
  calc
    mixedMoment B raw20087 raw20087Labels = mixedMoment B raw20087step0 raw20087step0Labels := by
      have hz : ∀ j, raw20087 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20087step0 = (fun i j => raw20087 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20087step0 raw20087; decide +kernel
      have hl : raw20087step0Labels = raw20087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20087 raw20087Labels permutation434 hz
    mixedMoment B raw20087step0 raw20087step0Labels = mixedMoment B raw20087step1 raw20087step1Labels := by
      have hz : ∀ j, raw20087step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20087step1 = (fun i j => raw20087step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20087step1 raw20087step0; decide +kernel
      have hl : raw20087step1Labels = raw20087step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20087step0 raw20087step0Labels permutation80 hz
    mixedMoment B raw20087step1 raw20087step1Labels = mixedMoment B raw20087step2 raw20087step2Labels := by
      have hz : ∀ j, raw20087step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20087step2 = (fun i j => raw20087step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20087step2 raw20087step1; decide +kernel
      have hl : raw20087step2Labels = raw20087step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20087step1 raw20087step1Labels permutation14 hz
    mixedMoment B raw20087step2 raw20087step2Labels = mixedMoment B raw20087step3 raw20087step3Labels := by
      have hz : ∀ i, raw20087step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw20087step3 = (fun i j => raw20087step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw20087step3 raw20087step2; decide +kernel
      have hl : raw20087step3Labels = (fun j => raw20087step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw20087step2 raw20087step2Labels permutation6 hz
    mixedMoment B raw20087step3 raw20087step3Labels = mixedMoment B raw20087step4 raw20087step4Labels := by
      have ha : raw20087step4 = (fun i j => raw20087step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20087step4 raw20087step3; decide +kernel
      have hl : raw20087step4Labels = raw20087step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20087step3 raw20087step3Labels permutation7 permutation0
    mixedMoment B raw20087step4 raw20087step4Labels = mixedMoment B raw20087step5 raw20087step5Labels := by
      have ha : raw20087step5 = -raw20087step4 := by apply Matrix.ext; change ∀ i j, raw20087step5 i j = -(raw20087step4 i j); unfold raw20087step5 raw20087step4; decide +kernel
      have hl : raw20087step5Labels = raw20087step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4060 node4060Labels := by rfl

def raw20088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw20088Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw20088step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw20088step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20088step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 1, -3], ![3, -3, 0]]
def raw20088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20088 raw20088Labels = mixedMoment B node621 node621Labels := by
  calc
    mixedMoment B raw20088 raw20088Labels = mixedMoment B raw20088step0 raw20088step0Labels := by
      have hz : ∀ j, raw20088 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20088step0 = (fun i j => raw20088 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20088step0 raw20088; decide +kernel
      have hl : raw20088step0Labels = raw20088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20088 raw20088Labels permutation434 hz
    mixedMoment B raw20088step0 raw20088step0Labels = mixedMoment B raw20088step1 raw20088step1Labels := by
      have hz : ∀ j, raw20088step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20088step1 = (fun i j => raw20088step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20088step1 raw20088step0; decide +kernel
      have hl : raw20088step1Labels = raw20088step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20088step0 raw20088step0Labels permutation80 hz
    mixedMoment B raw20088step1 raw20088step1Labels = mixedMoment B raw20088step2 raw20088step2Labels := by
      have hz : ∀ j, raw20088step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20088step2 = (fun i j => raw20088step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20088step2 raw20088step1; decide +kernel
      have hl : raw20088step2Labels = raw20088step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20088step1 raw20088step1Labels permutation14 hz
    _ = mixedMoment B node621 node621Labels := by rfl

def raw20089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw20089Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw20089step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw20089step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20089 raw20089Labels = mixedMoment B node940 node940Labels := by
  calc
    mixedMoment B raw20089 raw20089Labels = mixedMoment B raw20089step0 raw20089step0Labels := by
      have hz : ∀ j, raw20089 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20089step0 = (fun i j => raw20089 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20089step0 raw20089; decide +kernel
      have hl : raw20089step0Labels = raw20089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20089 raw20089Labels permutation434 hz
    mixedMoment B raw20089step0 raw20089step0Labels = mixedMoment B raw20089step1 raw20089step1Labels := by
      have hz : ∀ j, raw20089step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20089step1 = (fun i j => raw20089step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20089step1 raw20089step0; decide +kernel
      have hl : raw20089step1Labels = raw20089step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20089step0 raw20089step0Labels permutation80 hz
    _ = mixedMoment B node940 node940Labels := by rfl

def raw20090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw20090Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw20090step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20090step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw20090step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20090 raw20090Labels = mixedMoment B node940 node940Labels := by
  calc
    mixedMoment B raw20090 raw20090Labels = mixedMoment B raw20090step0 raw20090step0Labels := by
      have hz : ∀ j, raw20090 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20090step0 = (fun i j => raw20090 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20090step0 raw20090; decide +kernel
      have hl : raw20090step0Labels = raw20090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20090 raw20090Labels permutation434 hz
    mixedMoment B raw20090step0 raw20090step0Labels = mixedMoment B raw20090step1 raw20090step1Labels := by
      have hz : ∀ j, raw20090step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20090step1 = (fun i j => raw20090step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20090step1 raw20090step0; decide +kernel
      have hl : raw20090step1Labels = raw20090step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20090step0 raw20090step0Labels permutation56 hz
    _ = mixedMoment B node940 node940Labels := by rfl

def raw20091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw20091Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw20091step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20091step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw20091step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20091 raw20091Labels = mixedMoment B node940 node940Labels := by
  calc
    mixedMoment B raw20091 raw20091Labels = mixedMoment B raw20091step0 raw20091step0Labels := by
      have hz : ∀ j, raw20091 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20091step0 = (fun i j => raw20091 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20091step0 raw20091; decide +kernel
      have hl : raw20091step0Labels = raw20091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20091 raw20091Labels permutation346 hz
    mixedMoment B raw20091step0 raw20091step0Labels = mixedMoment B raw20091step1 raw20091step1Labels := by
      have hz : ∀ j, raw20091step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20091step1 = (fun i j => raw20091step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20091step1 raw20091step0; decide +kernel
      have hl : raw20091step1Labels = raw20091step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20091step0 raw20091step0Labels permutation56 hz
    _ = mixedMoment B node940 node940Labels := by rfl

def raw20092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw20092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw20092step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw20092step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20092step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 1, -3], ![2, -2, 0]]
def raw20092step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20092step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw20092step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20092 raw20092Labels = mixedMoment B node1094 node1094Labels := by
  calc
    mixedMoment B raw20092 raw20092Labels = mixedMoment B raw20092step0 raw20092step0Labels := by
      have hz : ∀ j, raw20092 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20092step0 = (fun i j => raw20092 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20092step0 raw20092; decide +kernel
      have hl : raw20092step0Labels = raw20092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20092 raw20092Labels permutation434 hz
    mixedMoment B raw20092step0 raw20092step0Labels = mixedMoment B raw20092step1 raw20092step1Labels := by
      have hz : ∀ j, raw20092step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20092step1 = (fun i j => raw20092step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20092step1 raw20092step0; decide +kernel
      have hl : raw20092step1Labels = raw20092step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20092step0 raw20092step0Labels permutation80 hz
    mixedMoment B raw20092step1 raw20092step1Labels = mixedMoment B raw20092step2 raw20092step2Labels := by
      have hz : ∀ j, raw20092step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20092step2 = (fun i j => raw20092step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20092step2 raw20092step1; decide +kernel
      have hl : raw20092step2Labels = raw20092step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20092step1 raw20092step1Labels permutation14 hz
    mixedMoment B raw20092step2 raw20092step2Labels = mixedMoment B raw20092step3 raw20092step3Labels := by
      have ha : raw20092step3 = (fun i j => raw20092step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20092step3 raw20092step2; decide +kernel
      have hl : raw20092step3Labels = raw20092step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20092step2 raw20092step2Labels permutation3 permutation2
    _ = mixedMoment B node1094 node1094Labels := by rfl

def raw20093 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20093Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20093step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20093step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20093step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20093step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![2, -3, 1], ![-3, 0, 3]]
def raw20093step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20093step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-3, 2, 1]]
def raw20093step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20093step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![3, -2, -1]]
def raw20093step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20093 raw20093Labels = mixedMoment B node1747 node1747Labels := by
  calc
    mixedMoment B raw20093 raw20093Labels = mixedMoment B raw20093step0 raw20093step0Labels := by
      have hz : ∀ j, raw20093 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20093step0 = (fun i j => raw20093 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20093step0 raw20093; decide +kernel
      have hl : raw20093step0Labels = raw20093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20093 raw20093Labels permutation434 hz
    mixedMoment B raw20093step0 raw20093step0Labels = mixedMoment B raw20093step1 raw20093step1Labels := by
      have hz : ∀ j, raw20093step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20093step1 = (fun i j => raw20093step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20093step1 raw20093step0; decide +kernel
      have hl : raw20093step1Labels = raw20093step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20093step0 raw20093step0Labels permutation80 hz
    mixedMoment B raw20093step1 raw20093step1Labels = mixedMoment B raw20093step2 raw20093step2Labels := by
      have hz : ∀ j, raw20093step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20093step2 = (fun i j => raw20093step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20093step2 raw20093step1; decide +kernel
      have hl : raw20093step2Labels = raw20093step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20093step1 raw20093step1Labels permutation14 hz
    mixedMoment B raw20093step2 raw20093step2Labels = mixedMoment B raw20093step3 raw20093step3Labels := by
      have ha : raw20093step3 = (fun i j => raw20093step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20093step3 raw20093step2; decide +kernel
      have hl : raw20093step3Labels = raw20093step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20093step2 raw20093step2Labels permutation3 permutation4
    mixedMoment B raw20093step3 raw20093step3Labels = mixedMoment B raw20093step4 raw20093step4Labels := by
      have ha : raw20093step4 = -raw20093step3 := by apply Matrix.ext; change ∀ i j, raw20093step4 i j = -(raw20093step3 i j); unfold raw20093step4 raw20093step3; decide +kernel
      have hl : raw20093step4Labels = raw20093step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1747 node1747Labels := by rfl

def raw20094 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20094Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20094step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20094step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20094step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -3, 1], ![2, 2, -4]]
def raw20094step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20094 raw20094Labels = mixedMoment B node2064 node2064Labels := by
  calc
    mixedMoment B raw20094 raw20094Labels = mixedMoment B raw20094step0 raw20094step0Labels := by
      have hz : ∀ j, raw20094 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20094step0 = (fun i j => raw20094 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20094step0 raw20094; decide +kernel
      have hl : raw20094step0Labels = raw20094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20094 raw20094Labels permutation434 hz
    mixedMoment B raw20094step0 raw20094step0Labels = mixedMoment B raw20094step1 raw20094step1Labels := by
      have hz : ∀ j, raw20094step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20094step1 = (fun i j => raw20094step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20094step1 raw20094step0; decide +kernel
      have hl : raw20094step1Labels = raw20094step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20094step0 raw20094step0Labels permutation80 hz
    mixedMoment B raw20094step1 raw20094step1Labels = mixedMoment B raw20094step2 raw20094step2Labels := by
      have ha : raw20094step2 = (fun i j => raw20094step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20094step2 raw20094step1; decide +kernel
      have hl : raw20094step2Labels = raw20094step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20094step1 raw20094step1Labels permutation29 permutation2
    _ = mixedMoment B node2064 node2064Labels := by rfl

def raw20095 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20095Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20095step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw20095step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20095step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -3, 1], ![2, 2, -4]]
def raw20095step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20095 raw20095Labels = mixedMoment B node2064 node2064Labels := by
  calc
    mixedMoment B raw20095 raw20095Labels = mixedMoment B raw20095step0 raw20095step0Labels := by
      have hz : ∀ j, raw20095 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20095step0 = (fun i j => raw20095 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20095step0 raw20095; decide +kernel
      have hl : raw20095step0Labels = raw20095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20095 raw20095Labels permutation434 hz
    mixedMoment B raw20095step0 raw20095step0Labels = mixedMoment B raw20095step1 raw20095step1Labels := by
      have hz : ∀ j, raw20095step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20095step1 = (fun i j => raw20095step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20095step1 raw20095step0; decide +kernel
      have hl : raw20095step1Labels = raw20095step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20095step0 raw20095step0Labels permutation56 hz
    mixedMoment B raw20095step1 raw20095step1Labels = mixedMoment B raw20095step2 raw20095step2Labels := by
      have ha : raw20095step2 = (fun i j => raw20095step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20095step2 raw20095step1; decide +kernel
      have hl : raw20095step2Labels = raw20095step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20095step1 raw20095step1Labels permutation29 permutation2
    _ = mixedMoment B node2064 node2064Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
