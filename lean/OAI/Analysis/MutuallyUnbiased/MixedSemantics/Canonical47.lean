import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw6016 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6016step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6016step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6016step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6016step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6016step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6016step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6016 raw6016Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw6016 raw6016Labels = mixedMoment B raw6016step0 raw6016step0Labels := by
      have hz : ∀ j, raw6016 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6016step0 = (fun i j => raw6016 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6016step0 raw6016; decide +kernel
      have hl : raw6016step0Labels = raw6016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6016 raw6016Labels permutation434 hz
    mixedMoment B raw6016step0 raw6016step0Labels = mixedMoment B raw6016step1 raw6016step1Labels := by
      have hz : ∀ j, raw6016step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6016step1 = (fun i j => raw6016step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6016step1 raw6016step0; decide +kernel
      have hl : raw6016step1Labels = raw6016step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6016step0 raw6016step0Labels permutation56 hz
    mixedMoment B raw6016step1 raw6016step1Labels = mixedMoment B raw6016step2 raw6016step2Labels := by
      have ha : raw6016step2 = (fun i j => raw6016step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6016step2 raw6016step1; decide +kernel
      have hl : raw6016step2Labels = raw6016step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6016step1 raw6016step1Labels permutation8 permutation6
    mixedMoment B raw6016step2 raw6016step2Labels = mixedMoment B raw6016step3 raw6016step3Labels := by
      have ha : raw6016step3 = raw6016step2 := by apply Matrix.ext; unfold raw6016step3 raw6016step2; decide +kernel
      have hl : raw6016step2Labels = labelEmbedding9 ∘ raw6016step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6016step2 raw6016step2Labels raw6016step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw6017 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6017step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6017step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6017step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6017step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6017step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6017 raw6017Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw6017 raw6017Labels = mixedMoment B raw6017step0 raw6017step0Labels := by
      have hz : ∀ j, raw6017 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6017step0 = (fun i j => raw6017 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6017step0 raw6017; decide +kernel
      have hl : raw6017step0Labels = raw6017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6017 raw6017Labels permutation346 hz
    mixedMoment B raw6017step0 raw6017step0Labels = mixedMoment B raw6017step1 raw6017step1Labels := by
      have hz : ∀ j, raw6017step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6017step1 = (fun i j => raw6017step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6017step1 raw6017step0; decide +kernel
      have hl : raw6017step1Labels = raw6017step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6017step0 raw6017step0Labels permutation56 hz
    mixedMoment B raw6017step1 raw6017step1Labels = mixedMoment B raw6017step2 raw6017step2Labels := by
      have ha : raw6017step2 = (fun i j => raw6017step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6017step2 raw6017step1; decide +kernel
      have hl : raw6017step2Labels = raw6017step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6017step1 raw6017step1Labels permutation8 permutation6
    mixedMoment B raw6017step2 raw6017step2Labels = mixedMoment B raw6017step3 raw6017step3Labels := by
      have ha : raw6017step3 = raw6017step2 := by apply Matrix.ext; unfold raw6017step3 raw6017step2; decide +kernel
      have hl : raw6017step2Labels = labelEmbedding9 ∘ raw6017step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6017step2 raw6017step2Labels raw6017step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw6018 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6018step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6018step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6018step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6018step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![-2, 0, 2]]
def raw6018step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6018step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw6018step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6018step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw6018step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6018 raw6018Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw6018 raw6018Labels = mixedMoment B raw6018step0 raw6018step0Labels := by
      have hz : ∀ j, raw6018 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6018step0 = (fun i j => raw6018 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6018step0 raw6018; decide +kernel
      have hl : raw6018step0Labels = raw6018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6018 raw6018Labels permutation434 hz
    mixedMoment B raw6018step0 raw6018step0Labels = mixedMoment B raw6018step1 raw6018step1Labels := by
      have hz : ∀ j, raw6018step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6018step1 = (fun i j => raw6018step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6018step1 raw6018step0; decide +kernel
      have hl : raw6018step1Labels = raw6018step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6018step0 raw6018step0Labels permutation80 hz
    mixedMoment B raw6018step1 raw6018step1Labels = mixedMoment B raw6018step2 raw6018step2Labels := by
      have hz : ∀ j, raw6018step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw6018step2 = (fun i j => raw6018step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw6018step2 raw6018step1; decide +kernel
      have hl : raw6018step2Labels = raw6018step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6018step1 raw6018step1Labels permutation14 hz
    mixedMoment B raw6018step2 raw6018step2Labels = mixedMoment B raw6018step3 raw6018step3Labels := by
      have ha : raw6018step3 = (fun i j => raw6018step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6018step3 raw6018step2; decide +kernel
      have hl : raw6018step3Labels = raw6018step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6018step2 raw6018step2Labels permutation2 permutation6
    mixedMoment B raw6018step3 raw6018step3Labels = mixedMoment B raw6018step4 raw6018step4Labels := by
      have ha : raw6018step4 = raw6018step3 := by apply Matrix.ext; unfold raw6018step4 raw6018step3; decide +kernel
      have hl : raw6018step3Labels = labelEmbedding9 ∘ raw6018step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6018step3 raw6018step3Labels raw6018step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

def raw6019 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6019step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6019step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6019step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6019step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![2, -3, 1], ![-3, 1, 2]]
def raw6019step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6019step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw6019step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6019 raw6019Labels = mixedMoment B node5311 node5311Labels := by
  calc
    mixedMoment B raw6019 raw6019Labels = mixedMoment B raw6019step0 raw6019step0Labels := by
      have hz : ∀ j, raw6019 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6019step0 = (fun i j => raw6019 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6019step0 raw6019; decide +kernel
      have hl : raw6019step0Labels = raw6019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6019 raw6019Labels permutation434 hz
    mixedMoment B raw6019step0 raw6019step0Labels = mixedMoment B raw6019step1 raw6019step1Labels := by
      have hz : ∀ j, raw6019step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6019step1 = (fun i j => raw6019step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6019step1 raw6019step0; decide +kernel
      have hl : raw6019step1Labels = raw6019step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6019step0 raw6019step0Labels permutation80 hz
    mixedMoment B raw6019step1 raw6019step1Labels = mixedMoment B raw6019step2 raw6019step2Labels := by
      have hz : ∀ j, raw6019step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw6019step2 = (fun i j => raw6019step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw6019step2 raw6019step1; decide +kernel
      have hl : raw6019step2Labels = raw6019step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6019step1 raw6019step1Labels permutation14 hz
    mixedMoment B raw6019step2 raw6019step2Labels = mixedMoment B raw6019step3 raw6019step3Labels := by
      have ha : raw6019step3 = (fun i j => raw6019step2 (permutation6 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6019step3 raw6019step2; decide +kernel
      have hl : raw6019step3Labels = raw6019step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6019step2 raw6019step2Labels permutation6 permutation2
    _ = mixedMoment B node5311 node5311Labels := by rfl

def raw6020 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6020step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw6020step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6020step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6020step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6020step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6020step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6020 raw6020Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw6020 raw6020Labels = mixedMoment B raw6020step0 raw6020step0Labels := by
      have hz : ∀ j, raw6020 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6020step0 = (fun i j => raw6020 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6020step0 raw6020; decide +kernel
      have hl : raw6020step0Labels = raw6020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6020 raw6020Labels permutation434 hz
    mixedMoment B raw6020step0 raw6020step0Labels = mixedMoment B raw6020step1 raw6020step1Labels := by
      have ha : raw6020step1 = (fun i j => raw6020step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6020step1 raw6020step0; decide +kernel
      have hl : raw6020step1Labels = raw6020step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6020step0 raw6020step0Labels permutation36 permutation4
    mixedMoment B raw6020step1 raw6020step1Labels = mixedMoment B raw6020step2 raw6020step2Labels := by
      have ha : raw6020step2 = -raw6020step1 := by apply Matrix.ext; change ∀ i j, raw6020step2 i j = -(raw6020step1 i j); unfold raw6020step2 raw6020step1; decide +kernel
      have hl : raw6020step2Labels = raw6020step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6020step2 raw6020step2Labels = mixedMoment B raw6020step3 raw6020step3Labels := by
      have ha : raw6020step3 = raw6020step2 := by apply Matrix.ext; unfold raw6020step3 raw6020step2; decide +kernel
      have hl : raw6020step2Labels = labelEmbedding7 ∘ raw6020step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6020step2 raw6020step2Labels raw6020step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4817 node4817Labels := by rfl

def raw6021 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6021step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw6021step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6021step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw6021step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6021 raw6021Labels = mixedMoment B node5089 node5089Labels := by
  calc
    mixedMoment B raw6021 raw6021Labels = mixedMoment B raw6021step0 raw6021step0Labels := by
      have hz : ∀ j, raw6021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6021step0 = (fun i j => raw6021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6021step0 raw6021; decide +kernel
      have hl : raw6021step0Labels = raw6021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6021 raw6021Labels permutation434 hz
    mixedMoment B raw6021step0 raw6021step0Labels = mixedMoment B raw6021step1 raw6021step1Labels := by
      have ha : raw6021step1 = (fun i j => raw6021step0 (permutation120 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6021step1 raw6021step0; decide +kernel
      have hl : raw6021step1Labels = raw6021step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6021step0 raw6021step0Labels permutation120 permutation5
    mixedMoment B raw6021step1 raw6021step1Labels = mixedMoment B raw6021step2 raw6021step2Labels := by
      have ha : raw6021step2 = raw6021step1 := by apply Matrix.ext; unfold raw6021step2 raw6021step1; decide +kernel
      have hl : raw6021step1Labels = labelEmbedding8 ∘ raw6021step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6021step1 raw6021step1Labels raw6021step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5089 node5089Labels := by rfl

def raw6022 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6022step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6022step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6022step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6022step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6022 raw6022Labels = mixedMoment B node5088 node5088Labels := by
  calc
    mixedMoment B raw6022 raw6022Labels = mixedMoment B raw6022step0 raw6022step0Labels := by
      have ha : raw6022step0 = (fun i j => raw6022 (permutation550 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6022step0 raw6022; decide +kernel
      have hl : raw6022step0Labels = raw6022Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6022 raw6022Labels permutation550 permutation5
    mixedMoment B raw6022step0 raw6022step0Labels = mixedMoment B raw6022step1 raw6022step1Labels := by
      have ha : raw6022step1 = raw6022step0 := by apply Matrix.ext; unfold raw6022step1 raw6022step0; decide +kernel
      have hl : raw6022step0Labels = labelEmbedding8 ∘ raw6022step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6022step0 raw6022step0Labels raw6022step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5088 node5088Labels := by rfl

def raw6023 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6023step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6023step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6023step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6023step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6023 raw6023Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw6023 raw6023Labels = mixedMoment B raw6023step0 raw6023step0Labels := by
      have hz : ∀ j, raw6023 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6023step0 = (fun i j => raw6023 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6023step0 raw6023; decide +kernel
      have hl : raw6023step0Labels = raw6023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6023 raw6023Labels permutation434 hz
    mixedMoment B raw6023step0 raw6023step0Labels = mixedMoment B raw6023step1 raw6023step1Labels := by
      have ha : raw6023step1 = (fun i j => raw6023step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6023step1 raw6023step0; decide +kernel
      have hl : raw6023step1Labels = raw6023step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6023step0 raw6023step0Labels permutation32 permutation6
    mixedMoment B raw6023step1 raw6023step1Labels = mixedMoment B raw6023step2 raw6023step2Labels := by
      have ha : raw6023step2 = raw6023step1 := by apply Matrix.ext; unfold raw6023step2 raw6023step1; decide +kernel
      have hl : raw6023step1Labels = labelEmbedding9 ∘ raw6023step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6023step1 raw6023step1Labels raw6023step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw6024 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6024step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw6024step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw6024step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6024 raw6024Labels = mixedMoment B node5106 node5106Labels := by
  calc
    mixedMoment B raw6024 raw6024Labels = mixedMoment B raw6024step0 raw6024step0Labels := by
      have hz : ∀ j, raw6024 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6024step0 = (fun i j => raw6024 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6024step0 raw6024; decide +kernel
      have hl : raw6024step0Labels = raw6024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6024 raw6024Labels permutation434 hz
    mixedMoment B raw6024step0 raw6024step0Labels = mixedMoment B raw6024step1 raw6024step1Labels := by
      have ha : raw6024step1 = (fun i j => raw6024step0 (permutation119 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6024step1 raw6024step0; decide +kernel
      have hl : raw6024step1Labels = raw6024step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6024step0 raw6024step0Labels permutation119 permutation5
    mixedMoment B raw6024step1 raw6024step1Labels = mixedMoment B raw6024step2 raw6024step2Labels := by
      have ha : raw6024step2 = raw6024step1 := by apply Matrix.ext; unfold raw6024step2 raw6024step1; decide +kernel
      have hl : raw6024step1Labels = labelEmbedding8 ∘ raw6024step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6024step1 raw6024step1Labels raw6024step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5106 node5106Labels := by rfl

def raw6025 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6025step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw6025step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6025step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6025step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6025step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6025step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6025 raw6025Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw6025 raw6025Labels = mixedMoment B raw6025step0 raw6025step0Labels := by
      have hz : ∀ j, raw6025 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6025step0 = (fun i j => raw6025 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6025step0 raw6025; decide +kernel
      have hl : raw6025step0Labels = raw6025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6025 raw6025Labels permutation346 hz
    mixedMoment B raw6025step0 raw6025step0Labels = mixedMoment B raw6025step1 raw6025step1Labels := by
      have ha : raw6025step1 = (fun i j => raw6025step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6025step1 raw6025step0; decide +kernel
      have hl : raw6025step1Labels = raw6025step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6025step0 raw6025step0Labels permutation36 permutation4
    mixedMoment B raw6025step1 raw6025step1Labels = mixedMoment B raw6025step2 raw6025step2Labels := by
      have ha : raw6025step2 = -raw6025step1 := by apply Matrix.ext; change ∀ i j, raw6025step2 i j = -(raw6025step1 i j); unfold raw6025step2 raw6025step1; decide +kernel
      have hl : raw6025step2Labels = raw6025step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6025step2 raw6025step2Labels = mixedMoment B raw6025step3 raw6025step3Labels := by
      have ha : raw6025step3 = raw6025step2 := by apply Matrix.ext; unfold raw6025step3 raw6025step2; decide +kernel
      have hl : raw6025step2Labels = labelEmbedding7 ∘ raw6025step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6025step2 raw6025step2Labels raw6025step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4817 node4817Labels := by rfl

def raw6026 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6026step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw6026step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6026step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw6026step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6026 raw6026Labels = mixedMoment B node5089 node5089Labels := by
  calc
    mixedMoment B raw6026 raw6026Labels = mixedMoment B raw6026step0 raw6026step0Labels := by
      have hz : ∀ j, raw6026 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6026step0 = (fun i j => raw6026 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6026step0 raw6026; decide +kernel
      have hl : raw6026step0Labels = raw6026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6026 raw6026Labels permutation346 hz
    mixedMoment B raw6026step0 raw6026step0Labels = mixedMoment B raw6026step1 raw6026step1Labels := by
      have ha : raw6026step1 = (fun i j => raw6026step0 (permutation120 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6026step1 raw6026step0; decide +kernel
      have hl : raw6026step1Labels = raw6026step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6026step0 raw6026step0Labels permutation120 permutation5
    mixedMoment B raw6026step1 raw6026step1Labels = mixedMoment B raw6026step2 raw6026step2Labels := by
      have ha : raw6026step2 = raw6026step1 := by apply Matrix.ext; unfold raw6026step2 raw6026step1; decide +kernel
      have hl : raw6026step1Labels = labelEmbedding8 ∘ raw6026step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6026step1 raw6026step1Labels raw6026step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5089 node5089Labels := by rfl

def raw6027 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6027step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6027step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6027step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6027step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6027 raw6027Labels = mixedMoment B node5088 node5088Labels := by
  calc
    mixedMoment B raw6027 raw6027Labels = mixedMoment B raw6027step0 raw6027step0Labels := by
      have ha : raw6027step0 = (fun i j => raw6027 (permutation566 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6027step0 raw6027; decide +kernel
      have hl : raw6027step0Labels = raw6027Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6027 raw6027Labels permutation566 permutation5
    mixedMoment B raw6027step0 raw6027step0Labels = mixedMoment B raw6027step1 raw6027step1Labels := by
      have ha : raw6027step1 = raw6027step0 := by apply Matrix.ext; unfold raw6027step1 raw6027step0; decide +kernel
      have hl : raw6027step0Labels = labelEmbedding8 ∘ raw6027step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6027step0 raw6027step0Labels raw6027step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5088 node5088Labels := by rfl

def raw6028 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6028step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6028step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6028step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6028step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6028 raw6028Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw6028 raw6028Labels = mixedMoment B raw6028step0 raw6028step0Labels := by
      have hz : ∀ j, raw6028 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6028step0 = (fun i j => raw6028 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6028step0 raw6028; decide +kernel
      have hl : raw6028step0Labels = raw6028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6028 raw6028Labels permutation346 hz
    mixedMoment B raw6028step0 raw6028step0Labels = mixedMoment B raw6028step1 raw6028step1Labels := by
      have ha : raw6028step1 = (fun i j => raw6028step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6028step1 raw6028step0; decide +kernel
      have hl : raw6028step1Labels = raw6028step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6028step0 raw6028step0Labels permutation32 permutation6
    mixedMoment B raw6028step1 raw6028step1Labels = mixedMoment B raw6028step2 raw6028step2Labels := by
      have ha : raw6028step2 = raw6028step1 := by apply Matrix.ext; unfold raw6028step2 raw6028step1; decide +kernel
      have hl : raw6028step1Labels = labelEmbedding9 ∘ raw6028step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6028step1 raw6028step1Labels raw6028step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw6029 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6029step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw6029step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6029step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw6029step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6029 raw6029Labels = mixedMoment B node5106 node5106Labels := by
  calc
    mixedMoment B raw6029 raw6029Labels = mixedMoment B raw6029step0 raw6029step0Labels := by
      have hz : ∀ j, raw6029 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6029step0 = (fun i j => raw6029 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6029step0 raw6029; decide +kernel
      have hl : raw6029step0Labels = raw6029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6029 raw6029Labels permutation346 hz
    mixedMoment B raw6029step0 raw6029step0Labels = mixedMoment B raw6029step1 raw6029step1Labels := by
      have ha : raw6029step1 = (fun i j => raw6029step0 (permutation119 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6029step1 raw6029step0; decide +kernel
      have hl : raw6029step1Labels = raw6029step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6029step0 raw6029step0Labels permutation119 permutation5
    mixedMoment B raw6029step1 raw6029step1Labels = mixedMoment B raw6029step2 raw6029step2Labels := by
      have ha : raw6029step2 = raw6029step1 := by apply Matrix.ext; unfold raw6029step2 raw6029step1; decide +kernel
      have hl : raw6029step1Labels = labelEmbedding8 ∘ raw6029step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6029step1 raw6029step1Labels raw6029step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5106 node5106Labels := by rfl

def raw6030 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6030step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6030step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6030step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6030step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6030step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6030step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6030step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6030 raw6030Labels = mixedMoment B node4478 node4478Labels := by
  calc
    mixedMoment B raw6030 raw6030Labels = mixedMoment B raw6030step0 raw6030step0Labels := by
      have hz : ∀ j, raw6030 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6030step0 = (fun i j => raw6030 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6030step0 raw6030; decide +kernel
      have hl : raw6030step0Labels = raw6030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6030 raw6030Labels permutation434 hz
    mixedMoment B raw6030step0 raw6030step0Labels = mixedMoment B raw6030step1 raw6030step1Labels := by
      have hz : ∀ j, raw6030step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6030step1 = (fun i j => raw6030step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6030step1 raw6030step0; decide +kernel
      have hl : raw6030step1Labels = raw6030step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6030step0 raw6030step0Labels permutation80 hz
    mixedMoment B raw6030step1 raw6030step1Labels = mixedMoment B raw6030step2 raw6030step2Labels := by
      have ha : raw6030step2 = (fun i j => raw6030step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6030step2 raw6030step1; decide +kernel
      have hl : raw6030step2Labels = raw6030step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6030step1 raw6030step1Labels permutation25 permutation5
    mixedMoment B raw6030step2 raw6030step2Labels = mixedMoment B raw6030step3 raw6030step3Labels := by
      have ha : raw6030step3 = raw6030step2 := by apply Matrix.ext; unfold raw6030step3 raw6030step2; decide +kernel
      have hl : raw6030step2Labels = labelEmbedding8 ∘ raw6030step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6030step2 raw6030step2Labels raw6030step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4478 node4478Labels := by rfl

def raw6031 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6031step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6031step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6031step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6031step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw6031step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6031step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw6031step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6031 raw6031Labels = mixedMoment B node4479 node4479Labels := by
  calc
    mixedMoment B raw6031 raw6031Labels = mixedMoment B raw6031step0 raw6031step0Labels := by
      have hz : ∀ j, raw6031 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6031step0 = (fun i j => raw6031 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6031step0 raw6031; decide +kernel
      have hl : raw6031step0Labels = raw6031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6031 raw6031Labels permutation434 hz
    mixedMoment B raw6031step0 raw6031step0Labels = mixedMoment B raw6031step1 raw6031step1Labels := by
      have hz : ∀ j, raw6031step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6031step1 = (fun i j => raw6031step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6031step1 raw6031step0; decide +kernel
      have hl : raw6031step1Labels = raw6031step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6031step0 raw6031step0Labels permutation80 hz
    mixedMoment B raw6031step1 raw6031step1Labels = mixedMoment B raw6031step2 raw6031step2Labels := by
      have ha : raw6031step2 = (fun i j => raw6031step1 (permutation24 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6031step2 raw6031step1; decide +kernel
      have hl : raw6031step2Labels = raw6031step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6031step1 raw6031step1Labels permutation24 permutation5
    mixedMoment B raw6031step2 raw6031step2Labels = mixedMoment B raw6031step3 raw6031step3Labels := by
      have ha : raw6031step3 = raw6031step2 := by apply Matrix.ext; unfold raw6031step3 raw6031step2; decide +kernel
      have hl : raw6031step2Labels = labelEmbedding8 ∘ raw6031step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6031step2 raw6031step2Labels raw6031step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4479 node4479Labels := by rfl

def raw6032 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6032step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6032step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6032step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6032step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6032 raw6032Labels = mixedMoment B node4477 node4477Labels := by
  calc
    mixedMoment B raw6032 raw6032Labels = mixedMoment B raw6032step0 raw6032step0Labels := by
      have hz : ∀ j, raw6032 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6032step0 = (fun i j => raw6032 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6032step0 raw6032; decide +kernel
      have hl : raw6032step0Labels = raw6032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6032 raw6032Labels permutation434 hz
    mixedMoment B raw6032step0 raw6032step0Labels = mixedMoment B raw6032step1 raw6032step1Labels := by
      have ha : raw6032step1 = (fun i j => raw6032step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6032step1 raw6032step0; decide +kernel
      have hl : raw6032step1Labels = raw6032step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6032step0 raw6032step0Labels permutation125 permutation5
    mixedMoment B raw6032step1 raw6032step1Labels = mixedMoment B raw6032step2 raw6032step2Labels := by
      have ha : raw6032step2 = raw6032step1 := by apply Matrix.ext; unfold raw6032step2 raw6032step1; decide +kernel
      have hl : raw6032step1Labels = labelEmbedding8 ∘ raw6032step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6032step1 raw6032step1Labels raw6032step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4477 node4477Labels := by rfl

def raw6033 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6033step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6033step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6033step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6033step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6033 raw6033Labels = mixedMoment B node4477 node4477Labels := by
  calc
    mixedMoment B raw6033 raw6033Labels = mixedMoment B raw6033step0 raw6033step0Labels := by
      have hz : ∀ j, raw6033 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6033step0 = (fun i j => raw6033 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6033step0 raw6033; decide +kernel
      have hl : raw6033step0Labels = raw6033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6033 raw6033Labels permutation346 hz
    mixedMoment B raw6033step0 raw6033step0Labels = mixedMoment B raw6033step1 raw6033step1Labels := by
      have ha : raw6033step1 = (fun i j => raw6033step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6033step1 raw6033step0; decide +kernel
      have hl : raw6033step1Labels = raw6033step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6033step0 raw6033step0Labels permutation125 permutation5
    mixedMoment B raw6033step1 raw6033step1Labels = mixedMoment B raw6033step2 raw6033step2Labels := by
      have ha : raw6033step2 = raw6033step1 := by apply Matrix.ext; unfold raw6033step2 raw6033step1; decide +kernel
      have hl : raw6033step1Labels = labelEmbedding8 ∘ raw6033step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6033step1 raw6033step1Labels raw6033step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4477 node4477Labels := by rfl

def raw6034 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![-3, 1, 2]]
def raw6034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -4, 1], ![-3, 1, 2]]
def raw6034step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6034step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -4, 1], ![-3, 1, 2]]
def raw6034step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6034step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw6034step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6034step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw6034step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6034 raw6034Labels = mixedMoment B node4504 node4504Labels := by
  calc
    mixedMoment B raw6034 raw6034Labels = mixedMoment B raw6034step0 raw6034step0Labels := by
      have hz : ∀ j, raw6034 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6034step0 = (fun i j => raw6034 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6034step0 raw6034; decide +kernel
      have hl : raw6034step0Labels = raw6034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6034 raw6034Labels permutation434 hz
    mixedMoment B raw6034step0 raw6034step0Labels = mixedMoment B raw6034step1 raw6034step1Labels := by
      have hz : ∀ j, raw6034step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6034step1 = (fun i j => raw6034step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6034step1 raw6034step0; decide +kernel
      have hl : raw6034step1Labels = raw6034step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6034step0 raw6034step0Labels permutation80 hz
    mixedMoment B raw6034step1 raw6034step1Labels = mixedMoment B raw6034step2 raw6034step2Labels := by
      have ha : raw6034step2 = (fun i j => raw6034step1 (permutation23 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6034step2 raw6034step1; decide +kernel
      have hl : raw6034step2Labels = raw6034step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6034step1 raw6034step1Labels permutation23 permutation5
    mixedMoment B raw6034step2 raw6034step2Labels = mixedMoment B raw6034step3 raw6034step3Labels := by
      have ha : raw6034step3 = raw6034step2 := by apply Matrix.ext; unfold raw6034step3 raw6034step2; decide +kernel
      have hl : raw6034step2Labels = labelEmbedding8 ∘ raw6034step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6034step2 raw6034step2Labels raw6034step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4504 node4504Labels := by rfl

def raw6035 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6035step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6035step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6035step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6035step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw6035step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6035step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw6035step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6035step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw6035step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6035 raw6035Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw6035 raw6035Labels = mixedMoment B raw6035step0 raw6035step0Labels := by
      have hz : ∀ j, raw6035 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6035step0 = (fun i j => raw6035 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6035step0 raw6035; decide +kernel
      have hl : raw6035step0Labels = raw6035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6035 raw6035Labels permutation434 hz
    mixedMoment B raw6035step0 raw6035step0Labels = mixedMoment B raw6035step1 raw6035step1Labels := by
      have hz : ∀ j, raw6035step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6035step1 = (fun i j => raw6035step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6035step1 raw6035step0; decide +kernel
      have hl : raw6035step1Labels = raw6035step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6035step0 raw6035step0Labels permutation80 hz
    mixedMoment B raw6035step1 raw6035step1Labels = mixedMoment B raw6035step2 raw6035step2Labels := by
      have ha : raw6035step2 = (fun i j => raw6035step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6035step2 raw6035step1; decide +kernel
      have hl : raw6035step2Labels = raw6035step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6035step1 raw6035step1Labels permutation9 permutation4
    mixedMoment B raw6035step2 raw6035step2Labels = mixedMoment B raw6035step3 raw6035step3Labels := by
      have ha : raw6035step3 = -raw6035step2 := by apply Matrix.ext; change ∀ i j, raw6035step3 i j = -(raw6035step2 i j); unfold raw6035step3 raw6035step2; decide +kernel
      have hl : raw6035step3Labels = raw6035step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6035step3 raw6035step3Labels = mixedMoment B raw6035step4 raw6035step4Labels := by
      have ha : raw6035step4 = raw6035step3 := by apply Matrix.ext; unfold raw6035step4 raw6035step3; decide +kernel
      have hl : raw6035step3Labels = labelEmbedding7 ∘ raw6035step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6035step3 raw6035step3Labels raw6035step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4843 node4843Labels := by rfl

def raw6036 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6036step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6036step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6036step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6036step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw6036step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6036step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw6036step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6036 raw6036Labels = mixedMoment B node5206 node5206Labels := by
  calc
    mixedMoment B raw6036 raw6036Labels = mixedMoment B raw6036step0 raw6036step0Labels := by
      have hz : ∀ j, raw6036 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6036step0 = (fun i j => raw6036 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6036step0 raw6036; decide +kernel
      have hl : raw6036step0Labels = raw6036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6036 raw6036Labels permutation434 hz
    mixedMoment B raw6036step0 raw6036step0Labels = mixedMoment B raw6036step1 raw6036step1Labels := by
      have hz : ∀ j, raw6036step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6036step1 = (fun i j => raw6036step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6036step1 raw6036step0; decide +kernel
      have hl : raw6036step1Labels = raw6036step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6036step0 raw6036step0Labels permutation80 hz
    mixedMoment B raw6036step1 raw6036step1Labels = mixedMoment B raw6036step2 raw6036step2Labels := by
      have ha : raw6036step2 = (fun i j => raw6036step1 (permutation24 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6036step2 raw6036step1; decide +kernel
      have hl : raw6036step2Labels = raw6036step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6036step1 raw6036step1Labels permutation24 permutation5
    mixedMoment B raw6036step2 raw6036step2Labels = mixedMoment B raw6036step3 raw6036step3Labels := by
      have ha : raw6036step3 = raw6036step2 := by apply Matrix.ext; unfold raw6036step3 raw6036step2; decide +kernel
      have hl : raw6036step2Labels = labelEmbedding8 ∘ raw6036step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6036step2 raw6036step2Labels raw6036step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5206 node5206Labels := by rfl

def raw6037 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6037step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6037step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6037step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6037step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6037 raw6037Labels = mixedMoment B node5205 node5205Labels := by
  calc
    mixedMoment B raw6037 raw6037Labels = mixedMoment B raw6037step0 raw6037step0Labels := by
      have hz : ∀ j, raw6037 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6037step0 = (fun i j => raw6037 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6037step0 raw6037; decide +kernel
      have hl : raw6037step0Labels = raw6037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6037 raw6037Labels permutation434 hz
    mixedMoment B raw6037step0 raw6037step0Labels = mixedMoment B raw6037step1 raw6037step1Labels := by
      have ha : raw6037step1 = (fun i j => raw6037step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6037step1 raw6037step0; decide +kernel
      have hl : raw6037step1Labels = raw6037step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6037step0 raw6037step0Labels permutation125 permutation5
    mixedMoment B raw6037step1 raw6037step1Labels = mixedMoment B raw6037step2 raw6037step2Labels := by
      have ha : raw6037step2 = raw6037step1 := by apply Matrix.ext; unfold raw6037step2 raw6037step1; decide +kernel
      have hl : raw6037step1Labels = labelEmbedding8 ∘ raw6037step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6037step1 raw6037step1Labels raw6037step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5205 node5205Labels := by rfl

def raw6038 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6038step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6038step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6038step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6038step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6038step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6038 raw6038Labels = mixedMoment B node5205 node5205Labels := by
  calc
    mixedMoment B raw6038 raw6038Labels = mixedMoment B raw6038step0 raw6038step0Labels := by
      have hz : ∀ j, raw6038 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6038step0 = (fun i j => raw6038 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6038step0 raw6038; decide +kernel
      have hl : raw6038step0Labels = raw6038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6038 raw6038Labels permutation346 hz
    mixedMoment B raw6038step0 raw6038step0Labels = mixedMoment B raw6038step1 raw6038step1Labels := by
      have ha : raw6038step1 = (fun i j => raw6038step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6038step1 raw6038step0; decide +kernel
      have hl : raw6038step1Labels = raw6038step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6038step0 raw6038step0Labels permutation125 permutation5
    mixedMoment B raw6038step1 raw6038step1Labels = mixedMoment B raw6038step2 raw6038step2Labels := by
      have ha : raw6038step2 = raw6038step1 := by apply Matrix.ext; unfold raw6038step2 raw6038step1; decide +kernel
      have hl : raw6038step1Labels = labelEmbedding8 ∘ raw6038step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6038step1 raw6038step1Labels raw6038step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5205 node5205Labels := by rfl

def raw6039 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6039step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6039step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6039step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6039step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw6039step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6039step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw6039step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6039 raw6039Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw6039 raw6039Labels = mixedMoment B raw6039step0 raw6039step0Labels := by
      have hz : ∀ j, raw6039 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6039step0 = (fun i j => raw6039 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6039step0 raw6039; decide +kernel
      have hl : raw6039step0Labels = raw6039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6039 raw6039Labels permutation434 hz
    mixedMoment B raw6039step0 raw6039step0Labels = mixedMoment B raw6039step1 raw6039step1Labels := by
      have hz : ∀ j, raw6039step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6039step1 = (fun i j => raw6039step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6039step1 raw6039step0; decide +kernel
      have hl : raw6039step1Labels = raw6039step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6039step0 raw6039step0Labels permutation80 hz
    mixedMoment B raw6039step1 raw6039step1Labels = mixedMoment B raw6039step2 raw6039step2Labels := by
      have ha : raw6039step2 = (fun i j => raw6039step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6039step2 raw6039step1; decide +kernel
      have hl : raw6039step2Labels = raw6039step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6039step1 raw6039step1Labels permutation8 permutation6
    mixedMoment B raw6039step2 raw6039step2Labels = mixedMoment B raw6039step3 raw6039step3Labels := by
      have ha : raw6039step3 = raw6039step2 := by apply Matrix.ext; unfold raw6039step3 raw6039step2; decide +kernel
      have hl : raw6039step2Labels = labelEmbedding9 ∘ raw6039step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6039step2 raw6039step2Labels raw6039step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw6040 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6040Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6040step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6040step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6040step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6040step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 2, -3], ![2, -2, 0]]
def raw6040step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6040 raw6040Labels = mixedMoment B node3056 node3056Labels := by
  calc
    mixedMoment B raw6040 raw6040Labels = mixedMoment B raw6040step0 raw6040step0Labels := by
      have hz : ∀ j, raw6040 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6040step0 = (fun i j => raw6040 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6040step0 raw6040; decide +kernel
      have hl : raw6040step0Labels = raw6040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6040 raw6040Labels permutation434 hz
    mixedMoment B raw6040step0 raw6040step0Labels = mixedMoment B raw6040step1 raw6040step1Labels := by
      have hz : ∀ j, raw6040step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6040step1 = (fun i j => raw6040step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6040step1 raw6040step0; decide +kernel
      have hl : raw6040step1Labels = raw6040step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6040step0 raw6040step0Labels permutation80 hz
    mixedMoment B raw6040step1 raw6040step1Labels = mixedMoment B raw6040step2 raw6040step2Labels := by
      have ha : raw6040step2 = (fun i j => raw6040step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6040step2 raw6040step1; decide +kernel
      have hl : raw6040step2Labels = raw6040step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6040step1 raw6040step1Labels permutation8 permutation6
    _ = mixedMoment B node3056 node3056Labels := by rfl

def raw6041 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6041Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6041step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6041step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6041 raw6041Labels = mixedMoment B node3079 node3079Labels := by
  calc
    mixedMoment B raw6041 raw6041Labels = mixedMoment B raw6041step0 raw6041step0Labels := by
      have hz : ∀ j, raw6041 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6041step0 = (fun i j => raw6041 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6041step0 raw6041; decide +kernel
      have hl : raw6041step0Labels = raw6041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6041 raw6041Labels permutation434 hz
    mixedMoment B raw6041step0 raw6041step0Labels = mixedMoment B raw6041step1 raw6041step1Labels := by
      have ha : raw6041step1 = (fun i j => raw6041step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6041step1 raw6041step0; decide +kernel
      have hl : raw6041step1Labels = raw6041step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6041step0 raw6041step0Labels permutation32 permutation6
    _ = mixedMoment B node3079 node3079Labels := by rfl

def raw6042 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6042Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6042step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6042 raw6042Labels = mixedMoment B node3079 node3079Labels := by
  calc
    mixedMoment B raw6042 raw6042Labels = mixedMoment B raw6042step0 raw6042step0Labels := by
      have hz : ∀ j, raw6042 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6042step0 = (fun i j => raw6042 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6042step0 raw6042; decide +kernel
      have hl : raw6042step0Labels = raw6042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6042 raw6042Labels permutation346 hz
    mixedMoment B raw6042step0 raw6042step0Labels = mixedMoment B raw6042step1 raw6042step1Labels := by
      have ha : raw6042step1 = (fun i j => raw6042step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6042step1 raw6042step0; decide +kernel
      have hl : raw6042step1Labels = raw6042step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6042step0 raw6042step0Labels permutation32 permutation6
    _ = mixedMoment B node3079 node3079Labels := by rfl

def raw6043 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6043Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6043step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6043step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6043step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6043step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw6043step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6043 raw6043Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw6043 raw6043Labels = mixedMoment B raw6043step0 raw6043step0Labels := by
      have hz : ∀ j, raw6043 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6043step0 = (fun i j => raw6043 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6043step0 raw6043; decide +kernel
      have hl : raw6043step0Labels = raw6043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6043 raw6043Labels permutation434 hz
    mixedMoment B raw6043step0 raw6043step0Labels = mixedMoment B raw6043step1 raw6043step1Labels := by
      have hz : ∀ j, raw6043step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6043step1 = (fun i j => raw6043step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6043step1 raw6043step0; decide +kernel
      have hl : raw6043step1Labels = raw6043step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6043step0 raw6043step0Labels permutation80 hz
    mixedMoment B raw6043step1 raw6043step1Labels = mixedMoment B raw6043step2 raw6043step2Labels := by
      have ha : raw6043step2 = (fun i j => raw6043step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6043step2 raw6043step1; decide +kernel
      have hl : raw6043step2Labels = raw6043step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6043step1 raw6043step1Labels permutation8 permutation6
    _ = mixedMoment B node3103 node3103Labels := by rfl

def raw6044 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6044Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6044step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6044step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6044step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6044step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -3, 1], ![2, 1, -3]]
def raw6044step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6044 raw6044Labels = mixedMoment B node2967 node2967Labels := by
  calc
    mixedMoment B raw6044 raw6044Labels = mixedMoment B raw6044step0 raw6044step0Labels := by
      have hz : ∀ j, raw6044 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6044step0 = (fun i j => raw6044 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6044step0 raw6044; decide +kernel
      have hl : raw6044step0Labels = raw6044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6044 raw6044Labels permutation434 hz
    mixedMoment B raw6044step0 raw6044step0Labels = mixedMoment B raw6044step1 raw6044step1Labels := by
      have hz : ∀ j, raw6044step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6044step1 = (fun i j => raw6044step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6044step1 raw6044step0; decide +kernel
      have hl : raw6044step1Labels = raw6044step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6044step0 raw6044step0Labels permutation80 hz
    mixedMoment B raw6044step1 raw6044step1Labels = mixedMoment B raw6044step2 raw6044step2Labels := by
      have ha : raw6044step2 = (fun i j => raw6044step1 (permutation28 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6044step2 raw6044step1; decide +kernel
      have hl : raw6044step2Labels = raw6044step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6044step1 raw6044step1Labels permutation28 permutation3
    _ = mixedMoment B node2967 node2967Labels := by rfl

def raw6045 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6045Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6045step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6045step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6045step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6045step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![2, -3, 1], ![-2, 0, 2]]
def raw6045step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6045step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw6045step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6045 raw6045Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw6045 raw6045Labels = mixedMoment B raw6045step0 raw6045step0Labels := by
      have hz : ∀ j, raw6045 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6045step0 = (fun i j => raw6045 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6045step0 raw6045; decide +kernel
      have hl : raw6045step0Labels = raw6045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6045 raw6045Labels permutation434 hz
    mixedMoment B raw6045step0 raw6045step0Labels = mixedMoment B raw6045step1 raw6045step1Labels := by
      have hz : ∀ j, raw6045step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6045step1 = (fun i j => raw6045step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6045step1 raw6045step0; decide +kernel
      have hl : raw6045step1Labels = raw6045step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6045step0 raw6045step0Labels permutation80 hz
    mixedMoment B raw6045step1 raw6045step1Labels = mixedMoment B raw6045step2 raw6045step2Labels := by
      have hz : ∀ j, raw6045step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw6045step2 = (fun i j => raw6045step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw6045step2 raw6045step1; decide +kernel
      have hl : raw6045step2Labels = raw6045step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6045step1 raw6045step1Labels permutation14 hz
    mixedMoment B raw6045step2 raw6045step2Labels = mixedMoment B raw6045step3 raw6045step3Labels := by
      have ha : raw6045step3 = (fun i j => raw6045step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6045step3 raw6045step2; decide +kernel
      have hl : raw6045step3Labels = raw6045step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6045step2 raw6045step2Labels permutation2 permutation6
    _ = mixedMoment B node2294 node2294Labels := by rfl

def raw6046 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6046Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6046step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6046step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6046step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6046step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6046step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6046 raw6046Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw6046 raw6046Labels = mixedMoment B raw6046step0 raw6046step0Labels := by
      have hz : ∀ j, raw6046 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6046step0 = (fun i j => raw6046 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6046step0 raw6046; decide +kernel
      have hl : raw6046step0Labels = raw6046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6046 raw6046Labels permutation434 hz
    mixedMoment B raw6046step0 raw6046step0Labels = mixedMoment B raw6046step1 raw6046step1Labels := by
      have hz : ∀ j, raw6046step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6046step1 = (fun i j => raw6046step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6046step1 raw6046step0; decide +kernel
      have hl : raw6046step1Labels = raw6046step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6046step0 raw6046step0Labels permutation56 hz
    mixedMoment B raw6046step1 raw6046step1Labels = mixedMoment B raw6046step2 raw6046step2Labels := by
      have ha : raw6046step2 = (fun i j => raw6046step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6046step2 raw6046step1; decide +kernel
      have hl : raw6046step2Labels = raw6046step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6046step1 raw6046step1Labels permutation8 permutation6
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw6047 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6047Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6047step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6047step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6047step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6047step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6047step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6047 raw6047Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw6047 raw6047Labels = mixedMoment B raw6047step0 raw6047step0Labels := by
      have hz : ∀ j, raw6047 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6047step0 = (fun i j => raw6047 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6047step0 raw6047; decide +kernel
      have hl : raw6047step0Labels = raw6047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6047 raw6047Labels permutation346 hz
    mixedMoment B raw6047step0 raw6047step0Labels = mixedMoment B raw6047step1 raw6047step1Labels := by
      have hz : ∀ j, raw6047step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6047step1 = (fun i j => raw6047step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6047step1 raw6047step0; decide +kernel
      have hl : raw6047step1Labels = raw6047step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6047step0 raw6047step0Labels permutation56 hz
    mixedMoment B raw6047step1 raw6047step1Labels = mixedMoment B raw6047step2 raw6047step2Labels := by
      have ha : raw6047step2 = (fun i j => raw6047step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6047step2 raw6047step1; decide +kernel
      have hl : raw6047step2Labels = raw6047step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6047step1 raw6047step1Labels permutation8 permutation6
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw6048 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6048Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6048step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6048step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6048step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6048step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![-2, 0, 2]]
def raw6048step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6048step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw6048step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6048 raw6048Labels = mixedMoment B node2788 node2788Labels := by
  calc
    mixedMoment B raw6048 raw6048Labels = mixedMoment B raw6048step0 raw6048step0Labels := by
      have hz : ∀ j, raw6048 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6048step0 = (fun i j => raw6048 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6048step0 raw6048; decide +kernel
      have hl : raw6048step0Labels = raw6048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6048 raw6048Labels permutation434 hz
    mixedMoment B raw6048step0 raw6048step0Labels = mixedMoment B raw6048step1 raw6048step1Labels := by
      have hz : ∀ j, raw6048step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6048step1 = (fun i j => raw6048step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6048step1 raw6048step0; decide +kernel
      have hl : raw6048step1Labels = raw6048step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6048step0 raw6048step0Labels permutation80 hz
    mixedMoment B raw6048step1 raw6048step1Labels = mixedMoment B raw6048step2 raw6048step2Labels := by
      have hz : ∀ j, raw6048step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw6048step2 = (fun i j => raw6048step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw6048step2 raw6048step1; decide +kernel
      have hl : raw6048step2Labels = raw6048step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6048step1 raw6048step1Labels permutation14 hz
    mixedMoment B raw6048step2 raw6048step2Labels = mixedMoment B raw6048step3 raw6048step3Labels := by
      have ha : raw6048step3 = (fun i j => raw6048step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6048step3 raw6048step2; decide +kernel
      have hl : raw6048step3Labels = raw6048step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6048step2 raw6048step2Labels permutation2 permutation6
    _ = mixedMoment B node2788 node2788Labels := by rfl

def raw6049 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6049Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6049step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6049step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6049step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6049step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![2, -3, 1], ![-3, 1, 2]]
def raw6049step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6049step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw6049step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6049 raw6049Labels = mixedMoment B node2789 node2789Labels := by
  calc
    mixedMoment B raw6049 raw6049Labels = mixedMoment B raw6049step0 raw6049step0Labels := by
      have hz : ∀ j, raw6049 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6049step0 = (fun i j => raw6049 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6049step0 raw6049; decide +kernel
      have hl : raw6049step0Labels = raw6049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6049 raw6049Labels permutation434 hz
    mixedMoment B raw6049step0 raw6049step0Labels = mixedMoment B raw6049step1 raw6049step1Labels := by
      have hz : ∀ j, raw6049step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6049step1 = (fun i j => raw6049step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6049step1 raw6049step0; decide +kernel
      have hl : raw6049step1Labels = raw6049step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6049step0 raw6049step0Labels permutation80 hz
    mixedMoment B raw6049step1 raw6049step1Labels = mixedMoment B raw6049step2 raw6049step2Labels := by
      have hz : ∀ j, raw6049step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw6049step2 = (fun i j => raw6049step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw6049step2 raw6049step1; decide +kernel
      have hl : raw6049step2Labels = raw6049step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6049step1 raw6049step1Labels permutation14 hz
    mixedMoment B raw6049step2 raw6049step2Labels = mixedMoment B raw6049step3 raw6049step3Labels := by
      have ha : raw6049step3 = (fun i j => raw6049step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6049step3 raw6049step2; decide +kernel
      have hl : raw6049step3Labels = raw6049step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6049step2 raw6049step2Labels permutation2 permutation6
    _ = mixedMoment B node2789 node2789Labels := by rfl

def raw6050 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6050Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6050step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6050step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6050 raw6050Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw6050 raw6050Labels = mixedMoment B raw6050step0 raw6050step0Labels := by
      have hz : ∀ j, raw6050 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6050step0 = (fun i j => raw6050 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6050step0 raw6050; decide +kernel
      have hl : raw6050step0Labels = raw6050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6050 raw6050Labels permutation434 hz
    mixedMoment B raw6050step0 raw6050step0Labels = mixedMoment B raw6050step1 raw6050step1Labels := by
      have ha : raw6050step1 = (fun i j => raw6050step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6050step1 raw6050step0; decide +kernel
      have hl : raw6050step1Labels = raw6050step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6050step0 raw6050step0Labels permutation32 permutation6
    _ = mixedMoment B node2207 node2207Labels := by rfl

def raw6051 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6051Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6051step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6051step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6051 raw6051Labels = mixedMoment B node2674 node2674Labels := by
  calc
    mixedMoment B raw6051 raw6051Labels = mixedMoment B raw6051step0 raw6051step0Labels := by
      have hz : ∀ j, raw6051 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6051step0 = (fun i j => raw6051 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6051step0 raw6051; decide +kernel
      have hl : raw6051step0Labels = raw6051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6051 raw6051Labels permutation434 hz
    mixedMoment B raw6051step0 raw6051step0Labels = mixedMoment B raw6051step1 raw6051step1Labels := by
      have ha : raw6051step1 = (fun i j => raw6051step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6051step1 raw6051step0; decide +kernel
      have hl : raw6051step1Labels = raw6051step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6051step0 raw6051step0Labels permutation32 permutation6
    _ = mixedMoment B node2674 node2674Labels := by rfl

def raw6052 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6052Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6052step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6052 raw6052Labels = mixedMoment B node2696 node2696Labels := by
  calc
    mixedMoment B raw6052 raw6052Labels = mixedMoment B raw6052step0 raw6052step0Labels := by
      have ha : raw6052step0 = (fun i j => raw6052 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6052step0 raw6052; decide +kernel
      have hl : raw6052step0Labels = raw6052Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6052 raw6052Labels permutation158 permutation6
    _ = mixedMoment B node2696 node2696Labels := by rfl

def raw6053 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6053Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6053step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6053step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6053 raw6053Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw6053 raw6053Labels = mixedMoment B raw6053step0 raw6053step0Labels := by
      have hz : ∀ j, raw6053 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6053step0 = (fun i j => raw6053 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6053step0 raw6053; decide +kernel
      have hl : raw6053step0Labels = raw6053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6053 raw6053Labels permutation434 hz
    mixedMoment B raw6053step0 raw6053step0Labels = mixedMoment B raw6053step1 raw6053step1Labels := by
      have ha : raw6053step1 = (fun i j => raw6053step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6053step1 raw6053step0; decide +kernel
      have hl : raw6053step1Labels = raw6053step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6053step0 raw6053step0Labels permutation32 permutation6
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw6054 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6054Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6054step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw6054step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6054 raw6054Labels = mixedMoment B node2725 node2725Labels := by
  calc
    mixedMoment B raw6054 raw6054Labels = mixedMoment B raw6054step0 raw6054step0Labels := by
      have hz : ∀ j, raw6054 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6054step0 = (fun i j => raw6054 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6054step0 raw6054; decide +kernel
      have hl : raw6054step0Labels = raw6054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6054 raw6054Labels permutation434 hz
    mixedMoment B raw6054step0 raw6054step0Labels = mixedMoment B raw6054step1 raw6054step1Labels := by
      have ha : raw6054step1 = (fun i j => raw6054step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6054step1 raw6054step0; decide +kernel
      have hl : raw6054step1Labels = raw6054step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6054step0 raw6054step0Labels permutation32 permutation6
    _ = mixedMoment B node2725 node2725Labels := by rfl

def raw6055 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6055Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6055step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6055step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6055 raw6055Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw6055 raw6055Labels = mixedMoment B raw6055step0 raw6055step0Labels := by
      have hz : ∀ j, raw6055 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6055step0 = (fun i j => raw6055 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6055step0 raw6055; decide +kernel
      have hl : raw6055step0Labels = raw6055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6055 raw6055Labels permutation346 hz
    mixedMoment B raw6055step0 raw6055step0Labels = mixedMoment B raw6055step1 raw6055step1Labels := by
      have ha : raw6055step1 = (fun i j => raw6055step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6055step1 raw6055step0; decide +kernel
      have hl : raw6055step1Labels = raw6055step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6055step0 raw6055step0Labels permutation32 permutation6
    _ = mixedMoment B node2207 node2207Labels := by rfl

def raw6056 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6056Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6056step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6056 raw6056Labels = mixedMoment B node2674 node2674Labels := by
  calc
    mixedMoment B raw6056 raw6056Labels = mixedMoment B raw6056step0 raw6056step0Labels := by
      have hz : ∀ j, raw6056 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6056step0 = (fun i j => raw6056 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6056step0 raw6056; decide +kernel
      have hl : raw6056step0Labels = raw6056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6056 raw6056Labels permutation346 hz
    mixedMoment B raw6056step0 raw6056step0Labels = mixedMoment B raw6056step1 raw6056step1Labels := by
      have ha : raw6056step1 = (fun i j => raw6056step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6056step1 raw6056step0; decide +kernel
      have hl : raw6056step1Labels = raw6056step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6056step0 raw6056step0Labels permutation32 permutation6
    _ = mixedMoment B node2674 node2674Labels := by rfl

def raw6057 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6057Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6057step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6057 raw6057Labels = mixedMoment B node2696 node2696Labels := by
  calc
    mixedMoment B raw6057 raw6057Labels = mixedMoment B raw6057step0 raw6057step0Labels := by
      have ha : raw6057step0 = (fun i j => raw6057 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6057step0 raw6057; decide +kernel
      have hl : raw6057step0Labels = raw6057Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6057 raw6057Labels permutation152 permutation6
    _ = mixedMoment B node2696 node2696Labels := by rfl

def raw6058 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6058Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6058step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6058step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6058 raw6058Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw6058 raw6058Labels = mixedMoment B raw6058step0 raw6058step0Labels := by
      have hz : ∀ j, raw6058 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6058step0 = (fun i j => raw6058 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6058step0 raw6058; decide +kernel
      have hl : raw6058step0Labels = raw6058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6058 raw6058Labels permutation346 hz
    mixedMoment B raw6058step0 raw6058step0Labels = mixedMoment B raw6058step1 raw6058step1Labels := by
      have ha : raw6058step1 = (fun i j => raw6058step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6058step1 raw6058step0; decide +kernel
      have hl : raw6058step1Labels = raw6058step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6058step0 raw6058step0Labels permutation32 permutation6
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw6059 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6059Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6059step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw6059step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6059 raw6059Labels = mixedMoment B node2725 node2725Labels := by
  calc
    mixedMoment B raw6059 raw6059Labels = mixedMoment B raw6059step0 raw6059step0Labels := by
      have hz : ∀ j, raw6059 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6059step0 = (fun i j => raw6059 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6059step0 raw6059; decide +kernel
      have hl : raw6059step0Labels = raw6059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6059 raw6059Labels permutation346 hz
    mixedMoment B raw6059step0 raw6059step0Labels = mixedMoment B raw6059step1 raw6059step1Labels := by
      have ha : raw6059step1 = (fun i j => raw6059step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6059step1 raw6059step0; decide +kernel
      have hl : raw6059step1Labels = raw6059step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6059step0 raw6059step0Labels permutation32 permutation6
    _ = mixedMoment B node2725 node2725Labels := by rfl

def raw6060 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6060Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6060step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6060step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6060step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6060step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 0, 1], ![-2, 2, 0]]
def raw6060step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6060step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw6060step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6060 raw6060Labels = mixedMoment B node1746 node1746Labels := by
  calc
    mixedMoment B raw6060 raw6060Labels = mixedMoment B raw6060step0 raw6060step0Labels := by
      have hz : ∀ j, raw6060 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6060step0 = (fun i j => raw6060 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6060step0 raw6060; decide +kernel
      have hl : raw6060step0Labels = raw6060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6060 raw6060Labels permutation434 hz
    mixedMoment B raw6060step0 raw6060step0Labels = mixedMoment B raw6060step1 raw6060step1Labels := by
      have hz : ∀ j, raw6060step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6060step1 = (fun i j => raw6060step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6060step1 raw6060step0; decide +kernel
      have hl : raw6060step1Labels = raw6060step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6060step0 raw6060step0Labels permutation80 hz
    mixedMoment B raw6060step1 raw6060step1Labels = mixedMoment B raw6060step2 raw6060step2Labels := by
      have ha : raw6060step2 = (fun i j => raw6060step1 (permutation20 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6060step2 raw6060step1; decide +kernel
      have hl : raw6060step2Labels = raw6060step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6060step1 raw6060step1Labels permutation20 permutation3
    mixedMoment B raw6060step2 raw6060step2Labels = mixedMoment B raw6060step3 raw6060step3Labels := by
      have ha : raw6060step3 = -raw6060step2 := by apply Matrix.ext; change ∀ i j, raw6060step3 i j = -(raw6060step2 i j); unfold raw6060step3 raw6060step2; decide +kernel
      have hl : raw6060step3Labels = raw6060step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1746 node1746Labels := by rfl

def raw6061 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6061Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6061step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6061step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6061step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6061step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw6061step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6061step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![2, -2, 0], ![2, 0, -2]]
def raw6061step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6061 raw6061Labels = mixedMoment B node1660 node1660Labels := by
  calc
    mixedMoment B raw6061 raw6061Labels = mixedMoment B raw6061step0 raw6061step0Labels := by
      have hz : ∀ j, raw6061 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6061step0 = (fun i j => raw6061 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6061step0 raw6061; decide +kernel
      have hl : raw6061step0Labels = raw6061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6061 raw6061Labels permutation434 hz
    mixedMoment B raw6061step0 raw6061step0Labels = mixedMoment B raw6061step1 raw6061step1Labels := by
      have hz : ∀ j, raw6061step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6061step1 = (fun i j => raw6061step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6061step1 raw6061step0; decide +kernel
      have hl : raw6061step1Labels = raw6061step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6061step0 raw6061step0Labels permutation80 hz
    mixedMoment B raw6061step1 raw6061step1Labels = mixedMoment B raw6061step2 raw6061step2Labels := by
      have ha : raw6061step2 = (fun i j => raw6061step1 (permutation21 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6061step2 raw6061step1; decide +kernel
      have hl : raw6061step2Labels = raw6061step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6061step1 raw6061step1Labels permutation21 permutation3
    mixedMoment B raw6061step2 raw6061step2Labels = mixedMoment B raw6061step3 raw6061step3Labels := by
      have ha : raw6061step3 = -raw6061step2 := by apply Matrix.ext; change ∀ i j, raw6061step3 i j = -(raw6061step2 i j); unfold raw6061step3 raw6061step2; decide +kernel
      have hl : raw6061step3Labels = raw6061step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1660 node1660Labels := by rfl

def raw6062 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6062Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6062step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw6062step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6062step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6062step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6062 raw6062Labels = mixedMoment B node1658 node1658Labels := by
  calc
    mixedMoment B raw6062 raw6062Labels = mixedMoment B raw6062step0 raw6062step0Labels := by
      have hz : ∀ j, raw6062 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6062step0 = (fun i j => raw6062 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6062step0 raw6062; decide +kernel
      have hl : raw6062step0Labels = raw6062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6062 raw6062Labels permutation434 hz
    mixedMoment B raw6062step0 raw6062step0Labels = mixedMoment B raw6062step1 raw6062step1Labels := by
      have ha : raw6062step1 = (fun i j => raw6062step0 (permutation104 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6062step1 raw6062step0; decide +kernel
      have hl : raw6062step1Labels = raw6062step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6062step0 raw6062step0Labels permutation104 permutation3
    mixedMoment B raw6062step1 raw6062step1Labels = mixedMoment B raw6062step2 raw6062step2Labels := by
      have ha : raw6062step2 = -raw6062step1 := by apply Matrix.ext; change ∀ i j, raw6062step2 i j = -(raw6062step1 i j); unfold raw6062step2 raw6062step1; decide +kernel
      have hl : raw6062step2Labels = raw6062step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1658 node1658Labels := by rfl

def raw6063 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6063Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6063step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw6063step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6063step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6063step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6063 raw6063Labels = mixedMoment B node1658 node1658Labels := by
  calc
    mixedMoment B raw6063 raw6063Labels = mixedMoment B raw6063step0 raw6063step0Labels := by
      have hz : ∀ j, raw6063 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6063step0 = (fun i j => raw6063 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6063step0 raw6063; decide +kernel
      have hl : raw6063step0Labels = raw6063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6063 raw6063Labels permutation346 hz
    mixedMoment B raw6063step0 raw6063step0Labels = mixedMoment B raw6063step1 raw6063step1Labels := by
      have ha : raw6063step1 = (fun i j => raw6063step0 (permutation104 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6063step1 raw6063step0; decide +kernel
      have hl : raw6063step1Labels = raw6063step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6063step0 raw6063step0Labels permutation104 permutation3
    mixedMoment B raw6063step1 raw6063step1Labels = mixedMoment B raw6063step2 raw6063step2Labels := by
      have ha : raw6063step2 = -raw6063step1 := by apply Matrix.ext; change ∀ i j, raw6063step2 i j = -(raw6063step1 i j); unfold raw6063step2 raw6063step1; decide +kernel
      have hl : raw6063step2Labels = raw6063step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1658 node1658Labels := by rfl

def raw6064 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![-3, 1, 2]]
def raw6064Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -4, 1], ![-3, 1, 2]]
def raw6064step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6064step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -4, 1], ![-3, 1, 2]]
def raw6064step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6064step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw6064step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6064step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, 0, -1], ![3, -2, -1]]
def raw6064step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6064 raw6064Labels = mixedMoment B node1659 node1659Labels := by
  calc
    mixedMoment B raw6064 raw6064Labels = mixedMoment B raw6064step0 raw6064step0Labels := by
      have hz : ∀ j, raw6064 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6064step0 = (fun i j => raw6064 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6064step0 raw6064; decide +kernel
      have hl : raw6064step0Labels = raw6064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6064 raw6064Labels permutation434 hz
    mixedMoment B raw6064step0 raw6064step0Labels = mixedMoment B raw6064step1 raw6064step1Labels := by
      have hz : ∀ j, raw6064step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6064step1 = (fun i j => raw6064step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6064step1 raw6064step0; decide +kernel
      have hl : raw6064step1Labels = raw6064step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6064step0 raw6064step0Labels permutation80 hz
    mixedMoment B raw6064step1 raw6064step1Labels = mixedMoment B raw6064step2 raw6064step2Labels := by
      have ha : raw6064step2 = (fun i j => raw6064step1 (permutation20 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6064step2 raw6064step1; decide +kernel
      have hl : raw6064step2Labels = raw6064step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6064step1 raw6064step1Labels permutation20 permutation3
    mixedMoment B raw6064step2 raw6064step2Labels = mixedMoment B raw6064step3 raw6064step3Labels := by
      have ha : raw6064step3 = -raw6064step2 := by apply Matrix.ext; change ∀ i j, raw6064step3 i j = -(raw6064step2 i j); unfold raw6064step3 raw6064step2; decide +kernel
      have hl : raw6064step3Labels = raw6064step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1659 node1659Labels := by rfl

def raw6065 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6065Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6065step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6065step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6065step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6065step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw6065step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6065 raw6065Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw6065 raw6065Labels = mixedMoment B raw6065step0 raw6065step0Labels := by
      have hz : ∀ j, raw6065 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6065step0 = (fun i j => raw6065 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6065step0 raw6065; decide +kernel
      have hl : raw6065step0Labels = raw6065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6065 raw6065Labels permutation434 hz
    mixedMoment B raw6065step0 raw6065step0Labels = mixedMoment B raw6065step1 raw6065step1Labels := by
      have hz : ∀ j, raw6065step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6065step1 = (fun i j => raw6065step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6065step1 raw6065step0; decide +kernel
      have hl : raw6065step1Labels = raw6065step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6065step0 raw6065step0Labels permutation80 hz
    mixedMoment B raw6065step1 raw6065step1Labels = mixedMoment B raw6065step2 raw6065step2Labels := by
      have ha : raw6065step2 = (fun i j => raw6065step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6065step2 raw6065step1; decide +kernel
      have hl : raw6065step2Labels = raw6065step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6065step1 raw6065step1Labels permutation8 permutation6
    _ = mixedMoment B node2230 node2230Labels := by rfl

def raw6066 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6066Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6066step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6066step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6066step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6066step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw6066step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6066 raw6066Labels = mixedMoment B node2687 node2687Labels := by
  calc
    mixedMoment B raw6066 raw6066Labels = mixedMoment B raw6066step0 raw6066step0Labels := by
      have hz : ∀ j, raw6066 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6066step0 = (fun i j => raw6066 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6066step0 raw6066; decide +kernel
      have hl : raw6066step0Labels = raw6066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6066 raw6066Labels permutation434 hz
    mixedMoment B raw6066step0 raw6066step0Labels = mixedMoment B raw6066step1 raw6066step1Labels := by
      have hz : ∀ j, raw6066step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6066step1 = (fun i j => raw6066step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6066step1 raw6066step0; decide +kernel
      have hl : raw6066step1Labels = raw6066step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6066step0 raw6066step0Labels permutation80 hz
    mixedMoment B raw6066step1 raw6066step1Labels = mixedMoment B raw6066step2 raw6066step2Labels := by
      have ha : raw6066step2 = (fun i j => raw6066step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6066step2 raw6066step1; decide +kernel
      have hl : raw6066step2Labels = raw6066step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6066step1 raw6066step1Labels permutation8 permutation6
    _ = mixedMoment B node2687 node2687Labels := by rfl

def raw6067 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6067Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6067step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6067step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw6067step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6067 raw6067Labels = mixedMoment B node2706 node2706Labels := by
  calc
    mixedMoment B raw6067 raw6067Labels = mixedMoment B raw6067step0 raw6067step0Labels := by
      have hz : ∀ j, raw6067 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6067step0 = (fun i j => raw6067 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6067step0 raw6067; decide +kernel
      have hl : raw6067step0Labels = raw6067Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6067 raw6067Labels permutation434 hz
    mixedMoment B raw6067step0 raw6067step0Labels = mixedMoment B raw6067step1 raw6067step1Labels := by
      have ha : raw6067step1 = (fun i j => raw6067step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6067step1 raw6067step0; decide +kernel
      have hl : raw6067step1Labels = raw6067step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6067step0 raw6067step0Labels permutation32 permutation6
    _ = mixedMoment B node2706 node2706Labels := by rfl

def raw6068 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6068Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6068step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6068step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw6068step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6068 raw6068Labels = mixedMoment B node2706 node2706Labels := by
  calc
    mixedMoment B raw6068 raw6068Labels = mixedMoment B raw6068step0 raw6068step0Labels := by
      have hz : ∀ j, raw6068 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6068step0 = (fun i j => raw6068 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6068step0 raw6068; decide +kernel
      have hl : raw6068step0Labels = raw6068Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6068 raw6068Labels permutation346 hz
    mixedMoment B raw6068step0 raw6068step0Labels = mixedMoment B raw6068step1 raw6068step1Labels := by
      have ha : raw6068step1 = (fun i j => raw6068step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6068step1 raw6068step0; decide +kernel
      have hl : raw6068step1Labels = raw6068step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6068step0 raw6068step0Labels permutation32 permutation6
    _ = mixedMoment B node2706 node2706Labels := by rfl

def raw6069 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6069Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6069step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6069step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6069step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6069step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw6069step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6069 raw6069Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw6069 raw6069Labels = mixedMoment B raw6069step0 raw6069step0Labels := by
      have hz : ∀ j, raw6069 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6069step0 = (fun i j => raw6069 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6069step0 raw6069; decide +kernel
      have hl : raw6069step0Labels = raw6069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6069 raw6069Labels permutation434 hz
    mixedMoment B raw6069step0 raw6069step0Labels = mixedMoment B raw6069step1 raw6069step1Labels := by
      have hz : ∀ j, raw6069step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6069step1 = (fun i j => raw6069step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6069step1 raw6069step0; decide +kernel
      have hl : raw6069step1Labels = raw6069step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6069step0 raw6069step0Labels permutation80 hz
    mixedMoment B raw6069step1 raw6069step1Labels = mixedMoment B raw6069step2 raw6069step2Labels := by
      have ha : raw6069step2 = (fun i j => raw6069step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6069step2 raw6069step1; decide +kernel
      have hl : raw6069step2Labels = raw6069step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6069step1 raw6069step1Labels permutation8 permutation6
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw6070 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6070Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6070step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6070step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6070step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6070step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw6070step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6070step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw6070step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6070 raw6070Labels = mixedMoment B node2771 node2771Labels := by
  calc
    mixedMoment B raw6070 raw6070Labels = mixedMoment B raw6070step0 raw6070step0Labels := by
      have hz : ∀ j, raw6070 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6070step0 = (fun i j => raw6070 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6070step0 raw6070; decide +kernel
      have hl : raw6070step0Labels = raw6070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6070 raw6070Labels permutation434 hz
    mixedMoment B raw6070step0 raw6070step0Labels = mixedMoment B raw6070step1 raw6070step1Labels := by
      have hz : ∀ j, raw6070step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6070step1 = (fun i j => raw6070step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6070step1 raw6070step0; decide +kernel
      have hl : raw6070step1Labels = raw6070step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6070step0 raw6070step0Labels permutation80 hz
    mixedMoment B raw6070step1 raw6070step1Labels = mixedMoment B raw6070step2 raw6070step2Labels := by
      have ha : raw6070step2 = (fun i j => raw6070step1 (permutation24 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6070step2 raw6070step1; decide +kernel
      have hl : raw6070step2Labels = raw6070step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6070step1 raw6070step1Labels permutation24 permutation5
    mixedMoment B raw6070step2 raw6070step2Labels = mixedMoment B raw6070step3 raw6070step3Labels := by
      have ha : raw6070step3 = raw6070step2 := by apply Matrix.ext; unfold raw6070step3 raw6070step2; decide +kernel
      have hl : raw6070step2Labels = labelEmbedding1 ∘ raw6070step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6070step2 raw6070step2Labels raw6070step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2771 node2771Labels := by rfl

def raw6071 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6071Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6071step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6071step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw6071step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6071step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw6071step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6071 raw6071Labels = mixedMoment B node2748 node2748Labels := by
  calc
    mixedMoment B raw6071 raw6071Labels = mixedMoment B raw6071step0 raw6071step0Labels := by
      have hz : ∀ j, raw6071 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6071step0 = (fun i j => raw6071 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6071step0 raw6071; decide +kernel
      have hl : raw6071step0Labels = raw6071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6071 raw6071Labels permutation434 hz
    mixedMoment B raw6071step0 raw6071step0Labels = mixedMoment B raw6071step1 raw6071step1Labels := by
      have ha : raw6071step1 = (fun i j => raw6071step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6071step1 raw6071step0; decide +kernel
      have hl : raw6071step1Labels = raw6071step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6071step0 raw6071step0Labels permutation32 permutation7
    mixedMoment B raw6071step1 raw6071step1Labels = mixedMoment B raw6071step2 raw6071step2Labels := by
      have ha : raw6071step2 = raw6071step1 := by apply Matrix.ext; unfold raw6071step2 raw6071step1; decide +kernel
      have hl : raw6071step1Labels = labelEmbedding1 ∘ raw6071step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6071step1 raw6071step1Labels raw6071step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2748 node2748Labels := by rfl

def raw6072 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6072Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6072step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6072step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw6072step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6072step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw6072step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6072 raw6072Labels = mixedMoment B node2748 node2748Labels := by
  calc
    mixedMoment B raw6072 raw6072Labels = mixedMoment B raw6072step0 raw6072step0Labels := by
      have hz : ∀ j, raw6072 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6072step0 = (fun i j => raw6072 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6072step0 raw6072; decide +kernel
      have hl : raw6072step0Labels = raw6072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6072 raw6072Labels permutation346 hz
    mixedMoment B raw6072step0 raw6072step0Labels = mixedMoment B raw6072step1 raw6072step1Labels := by
      have ha : raw6072step1 = (fun i j => raw6072step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6072step1 raw6072step0; decide +kernel
      have hl : raw6072step1Labels = raw6072step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6072step0 raw6072step0Labels permutation32 permutation7
    mixedMoment B raw6072step1 raw6072step1Labels = mixedMoment B raw6072step2 raw6072step2Labels := by
      have ha : raw6072step2 = raw6072step1 := by apply Matrix.ext; unfold raw6072step2 raw6072step1; decide +kernel
      have hl : raw6072step1Labels = labelEmbedding1 ∘ raw6072step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6072step1 raw6072step1Labels raw6072step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2748 node2748Labels := by rfl

def raw6073 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6073Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6073step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6073step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6073step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6073step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6073step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6073step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6073step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6073 raw6073Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw6073 raw6073Labels = mixedMoment B raw6073step0 raw6073step0Labels := by
      have hz : ∀ j, raw6073 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6073step0 = (fun i j => raw6073 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6073step0 raw6073; decide +kernel
      have hl : raw6073step0Labels = raw6073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6073 raw6073Labels permutation434 hz
    mixedMoment B raw6073step0 raw6073step0Labels = mixedMoment B raw6073step1 raw6073step1Labels := by
      have hz : ∀ j, raw6073step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6073step1 = (fun i j => raw6073step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6073step1 raw6073step0; decide +kernel
      have hl : raw6073step1Labels = raw6073step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6073step0 raw6073step0Labels permutation80 hz
    mixedMoment B raw6073step1 raw6073step1Labels = mixedMoment B raw6073step2 raw6073step2Labels := by
      have ha : raw6073step2 = (fun i j => raw6073step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6073step2 raw6073step1; decide +kernel
      have hl : raw6073step2Labels = raw6073step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6073step1 raw6073step1Labels permutation8 permutation7
    mixedMoment B raw6073step2 raw6073step2Labels = mixedMoment B raw6073step3 raw6073step3Labels := by
      have ha : raw6073step3 = raw6073step2 := by apply Matrix.ext; unfold raw6073step3 raw6073step2; decide +kernel
      have hl : raw6073step2Labels = labelEmbedding1 ∘ raw6073step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6073step2 raw6073step2Labels raw6073step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw6074 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6074Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6074step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6074step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6074step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6074step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw6074step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6074step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw6074step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6074 raw6074Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw6074 raw6074Labels = mixedMoment B raw6074step0 raw6074step0Labels := by
      have hz : ∀ j, raw6074 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6074step0 = (fun i j => raw6074 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6074step0 raw6074; decide +kernel
      have hl : raw6074step0Labels = raw6074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6074 raw6074Labels permutation434 hz
    mixedMoment B raw6074step0 raw6074step0Labels = mixedMoment B raw6074step1 raw6074step1Labels := by
      have hz : ∀ j, raw6074step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6074step1 = (fun i j => raw6074step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6074step1 raw6074step0; decide +kernel
      have hl : raw6074step1Labels = raw6074step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6074step0 raw6074step0Labels permutation80 hz
    mixedMoment B raw6074step1 raw6074step1Labels = mixedMoment B raw6074step2 raw6074step2Labels := by
      have ha : raw6074step2 = (fun i j => raw6074step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6074step2 raw6074step1; decide +kernel
      have hl : raw6074step2Labels = raw6074step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6074step1 raw6074step1Labels permutation8 permutation7
    mixedMoment B raw6074step2 raw6074step2Labels = mixedMoment B raw6074step3 raw6074step3Labels := by
      have ha : raw6074step3 = raw6074step2 := by apply Matrix.ext; unfold raw6074step3 raw6074step2; decide +kernel
      have hl : raw6074step2Labels = labelEmbedding1 ∘ raw6074step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6074step2 raw6074step2Labels raw6074step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2761 node2761Labels := by rfl

def raw6075 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6075Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6075step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6075step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6075step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6075step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![2, -3, 1], ![-2, 0, 2]]
def raw6075step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6075step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw6075step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6075step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw6075step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6075 raw6075Labels = mixedMoment B node2778 node2778Labels := by
  calc
    mixedMoment B raw6075 raw6075Labels = mixedMoment B raw6075step0 raw6075step0Labels := by
      have hz : ∀ j, raw6075 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6075step0 = (fun i j => raw6075 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6075step0 raw6075; decide +kernel
      have hl : raw6075step0Labels = raw6075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6075 raw6075Labels permutation434 hz
    mixedMoment B raw6075step0 raw6075step0Labels = mixedMoment B raw6075step1 raw6075step1Labels := by
      have hz : ∀ j, raw6075step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6075step1 = (fun i j => raw6075step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6075step1 raw6075step0; decide +kernel
      have hl : raw6075step1Labels = raw6075step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6075step0 raw6075step0Labels permutation80 hz
    mixedMoment B raw6075step1 raw6075step1Labels = mixedMoment B raw6075step2 raw6075step2Labels := by
      have hz : ∀ j, raw6075step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw6075step2 = (fun i j => raw6075step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw6075step2 raw6075step1; decide +kernel
      have hl : raw6075step2Labels = raw6075step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6075step1 raw6075step1Labels permutation14 hz
    mixedMoment B raw6075step2 raw6075step2Labels = mixedMoment B raw6075step3 raw6075step3Labels := by
      have ha : raw6075step3 = (fun i j => raw6075step2 (permutation5 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6075step3 raw6075step2; decide +kernel
      have hl : raw6075step3Labels = raw6075step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6075step2 raw6075step2Labels permutation5 permutation5
    mixedMoment B raw6075step3 raw6075step3Labels = mixedMoment B raw6075step4 raw6075step4Labels := by
      have ha : raw6075step4 = raw6075step3 := by apply Matrix.ext; unfold raw6075step4 raw6075step3; decide +kernel
      have hl : raw6075step3Labels = labelEmbedding1 ∘ raw6075step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6075step3 raw6075step3Labels raw6075step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2778 node2778Labels := by rfl

def raw6076 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6076Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6076step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6076step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6076step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6076step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw6076step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6076step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw6076step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6076 raw6076Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw6076 raw6076Labels = mixedMoment B raw6076step0 raw6076step0Labels := by
      have hz : ∀ j, raw6076 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6076step0 = (fun i j => raw6076 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6076step0 raw6076; decide +kernel
      have hl : raw6076step0Labels = raw6076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6076 raw6076Labels permutation434 hz
    mixedMoment B raw6076step0 raw6076step0Labels = mixedMoment B raw6076step1 raw6076step1Labels := by
      have hz : ∀ j, raw6076step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6076step1 = (fun i j => raw6076step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6076step1 raw6076step0; decide +kernel
      have hl : raw6076step1Labels = raw6076step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6076step0 raw6076step0Labels permutation56 hz
    mixedMoment B raw6076step1 raw6076step1Labels = mixedMoment B raw6076step2 raw6076step2Labels := by
      have ha : raw6076step2 = (fun i j => raw6076step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6076step2 raw6076step1; decide +kernel
      have hl : raw6076step2Labels = raw6076step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6076step1 raw6076step1Labels permutation25 permutation5
    mixedMoment B raw6076step2 raw6076step2Labels = mixedMoment B raw6076step3 raw6076step3Labels := by
      have ha : raw6076step3 = raw6076step2 := by apply Matrix.ext; unfold raw6076step3 raw6076step2; decide +kernel
      have hl : raw6076step2Labels = labelEmbedding1 ∘ raw6076step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6076step2 raw6076step2Labels raw6076step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2777 node2777Labels := by rfl

def raw6077 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6077Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6077step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6077step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6077step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6077step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw6077step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6077step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw6077step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6077 raw6077Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw6077 raw6077Labels = mixedMoment B raw6077step0 raw6077step0Labels := by
      have hz : ∀ j, raw6077 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6077step0 = (fun i j => raw6077 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6077step0 raw6077; decide +kernel
      have hl : raw6077step0Labels = raw6077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6077 raw6077Labels permutation346 hz
    mixedMoment B raw6077step0 raw6077step0Labels = mixedMoment B raw6077step1 raw6077step1Labels := by
      have hz : ∀ j, raw6077step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6077step1 = (fun i j => raw6077step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6077step1 raw6077step0; decide +kernel
      have hl : raw6077step1Labels = raw6077step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6077step0 raw6077step0Labels permutation56 hz
    mixedMoment B raw6077step1 raw6077step1Labels = mixedMoment B raw6077step2 raw6077step2Labels := by
      have ha : raw6077step2 = (fun i j => raw6077step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6077step2 raw6077step1; decide +kernel
      have hl : raw6077step2Labels = raw6077step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6077step1 raw6077step1Labels permutation25 permutation5
    mixedMoment B raw6077step2 raw6077step2Labels = mixedMoment B raw6077step3 raw6077step3Labels := by
      have ha : raw6077step3 = raw6077step2 := by apply Matrix.ext; unfold raw6077step3 raw6077step2; decide +kernel
      have hl : raw6077step2Labels = labelEmbedding1 ∘ raw6077step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6077step2 raw6077step2Labels raw6077step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2777 node2777Labels := by rfl

def raw6078 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6078Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6078step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6078step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6078step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6078step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![-2, 0, 2]]
def raw6078step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6078step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6078step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6078step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6078step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6078 raw6078Labels = mixedMoment B node3121 node3121Labels := by
  calc
    mixedMoment B raw6078 raw6078Labels = mixedMoment B raw6078step0 raw6078step0Labels := by
      have hz : ∀ j, raw6078 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6078step0 = (fun i j => raw6078 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6078step0 raw6078; decide +kernel
      have hl : raw6078step0Labels = raw6078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6078 raw6078Labels permutation434 hz
    mixedMoment B raw6078step0 raw6078step0Labels = mixedMoment B raw6078step1 raw6078step1Labels := by
      have hz : ∀ j, raw6078step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6078step1 = (fun i j => raw6078step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6078step1 raw6078step0; decide +kernel
      have hl : raw6078step1Labels = raw6078step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6078step0 raw6078step0Labels permutation80 hz
    mixedMoment B raw6078step1 raw6078step1Labels = mixedMoment B raw6078step2 raw6078step2Labels := by
      have hz : ∀ j, raw6078step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw6078step2 = (fun i j => raw6078step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw6078step2 raw6078step1; decide +kernel
      have hl : raw6078step2Labels = raw6078step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6078step1 raw6078step1Labels permutation14 hz
    mixedMoment B raw6078step2 raw6078step2Labels = mixedMoment B raw6078step3 raw6078step3Labels := by
      have ha : raw6078step3 = (fun i j => raw6078step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6078step3 raw6078step2; decide +kernel
      have hl : raw6078step3Labels = raw6078step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6078step2 raw6078step2Labels permutation2 permutation7
    mixedMoment B raw6078step3 raw6078step3Labels = mixedMoment B raw6078step4 raw6078step4Labels := by
      have ha : raw6078step4 = raw6078step3 := by apply Matrix.ext; unfold raw6078step4 raw6078step3; decide +kernel
      have hl : raw6078step3Labels = labelEmbedding1 ∘ raw6078step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6078step3 raw6078step3Labels raw6078step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3121 node3121Labels := by rfl

def raw6079 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6079Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6079step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6079step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6079step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6079step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![2, -3, 1], ![-3, 1, 2]]
def raw6079step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6079step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw6079step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6079step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw6079step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6079 raw6079Labels = mixedMoment B node2789 node2789Labels := by
  calc
    mixedMoment B raw6079 raw6079Labels = mixedMoment B raw6079step0 raw6079step0Labels := by
      have hz : ∀ j, raw6079 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6079step0 = (fun i j => raw6079 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6079step0 raw6079; decide +kernel
      have hl : raw6079step0Labels = raw6079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6079 raw6079Labels permutation434 hz
    mixedMoment B raw6079step0 raw6079step0Labels = mixedMoment B raw6079step1 raw6079step1Labels := by
      have hz : ∀ j, raw6079step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6079step1 = (fun i j => raw6079step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6079step1 raw6079step0; decide +kernel
      have hl : raw6079step1Labels = raw6079step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6079step0 raw6079step0Labels permutation80 hz
    mixedMoment B raw6079step1 raw6079step1Labels = mixedMoment B raw6079step2 raw6079step2Labels := by
      have hz : ∀ j, raw6079step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw6079step2 = (fun i j => raw6079step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw6079step2 raw6079step1; decide +kernel
      have hl : raw6079step2Labels = raw6079step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6079step1 raw6079step1Labels permutation14 hz
    mixedMoment B raw6079step2 raw6079step2Labels = mixedMoment B raw6079step3 raw6079step3Labels := by
      have ha : raw6079step3 = (fun i j => raw6079step2 (permutation5 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6079step3 raw6079step2; decide +kernel
      have hl : raw6079step3Labels = raw6079step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6079step2 raw6079step2Labels permutation5 permutation5
    mixedMoment B raw6079step3 raw6079step3Labels = mixedMoment B raw6079step4 raw6079step4Labels := by
      have ha : raw6079step4 = raw6079step3 := by apply Matrix.ext; unfold raw6079step4 raw6079step3; decide +kernel
      have hl : raw6079step3Labels = labelEmbedding1 ∘ raw6079step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6079step3 raw6079step3Labels raw6079step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2789 node2789Labels := by rfl

def raw6080 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6080Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6080step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6080step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6080step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6080step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6080step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6080 raw6080Labels = mixedMoment B node2497 node2497Labels := by
  calc
    mixedMoment B raw6080 raw6080Labels = mixedMoment B raw6080step0 raw6080step0Labels := by
      have hz : ∀ j, raw6080 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6080step0 = (fun i j => raw6080 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6080step0 raw6080; decide +kernel
      have hl : raw6080step0Labels = raw6080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6080 raw6080Labels permutation434 hz
    mixedMoment B raw6080step0 raw6080step0Labels = mixedMoment B raw6080step1 raw6080step1Labels := by
      have ha : raw6080step1 = (fun i j => raw6080step0 (permutation121 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6080step1 raw6080step0; decide +kernel
      have hl : raw6080step1Labels = raw6080step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6080step0 raw6080step0Labels permutation121 permutation5
    mixedMoment B raw6080step1 raw6080step1Labels = mixedMoment B raw6080step2 raw6080step2Labels := by
      have ha : raw6080step2 = raw6080step1 := by apply Matrix.ext; unfold raw6080step2 raw6080step1; decide +kernel
      have hl : raw6080step1Labels = labelEmbedding1 ∘ raw6080step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6080step1 raw6080step1Labels raw6080step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2497 node2497Labels := by rfl

def raw6081 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6081Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6081step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6081step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw6081step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6081step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw6081step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6081 raw6081Labels = mixedMoment B node2498 node2498Labels := by
  calc
    mixedMoment B raw6081 raw6081Labels = mixedMoment B raw6081step0 raw6081step0Labels := by
      have hz : ∀ j, raw6081 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6081step0 = (fun i j => raw6081 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6081step0 raw6081; decide +kernel
      have hl : raw6081step0Labels = raw6081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6081 raw6081Labels permutation434 hz
    mixedMoment B raw6081step0 raw6081step0Labels = mixedMoment B raw6081step1 raw6081step1Labels := by
      have ha : raw6081step1 = (fun i j => raw6081step0 (permutation120 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6081step1 raw6081step0; decide +kernel
      have hl : raw6081step1Labels = raw6081step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6081step0 raw6081step0Labels permutation120 permutation5
    mixedMoment B raw6081step1 raw6081step1Labels = mixedMoment B raw6081step2 raw6081step2Labels := by
      have ha : raw6081step2 = raw6081step1 := by apply Matrix.ext; unfold raw6081step2 raw6081step1; decide +kernel
      have hl : raw6081step1Labels = labelEmbedding1 ∘ raw6081step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6081step1 raw6081step1Labels raw6081step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2498 node2498Labels := by rfl

def raw6082 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6082Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6082step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6082step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6082step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6082 raw6082Labels = mixedMoment B node2496 node2496Labels := by
  calc
    mixedMoment B raw6082 raw6082Labels = mixedMoment B raw6082step0 raw6082step0Labels := by
      have ha : raw6082step0 = (fun i j => raw6082 (permutation550 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6082step0 raw6082; decide +kernel
      have hl : raw6082step0Labels = raw6082Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6082 raw6082Labels permutation550 permutation5
    mixedMoment B raw6082step0 raw6082step0Labels = mixedMoment B raw6082step1 raw6082step1Labels := by
      have ha : raw6082step1 = raw6082step0 := by apply Matrix.ext; unfold raw6082step1 raw6082step0; decide +kernel
      have hl : raw6082step0Labels = labelEmbedding1 ∘ raw6082step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6082step0 raw6082step0Labels raw6082step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2496 node2496Labels := by rfl

def raw6083 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6083Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6083step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6083step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6083step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6083step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6083 raw6083Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw6083 raw6083Labels = mixedMoment B raw6083step0 raw6083step0Labels := by
      have hz : ∀ j, raw6083 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6083step0 = (fun i j => raw6083 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6083step0 raw6083; decide +kernel
      have hl : raw6083step0Labels = raw6083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6083 raw6083Labels permutation434 hz
    mixedMoment B raw6083step0 raw6083step0Labels = mixedMoment B raw6083step1 raw6083step1Labels := by
      have ha : raw6083step1 = (fun i j => raw6083step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6083step1 raw6083step0; decide +kernel
      have hl : raw6083step1Labels = raw6083step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6083step0 raw6083step0Labels permutation38 permutation7
    mixedMoment B raw6083step1 raw6083step1Labels = mixedMoment B raw6083step2 raw6083step2Labels := by
      have ha : raw6083step2 = raw6083step1 := by apply Matrix.ext; unfold raw6083step2 raw6083step1; decide +kernel
      have hl : raw6083step1Labels = labelEmbedding1 ∘ raw6083step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6083step1 raw6083step1Labels raw6083step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw6084 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6084Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6084step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6084step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw6084step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6084step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw6084step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6084 raw6084Labels = mixedMoment B node2516 node2516Labels := by
  calc
    mixedMoment B raw6084 raw6084Labels = mixedMoment B raw6084step0 raw6084step0Labels := by
      have hz : ∀ j, raw6084 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6084step0 = (fun i j => raw6084 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6084step0 raw6084; decide +kernel
      have hl : raw6084step0Labels = raw6084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6084 raw6084Labels permutation434 hz
    mixedMoment B raw6084step0 raw6084step0Labels = mixedMoment B raw6084step1 raw6084step1Labels := by
      have ha : raw6084step1 = (fun i j => raw6084step0 (permutation119 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6084step1 raw6084step0; decide +kernel
      have hl : raw6084step1Labels = raw6084step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6084step0 raw6084step0Labels permutation119 permutation5
    mixedMoment B raw6084step1 raw6084step1Labels = mixedMoment B raw6084step2 raw6084step2Labels := by
      have ha : raw6084step2 = raw6084step1 := by apply Matrix.ext; unfold raw6084step2 raw6084step1; decide +kernel
      have hl : raw6084step1Labels = labelEmbedding1 ∘ raw6084step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6084step1 raw6084step1Labels raw6084step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2516 node2516Labels := by rfl

def raw6085 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6085Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6085step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6085step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6085step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6085step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6085 raw6085Labels = mixedMoment B node2497 node2497Labels := by
  calc
    mixedMoment B raw6085 raw6085Labels = mixedMoment B raw6085step0 raw6085step0Labels := by
      have hz : ∀ j, raw6085 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6085step0 = (fun i j => raw6085 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6085step0 raw6085; decide +kernel
      have hl : raw6085step0Labels = raw6085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6085 raw6085Labels permutation346 hz
    mixedMoment B raw6085step0 raw6085step0Labels = mixedMoment B raw6085step1 raw6085step1Labels := by
      have ha : raw6085step1 = (fun i j => raw6085step0 (permutation121 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6085step1 raw6085step0; decide +kernel
      have hl : raw6085step1Labels = raw6085step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6085step0 raw6085step0Labels permutation121 permutation5
    mixedMoment B raw6085step1 raw6085step1Labels = mixedMoment B raw6085step2 raw6085step2Labels := by
      have ha : raw6085step2 = raw6085step1 := by apply Matrix.ext; unfold raw6085step2 raw6085step1; decide +kernel
      have hl : raw6085step1Labels = labelEmbedding1 ∘ raw6085step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6085step1 raw6085step1Labels raw6085step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2497 node2497Labels := by rfl

def raw6086 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6086Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6086step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw6086step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6086step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw6086step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6086 raw6086Labels = mixedMoment B node2498 node2498Labels := by
  calc
    mixedMoment B raw6086 raw6086Labels = mixedMoment B raw6086step0 raw6086step0Labels := by
      have hz : ∀ j, raw6086 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6086step0 = (fun i j => raw6086 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6086step0 raw6086; decide +kernel
      have hl : raw6086step0Labels = raw6086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6086 raw6086Labels permutation346 hz
    mixedMoment B raw6086step0 raw6086step0Labels = mixedMoment B raw6086step1 raw6086step1Labels := by
      have ha : raw6086step1 = (fun i j => raw6086step0 (permutation120 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6086step1 raw6086step0; decide +kernel
      have hl : raw6086step1Labels = raw6086step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6086step0 raw6086step0Labels permutation120 permutation5
    mixedMoment B raw6086step1 raw6086step1Labels = mixedMoment B raw6086step2 raw6086step2Labels := by
      have ha : raw6086step2 = raw6086step1 := by apply Matrix.ext; unfold raw6086step2 raw6086step1; decide +kernel
      have hl : raw6086step1Labels = labelEmbedding1 ∘ raw6086step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6086step1 raw6086step1Labels raw6086step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2498 node2498Labels := by rfl

def raw6087 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6087Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6087step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6087step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6087 raw6087Labels = mixedMoment B node2496 node2496Labels := by
  calc
    mixedMoment B raw6087 raw6087Labels = mixedMoment B raw6087step0 raw6087step0Labels := by
      have ha : raw6087step0 = (fun i j => raw6087 (permutation566 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6087step0 raw6087; decide +kernel
      have hl : raw6087step0Labels = raw6087Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6087 raw6087Labels permutation566 permutation5
    mixedMoment B raw6087step0 raw6087step0Labels = mixedMoment B raw6087step1 raw6087step1Labels := by
      have ha : raw6087step1 = raw6087step0 := by apply Matrix.ext; unfold raw6087step1 raw6087step0; decide +kernel
      have hl : raw6087step0Labels = labelEmbedding1 ∘ raw6087step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6087step0 raw6087step0Labels raw6087step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2496 node2496Labels := by rfl

def raw6088 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6088Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6088step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6088step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6088step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6088 raw6088Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw6088 raw6088Labels = mixedMoment B raw6088step0 raw6088step0Labels := by
      have hz : ∀ j, raw6088 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6088step0 = (fun i j => raw6088 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6088step0 raw6088; decide +kernel
      have hl : raw6088step0Labels = raw6088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6088 raw6088Labels permutation346 hz
    mixedMoment B raw6088step0 raw6088step0Labels = mixedMoment B raw6088step1 raw6088step1Labels := by
      have ha : raw6088step1 = (fun i j => raw6088step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6088step1 raw6088step0; decide +kernel
      have hl : raw6088step1Labels = raw6088step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6088step0 raw6088step0Labels permutation38 permutation7
    mixedMoment B raw6088step1 raw6088step1Labels = mixedMoment B raw6088step2 raw6088step2Labels := by
      have ha : raw6088step2 = raw6088step1 := by apply Matrix.ext; unfold raw6088step2 raw6088step1; decide +kernel
      have hl : raw6088step1Labels = labelEmbedding1 ∘ raw6088step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6088step1 raw6088step1Labels raw6088step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw6089 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6089Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6089step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw6089step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6089step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw6089step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6089 raw6089Labels = mixedMoment B node2516 node2516Labels := by
  calc
    mixedMoment B raw6089 raw6089Labels = mixedMoment B raw6089step0 raw6089step0Labels := by
      have hz : ∀ j, raw6089 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6089step0 = (fun i j => raw6089 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6089step0 raw6089; decide +kernel
      have hl : raw6089step0Labels = raw6089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6089 raw6089Labels permutation346 hz
    mixedMoment B raw6089step0 raw6089step0Labels = mixedMoment B raw6089step1 raw6089step1Labels := by
      have ha : raw6089step1 = (fun i j => raw6089step0 (permutation119 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6089step1 raw6089step0; decide +kernel
      have hl : raw6089step1Labels = raw6089step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6089step0 raw6089step0Labels permutation119 permutation5
    mixedMoment B raw6089step1 raw6089step1Labels = mixedMoment B raw6089step2 raw6089step2Labels := by
      have ha : raw6089step2 = raw6089step1 := by apply Matrix.ext; unfold raw6089step2 raw6089step1; decide +kernel
      have hl : raw6089step1Labels = labelEmbedding1 ∘ raw6089step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6089step1 raw6089step1Labels raw6089step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2516 node2516Labels := by rfl

def raw6090 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6090Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6090step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6090step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6090step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6090step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6090step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6090step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6090step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6090 raw6090Labels = mixedMoment B node1061 node1061Labels := by
  calc
    mixedMoment B raw6090 raw6090Labels = mixedMoment B raw6090step0 raw6090step0Labels := by
      have hz : ∀ j, raw6090 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6090step0 = (fun i j => raw6090 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6090step0 raw6090; decide +kernel
      have hl : raw6090step0Labels = raw6090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6090 raw6090Labels permutation434 hz
    mixedMoment B raw6090step0 raw6090step0Labels = mixedMoment B raw6090step1 raw6090step1Labels := by
      have hz : ∀ j, raw6090step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6090step1 = (fun i j => raw6090step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6090step1 raw6090step0; decide +kernel
      have hl : raw6090step1Labels = raw6090step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6090step0 raw6090step0Labels permutation80 hz
    mixedMoment B raw6090step1 raw6090step1Labels = mixedMoment B raw6090step2 raw6090step2Labels := by
      have ha : raw6090step2 = (fun i j => raw6090step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6090step2 raw6090step1; decide +kernel
      have hl : raw6090step2Labels = raw6090step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6090step1 raw6090step1Labels permutation25 permutation5
    mixedMoment B raw6090step2 raw6090step2Labels = mixedMoment B raw6090step3 raw6090step3Labels := by
      have ha : raw6090step3 = raw6090step2 := by apply Matrix.ext; unfold raw6090step3 raw6090step2; decide +kernel
      have hl : raw6090step2Labels = labelEmbedding1 ∘ raw6090step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6090step2 raw6090step2Labels raw6090step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1061 node1061Labels := by rfl

def raw6091 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6091Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6091step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6091step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6091step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6091step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw6091step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6091step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw6091step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6091 raw6091Labels = mixedMoment B node1062 node1062Labels := by
  calc
    mixedMoment B raw6091 raw6091Labels = mixedMoment B raw6091step0 raw6091step0Labels := by
      have hz : ∀ j, raw6091 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6091step0 = (fun i j => raw6091 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6091step0 raw6091; decide +kernel
      have hl : raw6091step0Labels = raw6091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6091 raw6091Labels permutation434 hz
    mixedMoment B raw6091step0 raw6091step0Labels = mixedMoment B raw6091step1 raw6091step1Labels := by
      have hz : ∀ j, raw6091step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6091step1 = (fun i j => raw6091step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6091step1 raw6091step0; decide +kernel
      have hl : raw6091step1Labels = raw6091step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6091step0 raw6091step0Labels permutation80 hz
    mixedMoment B raw6091step1 raw6091step1Labels = mixedMoment B raw6091step2 raw6091step2Labels := by
      have ha : raw6091step2 = (fun i j => raw6091step1 (permutation24 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6091step2 raw6091step1; decide +kernel
      have hl : raw6091step2Labels = raw6091step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6091step1 raw6091step1Labels permutation24 permutation5
    mixedMoment B raw6091step2 raw6091step2Labels = mixedMoment B raw6091step3 raw6091step3Labels := by
      have ha : raw6091step3 = raw6091step2 := by apply Matrix.ext; unfold raw6091step3 raw6091step2; decide +kernel
      have hl : raw6091step2Labels = labelEmbedding1 ∘ raw6091step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6091step2 raw6091step2Labels raw6091step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1062 node1062Labels := by rfl

def raw6092 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6092Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6092step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6092step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6092step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6092step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6092 raw6092Labels = mixedMoment B node1060 node1060Labels := by
  calc
    mixedMoment B raw6092 raw6092Labels = mixedMoment B raw6092step0 raw6092step0Labels := by
      have hz : ∀ j, raw6092 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6092step0 = (fun i j => raw6092 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6092step0 raw6092; decide +kernel
      have hl : raw6092step0Labels = raw6092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6092 raw6092Labels permutation434 hz
    mixedMoment B raw6092step0 raw6092step0Labels = mixedMoment B raw6092step1 raw6092step1Labels := by
      have ha : raw6092step1 = (fun i j => raw6092step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6092step1 raw6092step0; decide +kernel
      have hl : raw6092step1Labels = raw6092step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6092step0 raw6092step0Labels permutation125 permutation5
    mixedMoment B raw6092step1 raw6092step1Labels = mixedMoment B raw6092step2 raw6092step2Labels := by
      have ha : raw6092step2 = raw6092step1 := by apply Matrix.ext; unfold raw6092step2 raw6092step1; decide +kernel
      have hl : raw6092step1Labels = labelEmbedding1 ∘ raw6092step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6092step1 raw6092step1Labels raw6092step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1060 node1060Labels := by rfl

def raw6093 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6093Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6093step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6093step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6093step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6093step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6093 raw6093Labels = mixedMoment B node1060 node1060Labels := by
  calc
    mixedMoment B raw6093 raw6093Labels = mixedMoment B raw6093step0 raw6093step0Labels := by
      have hz : ∀ j, raw6093 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6093step0 = (fun i j => raw6093 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6093step0 raw6093; decide +kernel
      have hl : raw6093step0Labels = raw6093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6093 raw6093Labels permutation346 hz
    mixedMoment B raw6093step0 raw6093step0Labels = mixedMoment B raw6093step1 raw6093step1Labels := by
      have ha : raw6093step1 = (fun i j => raw6093step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6093step1 raw6093step0; decide +kernel
      have hl : raw6093step1Labels = raw6093step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6093step0 raw6093step0Labels permutation125 permutation5
    mixedMoment B raw6093step1 raw6093step1Labels = mixedMoment B raw6093step2 raw6093step2Labels := by
      have ha : raw6093step2 = raw6093step1 := by apply Matrix.ext; unfold raw6093step2 raw6093step1; decide +kernel
      have hl : raw6093step1Labels = labelEmbedding1 ∘ raw6093step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6093step1 raw6093step1Labels raw6093step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1060 node1060Labels := by rfl

def raw6094 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![-3, 1, 2]]
def raw6094Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -4, 1], ![-3, 1, 2]]
def raw6094step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6094step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -4, 1], ![-3, 1, 2]]
def raw6094step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6094step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw6094step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6094step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw6094step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6094 raw6094Labels = mixedMoment B node1088 node1088Labels := by
  calc
    mixedMoment B raw6094 raw6094Labels = mixedMoment B raw6094step0 raw6094step0Labels := by
      have hz : ∀ j, raw6094 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6094step0 = (fun i j => raw6094 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6094step0 raw6094; decide +kernel
      have hl : raw6094step0Labels = raw6094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6094 raw6094Labels permutation434 hz
    mixedMoment B raw6094step0 raw6094step0Labels = mixedMoment B raw6094step1 raw6094step1Labels := by
      have hz : ∀ j, raw6094step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6094step1 = (fun i j => raw6094step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6094step1 raw6094step0; decide +kernel
      have hl : raw6094step1Labels = raw6094step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6094step0 raw6094step0Labels permutation80 hz
    mixedMoment B raw6094step1 raw6094step1Labels = mixedMoment B raw6094step2 raw6094step2Labels := by
      have ha : raw6094step2 = (fun i j => raw6094step1 (permutation23 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6094step2 raw6094step1; decide +kernel
      have hl : raw6094step2Labels = raw6094step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6094step1 raw6094step1Labels permutation23 permutation5
    mixedMoment B raw6094step2 raw6094step2Labels = mixedMoment B raw6094step3 raw6094step3Labels := by
      have ha : raw6094step3 = raw6094step2 := by apply Matrix.ext; unfold raw6094step3 raw6094step2; decide +kernel
      have hl : raw6094step2Labels = labelEmbedding1 ∘ raw6094step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6094step2 raw6094step2Labels raw6094step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1088 node1088Labels := by rfl

def raw6095 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6095Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6095step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6095step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6095step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw6095step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6095step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw6095step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6095 raw6095Labels = mixedMoment B node2642 node2642Labels := by
  calc
    mixedMoment B raw6095 raw6095Labels = mixedMoment B raw6095step0 raw6095step0Labels := by
      have hz : ∀ j, raw6095 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6095step0 = (fun i j => raw6095 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6095step0 raw6095; decide +kernel
      have hl : raw6095step0Labels = raw6095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6095 raw6095Labels permutation434 hz
    mixedMoment B raw6095step0 raw6095step0Labels = mixedMoment B raw6095step1 raw6095step1Labels := by
      have hz : ∀ j, raw6095step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6095step1 = (fun i j => raw6095step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6095step1 raw6095step0; decide +kernel
      have hl : raw6095step1Labels = raw6095step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6095step0 raw6095step0Labels permutation80 hz
    mixedMoment B raw6095step1 raw6095step1Labels = mixedMoment B raw6095step2 raw6095step2Labels := by
      have ha : raw6095step2 = (fun i j => raw6095step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6095step2 raw6095step1; decide +kernel
      have hl : raw6095step2Labels = raw6095step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6095step1 raw6095step1Labels permutation25 permutation5
    mixedMoment B raw6095step2 raw6095step2Labels = mixedMoment B raw6095step3 raw6095step3Labels := by
      have ha : raw6095step3 = raw6095step2 := by apply Matrix.ext; unfold raw6095step3 raw6095step2; decide +kernel
      have hl : raw6095step2Labels = labelEmbedding1 ∘ raw6095step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6095step2 raw6095step2Labels raw6095step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2642 node2642Labels := by rfl

def raw6096 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6096Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6096step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6096step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6096step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6096step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw6096step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6096step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw6096step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6096 raw6096Labels = mixedMoment B node2643 node2643Labels := by
  calc
    mixedMoment B raw6096 raw6096Labels = mixedMoment B raw6096step0 raw6096step0Labels := by
      have hz : ∀ j, raw6096 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6096step0 = (fun i j => raw6096 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6096step0 raw6096; decide +kernel
      have hl : raw6096step0Labels = raw6096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6096 raw6096Labels permutation434 hz
    mixedMoment B raw6096step0 raw6096step0Labels = mixedMoment B raw6096step1 raw6096step1Labels := by
      have hz : ∀ j, raw6096step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6096step1 = (fun i j => raw6096step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6096step1 raw6096step0; decide +kernel
      have hl : raw6096step1Labels = raw6096step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6096step0 raw6096step0Labels permutation80 hz
    mixedMoment B raw6096step1 raw6096step1Labels = mixedMoment B raw6096step2 raw6096step2Labels := by
      have ha : raw6096step2 = (fun i j => raw6096step1 (permutation24 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6096step2 raw6096step1; decide +kernel
      have hl : raw6096step2Labels = raw6096step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6096step1 raw6096step1Labels permutation24 permutation5
    mixedMoment B raw6096step2 raw6096step2Labels = mixedMoment B raw6096step3 raw6096step3Labels := by
      have ha : raw6096step3 = raw6096step2 := by apply Matrix.ext; unfold raw6096step3 raw6096step2; decide +kernel
      have hl : raw6096step2Labels = labelEmbedding1 ∘ raw6096step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6096step2 raw6096step2Labels raw6096step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2643 node2643Labels := by rfl

def raw6097 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6097Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6097step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6097step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6097step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6097step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6097step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6097 raw6097Labels = mixedMoment B node2641 node2641Labels := by
  calc
    mixedMoment B raw6097 raw6097Labels = mixedMoment B raw6097step0 raw6097step0Labels := by
      have hz : ∀ j, raw6097 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6097step0 = (fun i j => raw6097 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6097step0 raw6097; decide +kernel
      have hl : raw6097step0Labels = raw6097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6097 raw6097Labels permutation434 hz
    mixedMoment B raw6097step0 raw6097step0Labels = mixedMoment B raw6097step1 raw6097step1Labels := by
      have ha : raw6097step1 = (fun i j => raw6097step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6097step1 raw6097step0; decide +kernel
      have hl : raw6097step1Labels = raw6097step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6097step0 raw6097step0Labels permutation125 permutation5
    mixedMoment B raw6097step1 raw6097step1Labels = mixedMoment B raw6097step2 raw6097step2Labels := by
      have ha : raw6097step2 = raw6097step1 := by apply Matrix.ext; unfold raw6097step2 raw6097step1; decide +kernel
      have hl : raw6097step1Labels = labelEmbedding1 ∘ raw6097step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6097step1 raw6097step1Labels raw6097step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2641 node2641Labels := by rfl

def raw6098 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6098Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6098step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6098step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6098step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6098step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6098 raw6098Labels = mixedMoment B node2641 node2641Labels := by
  calc
    mixedMoment B raw6098 raw6098Labels = mixedMoment B raw6098step0 raw6098step0Labels := by
      have hz : ∀ j, raw6098 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6098step0 = (fun i j => raw6098 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6098step0 raw6098; decide +kernel
      have hl : raw6098step0Labels = raw6098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6098 raw6098Labels permutation346 hz
    mixedMoment B raw6098step0 raw6098step0Labels = mixedMoment B raw6098step1 raw6098step1Labels := by
      have ha : raw6098step1 = (fun i j => raw6098step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6098step1 raw6098step0; decide +kernel
      have hl : raw6098step1Labels = raw6098step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6098step0 raw6098step0Labels permutation125 permutation5
    mixedMoment B raw6098step1 raw6098step1Labels = mixedMoment B raw6098step2 raw6098step2Labels := by
      have ha : raw6098step2 = raw6098step1 := by apply Matrix.ext; unfold raw6098step2 raw6098step1; decide +kernel
      have hl : raw6098step1Labels = labelEmbedding1 ∘ raw6098step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6098step1 raw6098step1Labels raw6098step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2641 node2641Labels := by rfl

def raw6099 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6099Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6099step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6099step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6099step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6099step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw6099step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6099step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw6099step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6099 raw6099Labels = mixedMoment B node3110 node3110Labels := by
  calc
    mixedMoment B raw6099 raw6099Labels = mixedMoment B raw6099step0 raw6099step0Labels := by
      have hz : ∀ j, raw6099 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6099step0 = (fun i j => raw6099 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6099step0 raw6099; decide +kernel
      have hl : raw6099step0Labels = raw6099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6099 raw6099Labels permutation434 hz
    mixedMoment B raw6099step0 raw6099step0Labels = mixedMoment B raw6099step1 raw6099step1Labels := by
      have hz : ∀ j, raw6099step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6099step1 = (fun i j => raw6099step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6099step1 raw6099step0; decide +kernel
      have hl : raw6099step1Labels = raw6099step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6099step0 raw6099step0Labels permutation80 hz
    mixedMoment B raw6099step1 raw6099step1Labels = mixedMoment B raw6099step2 raw6099step2Labels := by
      have ha : raw6099step2 = (fun i j => raw6099step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6099step2 raw6099step1; decide +kernel
      have hl : raw6099step2Labels = raw6099step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6099step1 raw6099step1Labels permutation8 permutation7
    mixedMoment B raw6099step2 raw6099step2Labels = mixedMoment B raw6099step3 raw6099step3Labels := by
      have ha : raw6099step3 = raw6099step2 := by apply Matrix.ext; unfold raw6099step3 raw6099step2; decide +kernel
      have hl : raw6099step2Labels = labelEmbedding1 ∘ raw6099step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6099step2 raw6099step2Labels raw6099step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3110 node3110Labels := by rfl

def raw6100 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6100Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6100step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6100step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6100step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6100step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw6100step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6100 raw6100Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw6100 raw6100Labels = mixedMoment B raw6100step0 raw6100step0Labels := by
      have hz : ∀ j, raw6100 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6100step0 = (fun i j => raw6100 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6100step0 raw6100; decide +kernel
      have hl : raw6100step0Labels = raw6100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6100 raw6100Labels permutation434 hz
    mixedMoment B raw6100step0 raw6100step0Labels = mixedMoment B raw6100step1 raw6100step1Labels := by
      have hz : ∀ j, raw6100step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6100step1 = (fun i j => raw6100step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6100step1 raw6100step0; decide +kernel
      have hl : raw6100step1Labels = raw6100step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6100step0 raw6100step0Labels permutation80 hz
    mixedMoment B raw6100step1 raw6100step1Labels = mixedMoment B raw6100step2 raw6100step2Labels := by
      have ha : raw6100step2 = (fun i j => raw6100step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6100step2 raw6100step1; decide +kernel
      have hl : raw6100step2Labels = raw6100step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6100step1 raw6100step1Labels permutation25 permutation4
    _ = mixedMoment B node3052 node3052Labels := by rfl

def raw6101 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6101Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6101step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6101step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 2, -3], ![2, -2, 0]]
def raw6101step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6101 raw6101Labels = mixedMoment B node3056 node3056Labels := by
  calc
    mixedMoment B raw6101 raw6101Labels = mixedMoment B raw6101step0 raw6101step0Labels := by
      have hz : ∀ j, raw6101 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6101step0 = (fun i j => raw6101 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6101step0 raw6101; decide +kernel
      have hl : raw6101step0Labels = raw6101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6101 raw6101Labels permutation434 hz
    mixedMoment B raw6101step0 raw6101step0Labels = mixedMoment B raw6101step1 raw6101step1Labels := by
      have hz : ∀ j, raw6101step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6101step1 = (fun i j => raw6101step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6101step1 raw6101step0; decide +kernel
      have hl : raw6101step1Labels = raw6101step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6101step0 raw6101step0Labels permutation80 hz
    mixedMoment B raw6101step1 raw6101step1Labels = mixedMoment B raw6101step2 raw6101step2Labels := by
      have ha : raw6101step2 = (fun i j => raw6101step1 (permutation24 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6101step2 raw6101step1; decide +kernel
      have hl : raw6101step2Labels = raw6101step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6101step1 raw6101step1Labels permutation24 permutation4
    _ = mixedMoment B node3056 node3056Labels := by rfl

def raw6102 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6102Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6102step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw6102step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6102 raw6102Labels = mixedMoment B node3050 node3050Labels := by
  calc
    mixedMoment B raw6102 raw6102Labels = mixedMoment B raw6102step0 raw6102step0Labels := by
      have hz : ∀ j, raw6102 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6102step0 = (fun i j => raw6102 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6102step0 raw6102; decide +kernel
      have hl : raw6102step0Labels = raw6102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6102 raw6102Labels permutation434 hz
    mixedMoment B raw6102step0 raw6102step0Labels = mixedMoment B raw6102step1 raw6102step1Labels := by
      have ha : raw6102step1 = (fun i j => raw6102step0 (permutation125 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6102step1 raw6102step0; decide +kernel
      have hl : raw6102step1Labels = raw6102step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6102step0 raw6102step0Labels permutation125 permutation4
    _ = mixedMoment B node3050 node3050Labels := by rfl

def raw6103 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6103Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6103step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw6103step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6103 raw6103Labels = mixedMoment B node3050 node3050Labels := by
  calc
    mixedMoment B raw6103 raw6103Labels = mixedMoment B raw6103step0 raw6103step0Labels := by
      have hz : ∀ j, raw6103 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6103step0 = (fun i j => raw6103 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6103step0 raw6103; decide +kernel
      have hl : raw6103step0Labels = raw6103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6103 raw6103Labels permutation346 hz
    mixedMoment B raw6103step0 raw6103step0Labels = mixedMoment B raw6103step1 raw6103step1Labels := by
      have ha : raw6103step1 = (fun i j => raw6103step0 (permutation125 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6103step1 raw6103step0; decide +kernel
      have hl : raw6103step1Labels = raw6103step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6103step0 raw6103step0Labels permutation125 permutation4
    _ = mixedMoment B node3050 node3050Labels := by rfl

def raw6104 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6104Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6104step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6104step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6104step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw6104step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6104step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6104step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6104 raw6104Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw6104 raw6104Labels = mixedMoment B raw6104step0 raw6104step0Labels := by
      have hz : ∀ j, raw6104 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6104step0 = (fun i j => raw6104 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6104step0 raw6104; decide +kernel
      have hl : raw6104step0Labels = raw6104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6104 raw6104Labels permutation434 hz
    mixedMoment B raw6104step0 raw6104step0Labels = mixedMoment B raw6104step1 raw6104step1Labels := by
      have hz : ∀ j, raw6104step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6104step1 = (fun i j => raw6104step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6104step1 raw6104step0; decide +kernel
      have hl : raw6104step1Labels = raw6104step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6104step0 raw6104step0Labels permutation80 hz
    mixedMoment B raw6104step1 raw6104step1Labels = mixedMoment B raw6104step2 raw6104step2Labels := by
      have ha : raw6104step2 = (fun i j => raw6104step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6104step2 raw6104step1; decide +kernel
      have hl : raw6104step2Labels = raw6104step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6104step1 raw6104step1Labels permutation10 permutation2
    mixedMoment B raw6104step2 raw6104step2Labels = mixedMoment B raw6104step3 raw6104step3Labels := by
      have ha : raw6104step3 = -raw6104step2 := by apply Matrix.ext; change ∀ i j, raw6104step3 i j = -(raw6104step2 i j); unfold raw6104step3 raw6104step2; decide +kernel
      have hl : raw6104step3Labels = raw6104step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3582 node3582Labels := by rfl

def raw6105 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6105Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6105step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6105step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw6105step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6105 raw6105Labels = mixedMoment B node2603 node2603Labels := by
  calc
    mixedMoment B raw6105 raw6105Labels = mixedMoment B raw6105step0 raw6105step0Labels := by
      have hz : ∀ j, raw6105 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6105step0 = (fun i j => raw6105 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6105step0 raw6105; decide +kernel
      have hl : raw6105step0Labels = raw6105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6105 raw6105Labels permutation434 hz
    mixedMoment B raw6105step0 raw6105step0Labels = mixedMoment B raw6105step1 raw6105step1Labels := by
      have hz : ∀ j, raw6105step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6105step1 = (fun i j => raw6105step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6105step1 raw6105step0; decide +kernel
      have hl : raw6105step1Labels = raw6105step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6105step0 raw6105step0Labels permutation80 hz
    mixedMoment B raw6105step1 raw6105step1Labels = mixedMoment B raw6105step2 raw6105step2Labels := by
      have ha : raw6105step2 = (fun i j => raw6105step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6105step2 raw6105step1; decide +kernel
      have hl : raw6105step2Labels = raw6105step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6105step1 raw6105step1Labels permutation29 permutation2
    _ = mixedMoment B node2603 node2603Labels := by rfl

def raw6106 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6106Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6106step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -2, 0], ![2, 1, -3]]
def raw6106step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6106 raw6106Labels = mixedMoment B node2978 node2978Labels := by
  calc
    mixedMoment B raw6106 raw6106Labels = mixedMoment B raw6106step0 raw6106step0Labels := by
      have hz : ∀ j, raw6106 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6106step0 = (fun i j => raw6106 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6106step0 raw6106; decide +kernel
      have hl : raw6106step0Labels = raw6106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6106 raw6106Labels permutation434 hz
    mixedMoment B raw6106step0 raw6106step0Labels = mixedMoment B raw6106step1 raw6106step1Labels := by
      have ha : raw6106step1 = (fun i j => raw6106step0 (permutation121 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6106step1 raw6106step0; decide +kernel
      have hl : raw6106step1Labels = raw6106step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6106step0 raw6106step0Labels permutation121 permutation4
    _ = mixedMoment B node2978 node2978Labels := by rfl

def raw6107 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6107Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6107step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -2, 0], ![2, 1, -3]]
def raw6107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6107 raw6107Labels = mixedMoment B node2978 node2978Labels := by
  calc
    mixedMoment B raw6107 raw6107Labels = mixedMoment B raw6107step0 raw6107step0Labels := by
      have hz : ∀ j, raw6107 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6107step0 = (fun i j => raw6107 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6107step0 raw6107; decide +kernel
      have hl : raw6107step0Labels = raw6107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6107 raw6107Labels permutation346 hz
    mixedMoment B raw6107step0 raw6107step0Labels = mixedMoment B raw6107step1 raw6107step1Labels := by
      have ha : raw6107step1 = (fun i j => raw6107step0 (permutation121 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6107step1 raw6107step0; decide +kernel
      have hl : raw6107step1Labels = raw6107step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6107step0 raw6107step0Labels permutation121 permutation4
    _ = mixedMoment B node2978 node2978Labels := by rfl

def raw6108 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6108Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6108step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6108step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6108step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6108step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -2, 0], ![2, 1, -3]]
def raw6108step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6108 raw6108Labels = mixedMoment B node1374 node1374Labels := by
  calc
    mixedMoment B raw6108 raw6108Labels = mixedMoment B raw6108step0 raw6108step0Labels := by
      have hz : ∀ j, raw6108 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6108step0 = (fun i j => raw6108 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6108step0 raw6108; decide +kernel
      have hl : raw6108step0Labels = raw6108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6108 raw6108Labels permutation434 hz
    mixedMoment B raw6108step0 raw6108step0Labels = mixedMoment B raw6108step1 raw6108step1Labels := by
      have hz : ∀ j, raw6108step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6108step1 = (fun i j => raw6108step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6108step1 raw6108step0; decide +kernel
      have hl : raw6108step1Labels = raw6108step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6108step0 raw6108step0Labels permutation80 hz
    mixedMoment B raw6108step1 raw6108step1Labels = mixedMoment B raw6108step2 raw6108step2Labels := by
      have ha : raw6108step2 = (fun i j => raw6108step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6108step2 raw6108step1; decide +kernel
      have hl : raw6108step2Labels = raw6108step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6108step1 raw6108step1Labels permutation25 permutation4
    _ = mixedMoment B node1374 node1374Labels := by rfl

def raw6109 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6109Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6109step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6109step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw6109step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6109 raw6109Labels = mixedMoment B node2888 node2888Labels := by
  calc
    mixedMoment B raw6109 raw6109Labels = mixedMoment B raw6109step0 raw6109step0Labels := by
      have hz : ∀ j, raw6109 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6109step0 = (fun i j => raw6109 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6109step0 raw6109; decide +kernel
      have hl : raw6109step0Labels = raw6109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6109 raw6109Labels permutation434 hz
    mixedMoment B raw6109step0 raw6109step0Labels = mixedMoment B raw6109step1 raw6109step1Labels := by
      have hz : ∀ j, raw6109step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6109step1 = (fun i j => raw6109step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6109step1 raw6109step0; decide +kernel
      have hl : raw6109step1Labels = raw6109step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6109step0 raw6109step0Labels permutation80 hz
    mixedMoment B raw6109step1 raw6109step1Labels = mixedMoment B raw6109step2 raw6109step2Labels := by
      have ha : raw6109step2 = (fun i j => raw6109step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6109step2 raw6109step1; decide +kernel
      have hl : raw6109step2Labels = raw6109step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6109step1 raw6109step1Labels permutation25 permutation4
    _ = mixedMoment B node2888 node2888Labels := by rfl

def raw6110 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6110Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6110step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw6110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6110step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6110step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6110 raw6110Labels = mixedMoment B node2035 node2035Labels := by
  calc
    mixedMoment B raw6110 raw6110Labels = mixedMoment B raw6110step0 raw6110step0Labels := by
      have hz : ∀ j, raw6110 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6110step0 = (fun i j => raw6110 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6110step0 raw6110; decide +kernel
      have hl : raw6110step0Labels = raw6110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6110 raw6110Labels permutation434 hz
    mixedMoment B raw6110step0 raw6110step0Labels = mixedMoment B raw6110step1 raw6110step1Labels := by
      have ha : raw6110step1 = (fun i j => raw6110step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6110step1 raw6110step0; decide +kernel
      have hl : raw6110step1Labels = raw6110step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6110step0 raw6110step0Labels permutation36 permutation4
    mixedMoment B raw6110step1 raw6110step1Labels = mixedMoment B raw6110step2 raw6110step2Labels := by
      have ha : raw6110step2 = -raw6110step1 := by apply Matrix.ext; change ∀ i j, raw6110step2 i j = -(raw6110step1 i j); unfold raw6110step2 raw6110step1; decide +kernel
      have hl : raw6110step2Labels = raw6110step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2035 node2035Labels := by rfl

def raw6111 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6111Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6111step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw6111step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6111 raw6111Labels = mixedMoment B node2973 node2973Labels := by
  calc
    mixedMoment B raw6111 raw6111Labels = mixedMoment B raw6111step0 raw6111step0Labels := by
      have ha : raw6111step0 = (fun i j => raw6111 (permutation550 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6111step0 raw6111; decide +kernel
      have hl : raw6111step0Labels = raw6111Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6111 raw6111Labels permutation550 permutation4
    _ = mixedMoment B node2973 node2973Labels := by rfl

def raw6112 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6112Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6112step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw6112step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6112 raw6112Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw6112 raw6112Labels = mixedMoment B raw6112step0 raw6112step0Labels := by
      have hz : ∀ j, raw6112 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6112step0 = (fun i j => raw6112 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6112step0 raw6112; decide +kernel
      have hl : raw6112step0Labels = raw6112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6112 raw6112Labels permutation434 hz
    mixedMoment B raw6112step0 raw6112step0Labels = mixedMoment B raw6112step1 raw6112step1Labels := by
      have ha : raw6112step1 = (fun i j => raw6112step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6112step1 raw6112step0; decide +kernel
      have hl : raw6112step1Labels = raw6112step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6112step0 raw6112step0Labels permutation36 permutation4
    mixedMoment B raw6112step1 raw6112step1Labels = mixedMoment B raw6112step2 raw6112step2Labels := by
      have ha : raw6112step2 = -raw6112step1 := by apply Matrix.ext; change ∀ i j, raw6112step2 i j = -(raw6112step1 i j); unfold raw6112step2 raw6112step1; decide +kernel
      have hl : raw6112step2Labels = raw6112step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw6113 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6113Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6113step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -3, 1]]
def raw6113step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6113 raw6113Labels = mixedMoment B node2597 node2597Labels := by
  calc
    mixedMoment B raw6113 raw6113Labels = mixedMoment B raw6113step0 raw6113step0Labels := by
      have hz : ∀ j, raw6113 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6113step0 = (fun i j => raw6113 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6113step0 raw6113; decide +kernel
      have hl : raw6113step0Labels = raw6113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6113 raw6113Labels permutation434 hz
    mixedMoment B raw6113step0 raw6113step0Labels = mixedMoment B raw6113step1 raw6113step1Labels := by
      have ha : raw6113step1 = (fun i j => raw6113step0 (permutation136 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6113step1 raw6113step0; decide +kernel
      have hl : raw6113step1Labels = raw6113step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6113step0 raw6113step0Labels permutation136 permutation2
    _ = mixedMoment B node2597 node2597Labels := by rfl

def raw6114 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6114Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6114step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6114step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6114step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw6114step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6114 raw6114Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw6114 raw6114Labels = mixedMoment B raw6114step0 raw6114step0Labels := by
      have hz : ∀ j, raw6114 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6114step0 = (fun i j => raw6114 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6114step0 raw6114; decide +kernel
      have hl : raw6114step0Labels = raw6114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6114 raw6114Labels permutation434 hz
    mixedMoment B raw6114step0 raw6114step0Labels = mixedMoment B raw6114step1 raw6114step1Labels := by
      have hz : ∀ j, raw6114step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6114step1 = (fun i j => raw6114step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6114step1 raw6114step0; decide +kernel
      have hl : raw6114step1Labels = raw6114step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6114step0 raw6114step0Labels permutation56 hz
    mixedMoment B raw6114step1 raw6114step1Labels = mixedMoment B raw6114step2 raw6114step2Labels := by
      have ha : raw6114step2 = (fun i j => raw6114step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6114step2 raw6114step1; decide +kernel
      have hl : raw6114step2Labels = raw6114step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6114step1 raw6114step1Labels permutation25 permutation4
    _ = mixedMoment B node3052 node3052Labels := by rfl

def raw6115 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6115Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw6115step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6115 raw6115Labels = mixedMoment B node2973 node2973Labels := by
  calc
    mixedMoment B raw6115 raw6115Labels = mixedMoment B raw6115step0 raw6115step0Labels := by
      have ha : raw6115step0 = (fun i j => raw6115 (permutation566 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6115step0 raw6115; decide +kernel
      have hl : raw6115step0Labels = raw6115Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6115 raw6115Labels permutation566 permutation4
    _ = mixedMoment B node2973 node2973Labels := by rfl

def raw6116 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6116Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6116step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw6116step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6116 raw6116Labels = mixedMoment B node1365 node1365Labels := by
  calc
    mixedMoment B raw6116 raw6116Labels = mixedMoment B raw6116step0 raw6116step0Labels := by
      have hz : ∀ j, raw6116 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6116step0 = (fun i j => raw6116 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6116step0 raw6116; decide +kernel
      have hl : raw6116step0Labels = raw6116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6116 raw6116Labels permutation434 hz
    mixedMoment B raw6116step0 raw6116step0Labels = mixedMoment B raw6116step1 raw6116step1Labels := by
      have ha : raw6116step1 = (fun i j => raw6116step0 (permutation125 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6116step1 raw6116step0; decide +kernel
      have hl : raw6116step1Labels = raw6116step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6116step0 raw6116step0Labels permutation125 permutation4
    _ = mixedMoment B node1365 node1365Labels := by rfl

def raw6117 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6117Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6117step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw6117step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6117 raw6117Labels = mixedMoment B node2879 node2879Labels := by
  calc
    mixedMoment B raw6117 raw6117Labels = mixedMoment B raw6117step0 raw6117step0Labels := by
      have hz : ∀ j, raw6117 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6117step0 = (fun i j => raw6117 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6117step0 raw6117; decide +kernel
      have hl : raw6117step0Labels = raw6117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6117 raw6117Labels permutation434 hz
    mixedMoment B raw6117step0 raw6117step0Labels = mixedMoment B raw6117step1 raw6117step1Labels := by
      have ha : raw6117step1 = (fun i j => raw6117step0 (permutation125 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6117step1 raw6117step0; decide +kernel
      have hl : raw6117step1Labels = raw6117step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6117step0 raw6117step0Labels permutation125 permutation4
    _ = mixedMoment B node2879 node2879Labels := by rfl

def raw6118 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6118Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6118step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6118step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6118step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw6118step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6118 raw6118Labels = mixedMoment B node1369 node1369Labels := by
  calc
    mixedMoment B raw6118 raw6118Labels = mixedMoment B raw6118step0 raw6118step0Labels := by
      have hz : ∀ j, raw6118 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6118step0 = (fun i j => raw6118 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6118step0 raw6118; decide +kernel
      have hl : raw6118step0Labels = raw6118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6118 raw6118Labels permutation434 hz
    mixedMoment B raw6118step0 raw6118step0Labels = mixedMoment B raw6118step1 raw6118step1Labels := by
      have hz : ∀ j, raw6118step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6118step1 = (fun i j => raw6118step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6118step1 raw6118step0; decide +kernel
      have hl : raw6118step1Labels = raw6118step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6118step0 raw6118step0Labels permutation80 hz
    mixedMoment B raw6118step1 raw6118step1Labels = mixedMoment B raw6118step2 raw6118step2Labels := by
      have ha : raw6118step2 = (fun i j => raw6118step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6118step2 raw6118step1; decide +kernel
      have hl : raw6118step2Labels = raw6118step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6118step1 raw6118step1Labels permutation25 permutation4
    _ = mixedMoment B node1369 node1369Labels := by rfl

def raw6119 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6119Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -4, 1], ![-2, 0, 2]]
def raw6119step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw6119step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6119 raw6119Labels = mixedMoment B node1365 node1365Labels := by
  calc
    mixedMoment B raw6119 raw6119Labels = mixedMoment B raw6119step0 raw6119step0Labels := by
      have hz : ∀ j, raw6119 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6119step0 = (fun i j => raw6119 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6119step0 raw6119; decide +kernel
      have hl : raw6119step0Labels = raw6119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6119 raw6119Labels permutation346 hz
    mixedMoment B raw6119step0 raw6119step0Labels = mixedMoment B raw6119step1 raw6119step1Labels := by
      have ha : raw6119step1 = (fun i j => raw6119step0 (permutation125 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6119step1 raw6119step0; decide +kernel
      have hl : raw6119step1Labels = raw6119step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6119step0 raw6119step0Labels permutation125 permutation4
    _ = mixedMoment B node1365 node1365Labels := by rfl

def raw6120 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -4, 1], ![-3, 1, 2]]
def raw6120Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -4, 1], ![-3, 1, 2]]
def raw6120step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -4, 1], ![-3, 1, 2]]
def raw6120step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6120step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, -1, 0], ![2, 1, -3]]
def raw6120step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6120 raw6120Labels = mixedMoment B node1434 node1434Labels := by
  calc
    mixedMoment B raw6120 raw6120Labels = mixedMoment B raw6120step0 raw6120step0Labels := by
      have hz : ∀ j, raw6120 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6120step0 = (fun i j => raw6120 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6120step0 raw6120; decide +kernel
      have hl : raw6120step0Labels = raw6120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6120 raw6120Labels permutation434 hz
    mixedMoment B raw6120step0 raw6120step0Labels = mixedMoment B raw6120step1 raw6120step1Labels := by
      have hz : ∀ j, raw6120step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6120step1 = (fun i j => raw6120step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6120step1 raw6120step0; decide +kernel
      have hl : raw6120step1Labels = raw6120step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6120step0 raw6120step0Labels permutation80 hz
    mixedMoment B raw6120step1 raw6120step1Labels = mixedMoment B raw6120step2 raw6120step2Labels := by
      have ha : raw6120step2 = (fun i j => raw6120step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6120step2 raw6120step1; decide +kernel
      have hl : raw6120step2Labels = raw6120step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6120step1 raw6120step1Labels permutation25 permutation4
    _ = mixedMoment B node1434 node1434Labels := by rfl

def raw6121 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6121Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6121step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6121step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6121step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6121step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![-2, 0, 2]]
def raw6121step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6121step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-2, 1, 1]]
def raw6121step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6121step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw6121step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6121 raw6121Labels = mixedMoment B node3633 node3633Labels := by
  calc
    mixedMoment B raw6121 raw6121Labels = mixedMoment B raw6121step0 raw6121step0Labels := by
      have hz : ∀ j, raw6121 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6121step0 = (fun i j => raw6121 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6121step0 raw6121; decide +kernel
      have hl : raw6121step0Labels = raw6121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6121 raw6121Labels permutation434 hz
    mixedMoment B raw6121step0 raw6121step0Labels = mixedMoment B raw6121step1 raw6121step1Labels := by
      have hz : ∀ j, raw6121step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6121step1 = (fun i j => raw6121step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6121step1 raw6121step0; decide +kernel
      have hl : raw6121step1Labels = raw6121step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6121step0 raw6121step0Labels permutation80 hz
    mixedMoment B raw6121step1 raw6121step1Labels = mixedMoment B raw6121step2 raw6121step2Labels := by
      have hz : ∀ j, raw6121step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw6121step2 = (fun i j => raw6121step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw6121step2 raw6121step1; decide +kernel
      have hl : raw6121step2Labels = raw6121step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6121step1 raw6121step1Labels permutation14 hz
    mixedMoment B raw6121step2 raw6121step2Labels = mixedMoment B raw6121step3 raw6121step3Labels := by
      have ha : raw6121step3 = (fun i j => raw6121step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6121step3 raw6121step2; decide +kernel
      have hl : raw6121step3Labels = raw6121step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6121step2 raw6121step2Labels permutation3 permutation4
    mixedMoment B raw6121step3 raw6121step3Labels = mixedMoment B raw6121step4 raw6121step4Labels := by
      have ha : raw6121step4 = -raw6121step3 := by apply Matrix.ext; change ∀ i j, raw6121step4 i j = -(raw6121step3 i j); unfold raw6121step4 raw6121step3; decide +kernel
      have hl : raw6121step4Labels = raw6121step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3633 node3633Labels := by rfl

def raw6122 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6122Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6122step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw6122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6122step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6122step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6122 raw6122Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw6122 raw6122Labels = mixedMoment B raw6122step0 raw6122step0Labels := by
      have hz : ∀ j, raw6122 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6122step0 = (fun i j => raw6122 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6122step0 raw6122; decide +kernel
      have hl : raw6122step0Labels = raw6122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6122 raw6122Labels permutation346 hz
    mixedMoment B raw6122step0 raw6122step0Labels = mixedMoment B raw6122step1 raw6122step1Labels := by
      have ha : raw6122step1 = (fun i j => raw6122step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6122step1 raw6122step0; decide +kernel
      have hl : raw6122step1Labels = raw6122step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6122step0 raw6122step0Labels permutation36 permutation4
    mixedMoment B raw6122step1 raw6122step1Labels = mixedMoment B raw6122step2 raw6122step2Labels := by
      have ha : raw6122step2 = -raw6122step1 := by apply Matrix.ext; change ∀ i j, raw6122step2 i j = -(raw6122step1 i j); unfold raw6122step2 raw6122step1; decide +kernel
      have hl : raw6122step2Labels = raw6122step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw6123 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6123Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6123step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6123step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6123step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6123step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw6123step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6123step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6123step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6123 raw6123Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw6123 raw6123Labels = mixedMoment B raw6123step0 raw6123step0Labels := by
      have hz : ∀ j, raw6123 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6123step0 = (fun i j => raw6123 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6123step0 raw6123; decide +kernel
      have hl : raw6123step0Labels = raw6123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6123 raw6123Labels permutation434 hz
    mixedMoment B raw6123step0 raw6123step0Labels = mixedMoment B raw6123step1 raw6123step1Labels := by
      have hz : ∀ j, raw6123step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6123step1 = (fun i j => raw6123step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6123step1 raw6123step0; decide +kernel
      have hl : raw6123step1Labels = raw6123step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6123step0 raw6123step0Labels permutation80 hz
    mixedMoment B raw6123step1 raw6123step1Labels = mixedMoment B raw6123step2 raw6123step2Labels := by
      have ha : raw6123step2 = (fun i j => raw6123step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6123step2 raw6123step1; decide +kernel
      have hl : raw6123step2Labels = raw6123step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6123step1 raw6123step1Labels permutation9 permutation4
    mixedMoment B raw6123step2 raw6123step2Labels = mixedMoment B raw6123step3 raw6123step3Labels := by
      have ha : raw6123step3 = -raw6123step2 := by apply Matrix.ext; change ∀ i j, raw6123step3 i j = -(raw6123step2 i j); unfold raw6123step3 raw6123step2; decide +kernel
      have hl : raw6123step3Labels = raw6123step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3548 node3548Labels := by rfl

def raw6124 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6124Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6124step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6124step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6124step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw6124step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6124step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw6124step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6124 raw6124Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw6124 raw6124Labels = mixedMoment B raw6124step0 raw6124step0Labels := by
      have hz : ∀ j, raw6124 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6124step0 = (fun i j => raw6124 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6124step0 raw6124; decide +kernel
      have hl : raw6124step0Labels = raw6124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6124 raw6124Labels permutation434 hz
    mixedMoment B raw6124step0 raw6124step0Labels = mixedMoment B raw6124step1 raw6124step1Labels := by
      have hz : ∀ j, raw6124step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6124step1 = (fun i j => raw6124step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6124step1 raw6124step0; decide +kernel
      have hl : raw6124step1Labels = raw6124step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6124step0 raw6124step0Labels permutation80 hz
    mixedMoment B raw6124step1 raw6124step1Labels = mixedMoment B raw6124step2 raw6124step2Labels := by
      have ha : raw6124step2 = (fun i j => raw6124step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6124step2 raw6124step1; decide +kernel
      have hl : raw6124step2Labels = raw6124step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6124step1 raw6124step1Labels permutation9 permutation4
    mixedMoment B raw6124step2 raw6124step2Labels = mixedMoment B raw6124step3 raw6124step3Labels := by
      have ha : raw6124step3 = -raw6124step2 := by apply Matrix.ext; change ∀ i j, raw6124step3 i j = -(raw6124step2 i j); unfold raw6124step3 raw6124step2; decide +kernel
      have hl : raw6124step3Labels = raw6124step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2062 node2062Labels := by rfl

def raw6125 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6125Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw6125step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw6125step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6125 raw6125Labels = mixedMoment B node2879 node2879Labels := by
  calc
    mixedMoment B raw6125 raw6125Labels = mixedMoment B raw6125step0 raw6125step0Labels := by
      have hz : ∀ j, raw6125 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6125step0 = (fun i j => raw6125 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6125step0 raw6125; decide +kernel
      have hl : raw6125step0Labels = raw6125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6125 raw6125Labels permutation346 hz
    mixedMoment B raw6125step0 raw6125step0Labels = mixedMoment B raw6125step1 raw6125step1Labels := by
      have ha : raw6125step1 = (fun i j => raw6125step0 (permutation125 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6125step1 raw6125step0; decide +kernel
      have hl : raw6125step1Labels = raw6125step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6125step0 raw6125step0Labels permutation125 permutation4
    _ = mixedMoment B node2879 node2879Labels := by rfl

def raw6126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6126step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6126 raw6126Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw6126 raw6126Labels = mixedMoment B raw6126step0 raw6126step0Labels := by
      have hz : ∀ j, raw6126 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6126step0 = (fun i j => raw6126 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6126step0 raw6126; decide +kernel
      have hl : raw6126step0Labels = raw6126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6126 raw6126Labels permutation346 hz
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw6127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6127step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6127step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6127 raw6127Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw6127 raw6127Labels = mixedMoment B raw6127step0 raw6127step0Labels := by
      have ha : raw6127step0 = (fun i j => raw6127 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6127step0 raw6127; decide +kernel
      have hl : raw6127step0Labels = raw6127Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6127 raw6127Labels permutation176 permutation2
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw6128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6128step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6128step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6128 raw6128Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw6128 raw6128Labels = mixedMoment B raw6128step0 raw6128step0Labels := by
      have hz : ∀ j, raw6128 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6128step0 = (fun i j => raw6128 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6128step0 raw6128; decide +kernel
      have hl : raw6128step0Labels = raw6128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6128 raw6128Labels permutation346 hz
    mixedMoment B raw6128step0 raw6128step0Labels = mixedMoment B raw6128step1 raw6128step1Labels := by
      have ha : raw6128step1 = (fun i j => raw6128step0 (permutation135 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6128step1 raw6128step0; decide +kernel
      have hl : raw6128step1Labels = raw6128step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6128step0 raw6128step0Labels permutation135 permutation5
    mixedMoment B raw6128step1 raw6128step1Labels = mixedMoment B raw6128step2 raw6128step2Labels := by
      have ha : raw6128step2 = raw6128step1 := by apply Matrix.ext; unfold raw6128step2 raw6128step1; decide +kernel
      have hl : raw6128step1Labels = labelEmbedding8 ∘ raw6128step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6128step1 raw6128step1Labels raw6128step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5436 node5436Labels := by rfl

def raw6129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6129step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6129step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6129step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6129step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6129step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6129step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6129 raw6129Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw6129 raw6129Labels = mixedMoment B raw6129step0 raw6129step0Labels := by
      have hz : ∀ j, raw6129 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6129step0 = (fun i j => raw6129 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6129step0 raw6129; decide +kernel
      have hl : raw6129step0Labels = raw6129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6129 raw6129Labels permutation346 hz
    mixedMoment B raw6129step0 raw6129step0Labels = mixedMoment B raw6129step1 raw6129step1Labels := by
      have ha : raw6129step1 = (fun i j => raw6129step0 (permutation116 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6129step1 raw6129step0; decide +kernel
      have hl : raw6129step1Labels = raw6129step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6129step0 raw6129step0Labels permutation116 permutation4
    mixedMoment B raw6129step1 raw6129step1Labels = mixedMoment B raw6129step2 raw6129step2Labels := by
      have ha : raw6129step2 = -raw6129step1 := by apply Matrix.ext; change ∀ i j, raw6129step2 i j = -(raw6129step1 i j); unfold raw6129step2 raw6129step1; decide +kernel
      have hl : raw6129step2Labels = raw6129step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6129step2 raw6129step2Labels = mixedMoment B raw6129step3 raw6129step3Labels := by
      have ha : raw6129step3 = raw6129step2 := by apply Matrix.ext; unfold raw6129step3 raw6129step2; decide +kernel
      have hl : raw6129step2Labels = labelEmbedding7 ∘ raw6129step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6129step2 raw6129step2Labels raw6129step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw6130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6130step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw6130step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6130step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6130step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6130step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6130 raw6130Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw6130 raw6130Labels = mixedMoment B raw6130step0 raw6130step0Labels := by
      have hz : ∀ j, raw6130 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6130step0 = (fun i j => raw6130 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6130step0 raw6130; decide +kernel
      have hl : raw6130step0Labels = raw6130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6130 raw6130Labels permutation346 hz
    mixedMoment B raw6130step0 raw6130step0Labels = mixedMoment B raw6130step1 raw6130step1Labels := by
      have ha : raw6130step1 = (fun i j => raw6130step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6130step1 raw6130step0; decide +kernel
      have hl : raw6130step1Labels = raw6130step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6130step0 raw6130step0Labels permutation36 permutation7
    mixedMoment B raw6130step1 raw6130step1Labels = mixedMoment B raw6130step2 raw6130step2Labels := by
      have ha : raw6130step2 = -raw6130step1 := by apply Matrix.ext; change ∀ i j, raw6130step2 i j = -(raw6130step1 i j); unfold raw6130step2 raw6130step1; decide +kernel
      have hl : raw6130step2Labels = raw6130step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6130step2 raw6130step2Labels = mixedMoment B raw6130step3 raw6130step3Labels := by
      have ha : raw6130step3 = raw6130step2 := by apply Matrix.ext; unfold raw6130step3 raw6130step2; decide +kernel
      have hl : raw6130step2Labels = labelEmbedding10 ∘ raw6130step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6130step2 raw6130step2Labels raw6130step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw6131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6131step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw6131step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6131step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw6131step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6131 raw6131Labels = mixedMoment B node4597 node4597Labels := by
  calc
    mixedMoment B raw6131 raw6131Labels = mixedMoment B raw6131step0 raw6131step0Labels := by
      have hz : ∀ j, raw6131 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6131step0 = (fun i j => raw6131 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6131step0 raw6131; decide +kernel
      have hl : raw6131step0Labels = raw6131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6131 raw6131Labels permutation346 hz
    mixedMoment B raw6131step0 raw6131step0Labels = mixedMoment B raw6131step1 raw6131step1Labels := by
      have ha : raw6131step1 = (fun i j => raw6131step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6131step1 raw6131step0; decide +kernel
      have hl : raw6131step1Labels = raw6131step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6131step0 raw6131step0Labels permutation40 permutation3
    mixedMoment B raw6131step1 raw6131step1Labels = mixedMoment B raw6131step2 raw6131step2Labels := by
      have ha : raw6131step2 = raw6131step1 := by apply Matrix.ext; unfold raw6131step2 raw6131step1; decide +kernel
      have hl : raw6131step1Labels = labelEmbedding6 ∘ raw6131step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6131step1 raw6131step1Labels raw6131step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4597 node4597Labels := by rfl

def raw6132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw6132step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6132 raw6132Labels = mixedMoment B node5146 node5146Labels := by
  calc
    mixedMoment B raw6132 raw6132Labels = mixedMoment B raw6132step0 raw6132step0Labels := by
      have ha : raw6132step0 = (fun i j => raw6132 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6132step0 raw6132; decide +kernel
      have hl : raw6132step0Labels = raw6132Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6132 raw6132Labels permutation182 permutation2
    _ = mixedMoment B node5146 node5146Labels := by rfl

def raw6133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6133step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw6133step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6133 raw6133Labels = mixedMoment B node5200 node5200Labels := by
  calc
    mixedMoment B raw6133 raw6133Labels = mixedMoment B raw6133step0 raw6133step0Labels := by
      have hz : ∀ j, raw6133 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6133step0 = (fun i j => raw6133 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6133step0 raw6133; decide +kernel
      have hl : raw6133step0Labels = raw6133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6133 raw6133Labels permutation346 hz
    mixedMoment B raw6133step0 raw6133step0Labels = mixedMoment B raw6133step1 raw6133step1Labels := by
      have ha : raw6133step1 = (fun i j => raw6133step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6133step1 raw6133step0; decide +kernel
      have hl : raw6133step1Labels = raw6133step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6133step0 raw6133step0Labels permutation38 permutation2
    _ = mixedMoment B node5200 node5200Labels := by rfl

def raw6134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6134step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw6134step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6134 raw6134Labels = mixedMoment B node5287 node5287Labels := by
  calc
    mixedMoment B raw6134 raw6134Labels = mixedMoment B raw6134step0 raw6134step0Labels := by
      have hz : ∀ j, raw6134 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6134step0 = (fun i j => raw6134 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6134step0 raw6134; decide +kernel
      have hl : raw6134step0Labels = raw6134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6134 raw6134Labels permutation346 hz
    mixedMoment B raw6134step0 raw6134step0Labels = mixedMoment B raw6134step1 raw6134step1Labels := by
      have ha : raw6134step1 = (fun i j => raw6134step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6134step1 raw6134step0; decide +kernel
      have hl : raw6134step1Labels = raw6134step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6134step0 raw6134step0Labels permutation40 permutation2
    _ = mixedMoment B node5287 node5287Labels := by rfl

def raw6135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw6135step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6135 raw6135Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw6135 raw6135Labels = mixedMoment B raw6135step0 raw6135step0Labels := by
      have hz : ∀ j, raw6135 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6135step0 = (fun i j => raw6135 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6135step0 raw6135; decide +kernel
      have hl : raw6135step0Labels = raw6135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6135 raw6135Labels permutation346 hz
    mixedMoment B raw6135step0 raw6135step0Labels = mixedMoment B raw6135step1 raw6135step1Labels := by
      have ha : raw6135step1 = (fun i j => raw6135step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6135step1 raw6135step0; decide +kernel
      have hl : raw6135step1Labels = raw6135step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6135step0 raw6135step0Labels permutation39 permutation2
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw6136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw6136step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw6136step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6136 raw6136Labels = mixedMoment B node4587 node4587Labels := by
  calc
    mixedMoment B raw6136 raw6136Labels = mixedMoment B raw6136step0 raw6136step0Labels := by
      have ha : raw6136step0 = (fun i j => raw6136 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6136step0 raw6136; decide +kernel
      have hl : raw6136step0Labels = raw6136Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6136 raw6136Labels permutation202 permutation3
    mixedMoment B raw6136step0 raw6136step0Labels = mixedMoment B raw6136step1 raw6136step1Labels := by
      have ha : raw6136step1 = raw6136step0 := by apply Matrix.ext; unfold raw6136step1 raw6136step0; decide +kernel
      have hl : raw6136step0Labels = labelEmbedding6 ∘ raw6136step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6136step0 raw6136step0Labels raw6136step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4587 node4587Labels := by rfl

def raw6137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6137 raw6137Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw6137 raw6137Labels = mixedMoment B raw6137step0 raw6137step0Labels := by
      have ha : raw6137step0 = (fun i j => raw6137 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6137step0 raw6137; decide +kernel
      have hl : raw6137step0Labels = raw6137Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6137 raw6137Labels permutation158 permutation2
    _ = mixedMoment B node5074 node5074Labels := by rfl

def raw6138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6138step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6138 raw6138Labels = mixedMoment B node5186 node5186Labels := by
  calc
    mixedMoment B raw6138 raw6138Labels = mixedMoment B raw6138step0 raw6138step0Labels := by
      have ha : raw6138step0 = (fun i j => raw6138 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6138step0 raw6138; decide +kernel
      have hl : raw6138step0Labels = raw6138Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6138 raw6138Labels permutation200 permutation2
    _ = mixedMoment B node5186 node5186Labels := by rfl

def raw6139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6139 raw6139Labels = mixedMoment B node5254 node5254Labels := by
  calc
    mixedMoment B raw6139 raw6139Labels = mixedMoment B raw6139step0 raw6139step0Labels := by
      have ha : raw6139step0 = (fun i j => raw6139 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6139step0 raw6139; decide +kernel
      have hl : raw6139step0Labels = raw6139Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6139 raw6139Labels permutation160 permutation2
    _ = mixedMoment B node5254 node5254Labels := by rfl

def raw6140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw6140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6140 raw6140Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw6140 raw6140Labels = mixedMoment B raw6140step0 raw6140step0Labels := by
      have ha : raw6140step0 = (fun i j => raw6140 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6140step0 raw6140; decide +kernel
      have hl : raw6140step0Labels = raw6140Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6140 raw6140Labels permutation159 permutation2
    _ = mixedMoment B node5256 node5256Labels := by rfl

def raw6141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6141step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6141 raw6141Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw6141 raw6141Labels = mixedMoment B raw6141step0 raw6141step0Labels := by
      have hz : ∀ j, raw6141 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6141step0 = (fun i j => raw6141 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6141step0 raw6141; decide +kernel
      have hl : raw6141step0Labels = raw6141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6141 raw6141Labels permutation346 hz
    _ = mixedMoment B node4607 node4607Labels := by rfl

def raw6142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6142 raw6142Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw6142 raw6142Labels = mixedMoment B raw6142step0 raw6142step0Labels := by
      have hz : ∀ j, raw6142 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6142step0 = (fun i j => raw6142 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6142step0 raw6142; decide +kernel
      have hl : raw6142step0Labels = raw6142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6142 raw6142Labels permutation346 hz
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw6143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6143step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6143 raw6143Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw6143 raw6143Labels = mixedMoment B raw6143step0 raw6143step0Labels := by
      have ha : raw6143step0 = (fun i j => raw6143 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6143step0 raw6143; decide +kernel
      have hl : raw6143step0Labels = raw6143Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6143 raw6143Labels permutation176 permutation2
    _ = mixedMoment B node5138 node5138Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
