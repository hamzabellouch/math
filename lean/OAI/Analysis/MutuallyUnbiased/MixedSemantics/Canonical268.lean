import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw34304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw34304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34304step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34304step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34304 raw34304Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw34304 raw34304Labels = mixedMoment B raw34304step0 raw34304step0Labels := by
      have hz : ∀ j, raw34304 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34304step0 = (fun i j => raw34304 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34304step0 raw34304; decide +kernel
      have hl : raw34304step0Labels = raw34304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34304 raw34304Labels permutation520 hz
    mixedMoment B raw34304step0 raw34304step0Labels = mixedMoment B raw34304step1 raw34304step1Labels := by
      have hz : ∀ j, raw34304step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34304step1 = (fun i j => raw34304step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34304step1 raw34304step0; decide +kernel
      have hl : raw34304step1Labels = raw34304step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34304step0 raw34304step0Labels permutation80 hz
    _ = mixedMoment B node4846 node4846Labels := by rfl

def raw34305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw34305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw34305step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34305step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34305step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34305 raw34305Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw34305 raw34305Labels = mixedMoment B raw34305step0 raw34305step0Labels := by
      have hz : ∀ j, raw34305 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34305step0 = (fun i j => raw34305 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34305step0 raw34305; decide +kernel
      have hl : raw34305step0Labels = raw34305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34305 raw34305Labels permutation346 hz
    mixedMoment B raw34305step0 raw34305step0Labels = mixedMoment B raw34305step1 raw34305step1Labels := by
      have ha : raw34305step1 = (fun i j => raw34305step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34305step1 raw34305step0; decide +kernel
      have hl : raw34305step1Labels = raw34305step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34305step0 raw34305step0Labels permutation35 permutation2
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw34306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34306step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34306 raw34306Labels = mixedMoment B node4688 node4688Labels := by
  calc
    mixedMoment B raw34306 raw34306Labels = mixedMoment B raw34306step0 raw34306step0Labels := by
      have hz : ∀ j, raw34306 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34306step0 = (fun i j => raw34306 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34306step0 raw34306; decide +kernel
      have hl : raw34306step0Labels = raw34306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34306 raw34306Labels permutation346 hz
    _ = mixedMoment B node4688 node4688Labels := by rfl

def raw34307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34307 raw34307Labels = mixedMoment B node4766 node4766Labels := by
  calc
    _ = mixedMoment B node4766 node4766Labels := by rfl

def raw34308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34308step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34308 raw34308Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw34308 raw34308Labels = mixedMoment B raw34308step0 raw34308step0Labels := by
      have hz : ∀ j, raw34308 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34308step0 = (fun i j => raw34308 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34308step0 raw34308; decide +kernel
      have hl : raw34308step0Labels = raw34308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34308 raw34308Labels permutation346 hz
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw34309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw34309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw34309step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34309step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34309 raw34309Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw34309 raw34309Labels = mixedMoment B raw34309step0 raw34309step0Labels := by
      have hz : ∀ j, raw34309 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34309step0 = (fun i j => raw34309 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34309step0 raw34309; decide +kernel
      have hl : raw34309step0Labels = raw34309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34309 raw34309Labels permutation346 hz
    mixedMoment B raw34309step0 raw34309step0Labels = mixedMoment B raw34309step1 raw34309step1Labels := by
      have ha : raw34309step1 = (fun i j => raw34309step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34309step1 raw34309step0; decide +kernel
      have hl : raw34309step1Labels = raw34309step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34309step0 raw34309step0Labels permutation33 permutation2
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw34310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34310step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw34310step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34310 raw34310Labels = mixedMoment B node4681 node4681Labels := by
  calc
    mixedMoment B raw34310 raw34310Labels = mixedMoment B raw34310step0 raw34310step0Labels := by
      have hz : ∀ j, raw34310 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34310step0 = (fun i j => raw34310 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34310step0 raw34310; decide +kernel
      have hl : raw34310step0Labels = raw34310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34310 raw34310Labels permutation346 hz
    mixedMoment B raw34310step0 raw34310step0Labels = mixedMoment B raw34310step1 raw34310step1Labels := by
      have ha : raw34310step1 = (fun i j => raw34310step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34310step1 raw34310step0; decide +kernel
      have hl : raw34310step1Labels = raw34310step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34310step0 raw34310step0Labels permutation34 permutation2
    _ = mixedMoment B node4681 node4681Labels := by rfl

def raw34311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34311step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw34311step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34311 raw34311Labels = mixedMoment B node4760 node4760Labels := by
  calc
    mixedMoment B raw34311 raw34311Labels = mixedMoment B raw34311step0 raw34311step0Labels := by
      have ha : raw34311step0 = (fun i j => raw34311 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34311step0 raw34311; decide +kernel
      have hl : raw34311step0Labels = raw34311Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34311 raw34311Labels permutation154 permutation2
    _ = mixedMoment B node4760 node4760Labels := by rfl

def raw34312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34312step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34312 raw34312Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw34312 raw34312Labels = mixedMoment B raw34312step0 raw34312step0Labels := by
      have hz : ∀ j, raw34312 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34312step0 = (fun i j => raw34312 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34312step0 raw34312; decide +kernel
      have hl : raw34312step0Labels = raw34312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34312 raw34312Labels permutation346 hz
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw34313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw34313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw34313step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34313step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw34313step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34313 raw34313Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw34313 raw34313Labels = mixedMoment B raw34313step0 raw34313step0Labels := by
      have hz : ∀ j, raw34313 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34313step0 = (fun i j => raw34313 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34313step0 raw34313; decide +kernel
      have hl : raw34313step0Labels = raw34313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34313 raw34313Labels permutation520 hz
    mixedMoment B raw34313step0 raw34313step0Labels = mixedMoment B raw34313step1 raw34313step1Labels := by
      have hz : ∀ j, raw34313step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34313step1 = (fun i j => raw34313step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34313step1 raw34313step0; decide +kernel
      have hl : raw34313step1Labels = raw34313step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34313step0 raw34313step0Labels permutation80 hz
    _ = mixedMoment B node4841 node4841Labels := by rfl

def raw34314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34314step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw34314step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34314step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34314step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34314step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34314 raw34314Labels = mixedMoment B node5222 node5222Labels := by
  calc
    mixedMoment B raw34314 raw34314Labels = mixedMoment B raw34314step0 raw34314step0Labels := by
      have hz : ∀ j, raw34314 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34314step0 = (fun i j => raw34314 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34314step0 raw34314; decide +kernel
      have hl : raw34314step0Labels = raw34314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34314 raw34314Labels permutation346 hz
    mixedMoment B raw34314step0 raw34314step0Labels = mixedMoment B raw34314step1 raw34314step1Labels := by
      have ha : raw34314step1 = (fun i j => raw34314step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34314step1 raw34314step0; decide +kernel
      have hl : raw34314step1Labels = raw34314step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34314step0 raw34314step0Labels permutation32 permutation7
    mixedMoment B raw34314step1 raw34314step1Labels = mixedMoment B raw34314step2 raw34314step2Labels := by
      have ha : raw34314step2 = -raw34314step1 := by apply Matrix.ext; change ∀ i j, raw34314step2 i j = -(raw34314step1 i j); unfold raw34314step2 raw34314step1; decide +kernel
      have hl : raw34314step2Labels = raw34314step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34314step2 raw34314step2Labels = mixedMoment B raw34314step3 raw34314step3Labels := by
      have ha : raw34314step3 = raw34314step2 := by apply Matrix.ext; unfold raw34314step3 raw34314step2; decide +kernel
      have hl : raw34314step2Labels = labelEmbedding10 ∘ raw34314step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34314step2 raw34314step2Labels raw34314step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5222 node5222Labels := by rfl

def raw34315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34315step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34315step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34315step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34315 raw34315Labels = mixedMoment B node5239 node5239Labels := by
  calc
    mixedMoment B raw34315 raw34315Labels = mixedMoment B raw34315step0 raw34315step0Labels := by
      have ha : raw34315step0 = (fun i j => raw34315 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34315step0 raw34315; decide +kernel
      have hl : raw34315step0Labels = raw34315Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34315 raw34315Labels permutation662 permutation7
    mixedMoment B raw34315step0 raw34315step0Labels = mixedMoment B raw34315step1 raw34315step1Labels := by
      have ha : raw34315step1 = raw34315step0 := by apply Matrix.ext; unfold raw34315step1 raw34315step0; decide +kernel
      have hl : raw34315step0Labels = labelEmbedding10 ∘ raw34315step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34315step0 raw34315step0Labels raw34315step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5239 node5239Labels := by rfl

def raw34316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw34316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34316step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34316step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34316step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34316step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw34316step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34316step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw34316step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34316 raw34316Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw34316 raw34316Labels = mixedMoment B raw34316step0 raw34316step0Labels := by
      have hz : ∀ j, raw34316 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34316step0 = (fun i j => raw34316 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34316step0 raw34316; decide +kernel
      have hl : raw34316step0Labels = raw34316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34316 raw34316Labels permutation520 hz
    mixedMoment B raw34316step0 raw34316step0Labels = mixedMoment B raw34316step1 raw34316step1Labels := by
      have hz : ∀ j, raw34316step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34316step1 = (fun i j => raw34316step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34316step1 raw34316step0; decide +kernel
      have hl : raw34316step1Labels = raw34316step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34316step0 raw34316step0Labels permutation80 hz
    mixedMoment B raw34316step1 raw34316step1Labels = mixedMoment B raw34316step2 raw34316step2Labels := by
      have ha : raw34316step2 = (fun i j => raw34316step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34316step2 raw34316step1; decide +kernel
      have hl : raw34316step2Labels = raw34316step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34316step1 raw34316step1Labels permutation31 permutation7
    mixedMoment B raw34316step2 raw34316step2Labels = mixedMoment B raw34316step3 raw34316step3Labels := by
      have ha : raw34316step3 = raw34316step2 := by apply Matrix.ext; unfold raw34316step3 raw34316step2; decide +kernel
      have hl : raw34316step2Labels = labelEmbedding10 ∘ raw34316step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34316step2 raw34316step2Labels raw34316step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw34317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34317step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34317step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34317step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34317step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34317 raw34317Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw34317 raw34317Labels = mixedMoment B raw34317step0 raw34317step0Labels := by
      have hz : ∀ j, raw34317 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34317step0 = (fun i j => raw34317 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34317step0 raw34317; decide +kernel
      have hl : raw34317step0Labels = raw34317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34317 raw34317Labels permutation346 hz
    mixedMoment B raw34317step0 raw34317step0Labels = mixedMoment B raw34317step1 raw34317step1Labels := by
      have ha : raw34317step1 = (fun i j => raw34317step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34317step1 raw34317step0; decide +kernel
      have hl : raw34317step1Labels = raw34317step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34317step0 raw34317step0Labels permutation137 permutation6
    mixedMoment B raw34317step1 raw34317step1Labels = mixedMoment B raw34317step2 raw34317step2Labels := by
      have ha : raw34317step2 = raw34317step1 := by apply Matrix.ext; unfold raw34317step2 raw34317step1; decide +kernel
      have hl : raw34317step1Labels = labelEmbedding9 ∘ raw34317step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34317step1 raw34317step1Labels raw34317step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5252 node5252Labels := by rfl

def raw34318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34318 raw34318Labels = mixedMoment B node4675 node4675Labels := by
  calc
    _ = mixedMoment B node4675 node4675Labels := by rfl

def raw34319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw34319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34319step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34319 raw34319Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw34319 raw34319Labels = mixedMoment B raw34319step0 raw34319step0Labels := by
      have hz : ∀ j, raw34319 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34319step0 = (fun i j => raw34319 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34319step0 raw34319; decide +kernel
      have hl : raw34319step0Labels = raw34319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34319 raw34319Labels permutation520 hz
    _ = mixedMoment B node4832 node4832Labels := by rfl

def raw34320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34320 raw34320Labels = mixedMoment B node4830 node4830Labels := by
  calc
    _ = mixedMoment B node4830 node4830Labels := by rfl

def raw34321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34321step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34321step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34321step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34321 raw34321Labels = mixedMoment B node4683 node4683Labels := by
  calc
    mixedMoment B raw34321 raw34321Labels = mixedMoment B raw34321step0 raw34321step0Labels := by
      have hz : ∀ j, raw34321 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34321step0 = (fun i j => raw34321 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34321step0 raw34321; decide +kernel
      have hl : raw34321step0Labels = raw34321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34321 raw34321Labels permutation346 hz
    mixedMoment B raw34321step0 raw34321step0Labels = mixedMoment B raw34321step1 raw34321step1Labels := by
      have ha : raw34321step1 = (fun i j => raw34321step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34321step1 raw34321step0; decide +kernel
      have hl : raw34321step1Labels = raw34321step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34321step0 raw34321step0Labels permutation34 permutation2
    _ = mixedMoment B node4683 node4683Labels := by rfl

def raw34322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34322step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34322 raw34322Labels = mixedMoment B node4762 node4762Labels := by
  calc
    mixedMoment B raw34322 raw34322Labels = mixedMoment B raw34322step0 raw34322step0Labels := by
      have ha : raw34322step0 = (fun i j => raw34322 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34322step0 raw34322; decide +kernel
      have hl : raw34322step0Labels = raw34322Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34322 raw34322Labels permutation154 permutation2
    _ = mixedMoment B node4762 node4762Labels := by rfl

def raw34323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 1, -3]]
def raw34323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34323step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34323step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34323step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34323 raw34323Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw34323 raw34323Labels = mixedMoment B raw34323step0 raw34323step0Labels := by
      have hz : ∀ j, raw34323 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34323step0 = (fun i j => raw34323 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34323step0 raw34323; decide +kernel
      have hl : raw34323step0Labels = raw34323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34323 raw34323Labels permutation520 hz
    mixedMoment B raw34323step0 raw34323step0Labels = mixedMoment B raw34323step1 raw34323step1Labels := by
      have hz : ∀ j, raw34323step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34323step1 = (fun i j => raw34323step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34323step1 raw34323step0; decide +kernel
      have hl : raw34323step1Labels = raw34323step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34323step0 raw34323step0Labels permutation80 hz
    _ = mixedMoment B node4845 node4845Labels := by rfl

def raw34324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34324step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw34324step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34324 raw34324Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw34324 raw34324Labels = mixedMoment B raw34324step0 raw34324step0Labels := by
      have hz : ∀ j, raw34324 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34324step0 = (fun i j => raw34324 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34324step0 raw34324; decide +kernel
      have hl : raw34324step0Labels = raw34324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34324 raw34324Labels permutation346 hz
    mixedMoment B raw34324step0 raw34324step0Labels = mixedMoment B raw34324step1 raw34324step1Labels := by
      have ha : raw34324step1 = (fun i j => raw34324step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34324step1 raw34324step0; decide +kernel
      have hl : raw34324step1Labels = raw34324step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34324step0 raw34324step0Labels permutation35 permutation2
    _ = mixedMoment B node4836 node4836Labels := by rfl

def raw34325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34325step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34325 raw34325Labels = mixedMoment B node4683 node4683Labels := by
  calc
    mixedMoment B raw34325 raw34325Labels = mixedMoment B raw34325step0 raw34325step0Labels := by
      have hz : ∀ j, raw34325 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34325step0 = (fun i j => raw34325 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34325step0 raw34325; decide +kernel
      have hl : raw34325step0Labels = raw34325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34325 raw34325Labels permutation346 hz
    _ = mixedMoment B node4683 node4683Labels := by rfl

def raw34326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34326 raw34326Labels = mixedMoment B node4762 node4762Labels := by
  calc
    _ = mixedMoment B node4762 node4762Labels := by rfl

def raw34327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw34327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw34327step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw34327step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34327 raw34327Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw34327 raw34327Labels = mixedMoment B raw34327step0 raw34327step0Labels := by
      have hz : ∀ j, raw34327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34327step0 = (fun i j => raw34327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34327step0 raw34327; decide +kernel
      have hl : raw34327step0Labels = raw34327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34327 raw34327Labels permutation346 hz
    mixedMoment B raw34327step0 raw34327step0Labels = mixedMoment B raw34327step1 raw34327step1Labels := by
      have ha : raw34327step1 = (fun i j => raw34327step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34327step1 raw34327step0; decide +kernel
      have hl : raw34327step1Labels = raw34327step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34327step0 raw34327step0Labels permutation33 permutation2
    _ = mixedMoment B node4836 node4836Labels := by rfl

def raw34328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34328Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34328step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34328 raw34328Labels = mixedMoment B node3031 node3031Labels := by
  calc
    mixedMoment B raw34328 raw34328Labels = mixedMoment B raw34328step0 raw34328step0Labels := by
      have hz : ∀ j, raw34328 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34328step0 = (fun i j => raw34328 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34328step0 raw34328; decide +kernel
      have hl : raw34328step0Labels = raw34328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34328 raw34328Labels permutation346 hz
    mixedMoment B raw34328step0 raw34328step0Labels = mixedMoment B raw34328step1 raw34328step1Labels := by
      have ha : raw34328step1 = (fun i j => raw34328step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34328step1 raw34328step0; decide +kernel
      have hl : raw34328step1Labels = raw34328step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34328step0 raw34328step0Labels permutation137 permutation6
    _ = mixedMoment B node3031 node3031Labels := by rfl

def raw34329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34329Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34329step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34329step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34329 raw34329Labels = mixedMoment B node3061 node3061Labels := by
  calc
    mixedMoment B raw34329 raw34329Labels = mixedMoment B raw34329step0 raw34329step0Labels := by
      have ha : raw34329step0 = (fun i j => raw34329 (permutation609 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34329step0 raw34329; decide +kernel
      have hl : raw34329step0Labels = raw34329Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34329 raw34329Labels permutation609 permutation6
    _ = mixedMoment B node3061 node3061Labels := by rfl

def raw34330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34330Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34330step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34330step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34330step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34330step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw34330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34330 raw34330Labels = mixedMoment B node3090 node3090Labels := by
  calc
    mixedMoment B raw34330 raw34330Labels = mixedMoment B raw34330step0 raw34330step0Labels := by
      have hz : ∀ j, raw34330 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34330step0 = (fun i j => raw34330 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34330step0 raw34330; decide +kernel
      have hl : raw34330step0Labels = raw34330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34330 raw34330Labels permutation434 hz
    mixedMoment B raw34330step0 raw34330step0Labels = mixedMoment B raw34330step1 raw34330step1Labels := by
      have hz : ∀ j, raw34330step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34330step1 = (fun i j => raw34330step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34330step1 raw34330step0; decide +kernel
      have hl : raw34330step1Labels = raw34330step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34330step0 raw34330step0Labels permutation80 hz
    mixedMoment B raw34330step1 raw34330step1Labels = mixedMoment B raw34330step2 raw34330step2Labels := by
      have ha : raw34330step2 = (fun i j => raw34330step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34330step2 raw34330step1; decide +kernel
      have hl : raw34330step2Labels = raw34330step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34330step1 raw34330step1Labels permutation29 permutation6
    _ = mixedMoment B node3090 node3090Labels := by rfl

def raw34331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw34331Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34331step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34331step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34331step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34331step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw34331step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34331 raw34331Labels = mixedMoment B node3090 node3090Labels := by
  calc
    mixedMoment B raw34331 raw34331Labels = mixedMoment B raw34331step0 raw34331step0Labels := by
      have hz : ∀ j, raw34331 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34331step0 = (fun i j => raw34331 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34331step0 raw34331; decide +kernel
      have hl : raw34331step0Labels = raw34331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34331 raw34331Labels permutation520 hz
    mixedMoment B raw34331step0 raw34331step0Labels = mixedMoment B raw34331step1 raw34331step1Labels := by
      have hz : ∀ j, raw34331step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34331step1 = (fun i j => raw34331step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34331step1 raw34331step0; decide +kernel
      have hl : raw34331step1Labels = raw34331step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34331step0 raw34331step0Labels permutation80 hz
    mixedMoment B raw34331step1 raw34331step1Labels = mixedMoment B raw34331step2 raw34331step2Labels := by
      have ha : raw34331step2 = (fun i j => raw34331step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34331step2 raw34331step1; decide +kernel
      have hl : raw34331step2Labels = raw34331step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34331step1 raw34331step1Labels permutation29 permutation6
    _ = mixedMoment B node3090 node3090Labels := by rfl

def raw34332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34332Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34332step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34332step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34332 raw34332Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw34332 raw34332Labels = mixedMoment B raw34332step0 raw34332step0Labels := by
      have hz : ∀ j, raw34332 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34332step0 = (fun i j => raw34332 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34332step0 raw34332; decide +kernel
      have hl : raw34332step0Labels = raw34332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34332 raw34332Labels permutation346 hz
    mixedMoment B raw34332step0 raw34332step0Labels = mixedMoment B raw34332step1 raw34332step1Labels := by
      have ha : raw34332step1 = (fun i j => raw34332step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34332step1 raw34332step0; decide +kernel
      have hl : raw34332step1Labels = raw34332step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34332step0 raw34332step0Labels permutation137 permutation6
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw34333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34333Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34333step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34333step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34333step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34333step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34333 raw34333Labels = mixedMoment B node1451 node1451Labels := by
  calc
    mixedMoment B raw34333 raw34333Labels = mixedMoment B raw34333step0 raw34333step0Labels := by
      have hz : ∀ j, raw34333 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34333step0 = (fun i j => raw34333 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34333step0 raw34333; decide +kernel
      have hl : raw34333step0Labels = raw34333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34333 raw34333Labels permutation346 hz
    mixedMoment B raw34333step0 raw34333step0Labels = mixedMoment B raw34333step1 raw34333step1Labels := by
      have hz : ∀ j, raw34333step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw34333step1 = (fun i j => raw34333step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw34333step1 raw34333step0; decide +kernel
      have hl : raw34333step1Labels = raw34333step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34333step0 raw34333step0Labels permutation56 hz
    mixedMoment B raw34333step1 raw34333step1Labels = mixedMoment B raw34333step2 raw34333step2Labels := by
      have ha : raw34333step2 = (fun i j => raw34333step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34333step2 raw34333step1; decide +kernel
      have hl : raw34333step2Labels = raw34333step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34333step1 raw34333step1Labels permutation8 permutation3
    _ = mixedMoment B node1451 node1451Labels := by rfl

def raw34334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34334Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34334step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw34334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34334 raw34334Labels = mixedMoment B node3027 node3027Labels := by
  calc
    mixedMoment B raw34334 raw34334Labels = mixedMoment B raw34334step0 raw34334step0Labels := by
      have ha : raw34334step0 = (fun i j => raw34334 (permutation609 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34334step0 raw34334; decide +kernel
      have hl : raw34334step0Labels = raw34334Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34334 raw34334Labels permutation609 permutation6
    _ = mixedMoment B node3027 node3027Labels := by rfl

def raw34335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34335Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34335step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw34335step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34335 raw34335Labels = mixedMoment B node3082 node3082Labels := by
  calc
    mixedMoment B raw34335 raw34335Labels = mixedMoment B raw34335step0 raw34335step0Labels := by
      have hz : ∀ j, raw34335 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34335step0 = (fun i j => raw34335 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34335step0 raw34335; decide +kernel
      have hl : raw34335step0Labels = raw34335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34335 raw34335Labels permutation434 hz
    mixedMoment B raw34335step0 raw34335step0Labels = mixedMoment B raw34335step1 raw34335step1Labels := by
      have ha : raw34335step1 = (fun i j => raw34335step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34335step1 raw34335step0; decide +kernel
      have hl : raw34335step1Labels = raw34335step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34335step0 raw34335step0Labels permutation137 permutation6
    _ = mixedMoment B node3082 node3082Labels := by rfl

def raw34336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw34336Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34336step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw34336step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34336 raw34336Labels = mixedMoment B node3082 node3082Labels := by
  calc
    mixedMoment B raw34336 raw34336Labels = mixedMoment B raw34336step0 raw34336step0Labels := by
      have hz : ∀ j, raw34336 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34336step0 = (fun i j => raw34336 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34336step0 raw34336; decide +kernel
      have hl : raw34336step0Labels = raw34336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34336 raw34336Labels permutation520 hz
    mixedMoment B raw34336step0 raw34336step0Labels = mixedMoment B raw34336step1 raw34336step1Labels := by
      have ha : raw34336step1 = (fun i j => raw34336step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34336step1 raw34336step0; decide +kernel
      have hl : raw34336step1Labels = raw34336step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34336step0 raw34336step0Labels permutation137 permutation6
    _ = mixedMoment B node3082 node3082Labels := by rfl

def raw34337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34337Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34337step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw34337step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34337 raw34337Labels = mixedMoment B node2707 node2707Labels := by
  calc
    mixedMoment B raw34337 raw34337Labels = mixedMoment B raw34337step0 raw34337step0Labels := by
      have ha : raw34337step0 = (fun i j => raw34337 (permutation609 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34337step0 raw34337; decide +kernel
      have hl : raw34337step0Labels = raw34337Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34337 raw34337Labels permutation609 permutation6
    _ = mixedMoment B node2707 node2707Labels := by rfl

def raw34338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34338Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34338step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw34338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34338 raw34338Labels = mixedMoment B node3033 node3033Labels := by
  calc
    mixedMoment B raw34338 raw34338Labels = mixedMoment B raw34338step0 raw34338step0Labels := by
      have hz : ∀ j, raw34338 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34338step0 = (fun i j => raw34338 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34338step0 raw34338; decide +kernel
      have hl : raw34338step0Labels = raw34338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34338 raw34338Labels permutation346 hz
    mixedMoment B raw34338step0 raw34338step0Labels = mixedMoment B raw34338step1 raw34338step1Labels := by
      have ha : raw34338step1 = (fun i j => raw34338step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34338step1 raw34338step0; decide +kernel
      have hl : raw34338step1Labels = raw34338step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34338step0 raw34338step0Labels permutation139 permutation6
    _ = mixedMoment B node3033 node3033Labels := by rfl

def raw34339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34339Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34339step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw34339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34339 raw34339Labels = mixedMoment B node3062 node3062Labels := by
  calc
    mixedMoment B raw34339 raw34339Labels = mixedMoment B raw34339step0 raw34339step0Labels := by
      have ha : raw34339step0 = (fun i j => raw34339 (permutation611 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34339step0 raw34339; decide +kernel
      have hl : raw34339step0Labels = raw34339Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34339 raw34339Labels permutation611 permutation6
    _ = mixedMoment B node3062 node3062Labels := by rfl

def raw34340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 1, -3]]
def raw34340Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34340step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34340step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34340step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34340step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw34340step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34340 raw34340Labels = mixedMoment B node3095 node3095Labels := by
  calc
    mixedMoment B raw34340 raw34340Labels = mixedMoment B raw34340step0 raw34340step0Labels := by
      have hz : ∀ j, raw34340 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34340step0 = (fun i j => raw34340 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34340step0 raw34340; decide +kernel
      have hl : raw34340step0Labels = raw34340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34340 raw34340Labels permutation520 hz
    mixedMoment B raw34340step0 raw34340step0Labels = mixedMoment B raw34340step1 raw34340step1Labels := by
      have hz : ∀ j, raw34340step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34340step1 = (fun i j => raw34340step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34340step1 raw34340step0; decide +kernel
      have hl : raw34340step1Labels = raw34340step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34340step0 raw34340step0Labels permutation80 hz
    mixedMoment B raw34340step1 raw34340step1Labels = mixedMoment B raw34340step2 raw34340step2Labels := by
      have ha : raw34340step2 = (fun i j => raw34340step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34340step2 raw34340step1; decide +kernel
      have hl : raw34340step2Labels = raw34340step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34340step1 raw34340step1Labels permutation29 permutation6
    _ = mixedMoment B node3095 node3095Labels := by rfl

def raw34341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34341Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34341step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw34341step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34341 raw34341Labels = mixedMoment B node2716 node2716Labels := by
  calc
    mixedMoment B raw34341 raw34341Labels = mixedMoment B raw34341step0 raw34341step0Labels := by
      have hz : ∀ j, raw34341 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34341step0 = (fun i j => raw34341 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34341step0 raw34341; decide +kernel
      have hl : raw34341step0Labels = raw34341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34341 raw34341Labels permutation346 hz
    mixedMoment B raw34341step0 raw34341step0Labels = mixedMoment B raw34341step1 raw34341step1Labels := by
      have ha : raw34341step1 = (fun i j => raw34341step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34341step1 raw34341step0; decide +kernel
      have hl : raw34341step1Labels = raw34341step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34341step0 raw34341step0Labels permutation139 permutation6
    _ = mixedMoment B node2716 node2716Labels := by rfl

def raw34342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34342Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34342step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw34342step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34342 raw34342Labels = mixedMoment B node3033 node3033Labels := by
  calc
    mixedMoment B raw34342 raw34342Labels = mixedMoment B raw34342step0 raw34342step0Labels := by
      have hz : ∀ j, raw34342 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34342step0 = (fun i j => raw34342 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34342step0 raw34342; decide +kernel
      have hl : raw34342step0Labels = raw34342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34342 raw34342Labels permutation346 hz
    mixedMoment B raw34342step0 raw34342step0Labels = mixedMoment B raw34342step1 raw34342step1Labels := by
      have ha : raw34342step1 = (fun i j => raw34342step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34342step1 raw34342step0; decide +kernel
      have hl : raw34342step1Labels = raw34342step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34342step0 raw34342step0Labels permutation137 permutation6
    _ = mixedMoment B node3033 node3033Labels := by rfl

def raw34343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34343Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34343step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw34343step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34343 raw34343Labels = mixedMoment B node3062 node3062Labels := by
  calc
    mixedMoment B raw34343 raw34343Labels = mixedMoment B raw34343step0 raw34343step0Labels := by
      have ha : raw34343step0 = (fun i j => raw34343 (permutation609 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34343step0 raw34343; decide +kernel
      have hl : raw34343step0Labels = raw34343Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34343 raw34343Labels permutation609 permutation6
    _ = mixedMoment B node3062 node3062Labels := by rfl

def raw34344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34344Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34344step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34344step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34344step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34344step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw34344step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34344 raw34344Labels = mixedMoment B node3095 node3095Labels := by
  calc
    mixedMoment B raw34344 raw34344Labels = mixedMoment B raw34344step0 raw34344step0Labels := by
      have hz : ∀ j, raw34344 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34344step0 = (fun i j => raw34344 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34344step0 raw34344; decide +kernel
      have hl : raw34344step0Labels = raw34344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34344 raw34344Labels permutation434 hz
    mixedMoment B raw34344step0 raw34344step0Labels = mixedMoment B raw34344step1 raw34344step1Labels := by
      have hz : ∀ j, raw34344step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34344step1 = (fun i j => raw34344step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34344step1 raw34344step0; decide +kernel
      have hl : raw34344step1Labels = raw34344step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34344step0 raw34344step0Labels permutation80 hz
    mixedMoment B raw34344step1 raw34344step1Labels = mixedMoment B raw34344step2 raw34344step2Labels := by
      have ha : raw34344step2 = (fun i j => raw34344step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34344step2 raw34344step1; decide +kernel
      have hl : raw34344step2Labels = raw34344step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34344step1 raw34344step1Labels permutation29 permutation6
    _ = mixedMoment B node3095 node3095Labels := by rfl

def raw34345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw34345Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw34345step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw34345step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34345 raw34345Labels = mixedMoment B node2716 node2716Labels := by
  calc
    mixedMoment B raw34345 raw34345Labels = mixedMoment B raw34345step0 raw34345step0Labels := by
      have hz : ∀ j, raw34345 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34345step0 = (fun i j => raw34345 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34345step0 raw34345; decide +kernel
      have hl : raw34345step0Labels = raw34345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34345 raw34345Labels permutation346 hz
    mixedMoment B raw34345step0 raw34345step0Labels = mixedMoment B raw34345step1 raw34345step1Labels := by
      have ha : raw34345step1 = (fun i j => raw34345step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34345step1 raw34345step0; decide +kernel
      have hl : raw34345step1Labels = raw34345step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34345step0 raw34345step0Labels permutation137 permutation6
    _ = mixedMoment B node2716 node2716Labels := by rfl

def raw34346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34346Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34346step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw34346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34346 raw34346Labels = mixedMoment B node3143 node3143Labels := by
  calc
    mixedMoment B raw34346 raw34346Labels = mixedMoment B raw34346step0 raw34346step0Labels := by
      have hz : ∀ j, raw34346 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34346step0 = (fun i j => raw34346 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34346step0 raw34346; decide +kernel
      have hl : raw34346step0Labels = raw34346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34346 raw34346Labels permutation346 hz
    mixedMoment B raw34346step0 raw34346step0Labels = mixedMoment B raw34346step1 raw34346step1Labels := by
      have ha : raw34346step1 = (fun i j => raw34346step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34346step1 raw34346step0; decide +kernel
      have hl : raw34346step1Labels = raw34346step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34346step0 raw34346step0Labels permutation32 permutation3
    _ = mixedMoment B node3143 node3143Labels := by rfl

def raw34347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34347Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw34347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34347 raw34347Labels = mixedMoment B node3192 node3192Labels := by
  calc
    mixedMoment B raw34347 raw34347Labels = mixedMoment B raw34347step0 raw34347step0Labels := by
      have ha : raw34347step0 = (fun i j => raw34347 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34347step0 raw34347; decide +kernel
      have hl : raw34347step0Labels = raw34347Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34347 raw34347Labels permutation152 permutation3
    _ = mixedMoment B node3192 node3192Labels := by rfl

def raw34348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34348Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34348step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34348step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34348step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34348step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -3, 0]]
def raw34348step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34348 raw34348Labels = mixedMoment B node3215 node3215Labels := by
  calc
    mixedMoment B raw34348 raw34348Labels = mixedMoment B raw34348step0 raw34348step0Labels := by
      have hz : ∀ j, raw34348 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34348step0 = (fun i j => raw34348 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34348step0 raw34348; decide +kernel
      have hl : raw34348step0Labels = raw34348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34348 raw34348Labels permutation434 hz
    mixedMoment B raw34348step0 raw34348step0Labels = mixedMoment B raw34348step1 raw34348step1Labels := by
      have hz : ∀ j, raw34348step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34348step1 = (fun i j => raw34348step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34348step1 raw34348step0; decide +kernel
      have hl : raw34348step1Labels = raw34348step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34348step0 raw34348step0Labels permutation80 hz
    mixedMoment B raw34348step1 raw34348step1Labels = mixedMoment B raw34348step2 raw34348step2Labels := by
      have ha : raw34348step2 = (fun i j => raw34348step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34348step2 raw34348step1; decide +kernel
      have hl : raw34348step2Labels = raw34348step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34348step1 raw34348step1Labels permutation8 permutation3
    _ = mixedMoment B node3215 node3215Labels := by rfl

def raw34349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw34349Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34349step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34349step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34349step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34349step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -3, 0]]
def raw34349step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34349 raw34349Labels = mixedMoment B node3215 node3215Labels := by
  calc
    mixedMoment B raw34349 raw34349Labels = mixedMoment B raw34349step0 raw34349step0Labels := by
      have hz : ∀ j, raw34349 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34349step0 = (fun i j => raw34349 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34349step0 raw34349; decide +kernel
      have hl : raw34349step0Labels = raw34349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34349 raw34349Labels permutation520 hz
    mixedMoment B raw34349step0 raw34349step0Labels = mixedMoment B raw34349step1 raw34349step1Labels := by
      have hz : ∀ j, raw34349step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34349step1 = (fun i j => raw34349step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34349step1 raw34349step0; decide +kernel
      have hl : raw34349step1Labels = raw34349step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34349step0 raw34349step0Labels permutation80 hz
    mixedMoment B raw34349step1 raw34349step1Labels = mixedMoment B raw34349step2 raw34349step2Labels := by
      have ha : raw34349step2 = (fun i j => raw34349step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34349step2 raw34349step1; decide +kernel
      have hl : raw34349step2Labels = raw34349step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34349step1 raw34349step1Labels permutation8 permutation3
    _ = mixedMoment B node3215 node3215Labels := by rfl

def raw34350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34350Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34350step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw34350step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34350step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34350step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34350step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34350step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34350 raw34350Labels = mixedMoment B node2664 node2664Labels := by
  calc
    mixedMoment B raw34350 raw34350Labels = mixedMoment B raw34350step0 raw34350step0Labels := by
      have hz : ∀ j, raw34350 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34350step0 = (fun i j => raw34350 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34350step0 raw34350; decide +kernel
      have hl : raw34350step0Labels = raw34350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34350 raw34350Labels permutation346 hz
    mixedMoment B raw34350step0 raw34350step0Labels = mixedMoment B raw34350step1 raw34350step1Labels := by
      have ha : raw34350step1 = (fun i j => raw34350step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34350step1 raw34350step0; decide +kernel
      have hl : raw34350step1Labels = raw34350step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34350step0 raw34350step0Labels permutation32 permutation7
    mixedMoment B raw34350step1 raw34350step1Labels = mixedMoment B raw34350step2 raw34350step2Labels := by
      have ha : raw34350step2 = -raw34350step1 := by apply Matrix.ext; change ∀ i j, raw34350step2 i j = -(raw34350step1 i j); unfold raw34350step2 raw34350step1; decide +kernel
      have hl : raw34350step2Labels = raw34350step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34350step2 raw34350step2Labels = mixedMoment B raw34350step3 raw34350step3Labels := by
      have ha : raw34350step3 = raw34350step2 := by apply Matrix.ext; unfold raw34350step3 raw34350step2; decide +kernel
      have hl : raw34350step2Labels = labelEmbedding1 ∘ raw34350step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34350step2 raw34350step2Labels raw34350step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2664 node2664Labels := by rfl

def raw34351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34351Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34351step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34351step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34351 raw34351Labels = mixedMoment B node2691 node2691Labels := by
  calc
    mixedMoment B raw34351 raw34351Labels = mixedMoment B raw34351step0 raw34351step0Labels := by
      have ha : raw34351step0 = (fun i j => raw34351 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34351step0 raw34351; decide +kernel
      have hl : raw34351step0Labels = raw34351Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34351 raw34351Labels permutation662 permutation7
    mixedMoment B raw34351step0 raw34351step0Labels = mixedMoment B raw34351step1 raw34351step1Labels := by
      have ha : raw34351step1 = raw34351step0 := by apply Matrix.ext; unfold raw34351step1 raw34351step0; decide +kernel
      have hl : raw34351step0Labels = labelEmbedding1 ∘ raw34351step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34351step0 raw34351step0Labels raw34351step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2691 node2691Labels := by rfl

def raw34352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw34352Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34352step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34352step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34352step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34352step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw34352step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34352step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw34352step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34352 raw34352Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw34352 raw34352Labels = mixedMoment B raw34352step0 raw34352step0Labels := by
      have hz : ∀ j, raw34352 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34352step0 = (fun i j => raw34352 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34352step0 raw34352; decide +kernel
      have hl : raw34352step0Labels = raw34352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34352 raw34352Labels permutation520 hz
    mixedMoment B raw34352step0 raw34352step0Labels = mixedMoment B raw34352step1 raw34352step1Labels := by
      have hz : ∀ j, raw34352step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34352step1 = (fun i j => raw34352step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34352step1 raw34352step0; decide +kernel
      have hl : raw34352step1Labels = raw34352step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34352step0 raw34352step0Labels permutation80 hz
    mixedMoment B raw34352step1 raw34352step1Labels = mixedMoment B raw34352step2 raw34352step2Labels := by
      have ha : raw34352step2 = (fun i j => raw34352step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34352step2 raw34352step1; decide +kernel
      have hl : raw34352step2Labels = raw34352step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34352step1 raw34352step1Labels permutation31 permutation7
    mixedMoment B raw34352step2 raw34352step2Labels = mixedMoment B raw34352step3 raw34352step3Labels := by
      have ha : raw34352step3 = raw34352step2 := by apply Matrix.ext; unfold raw34352step3 raw34352step2; decide +kernel
      have hl : raw34352step2Labels = labelEmbedding1 ∘ raw34352step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34352step2 raw34352step2Labels raw34352step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2726 node2726Labels := by rfl

def raw34353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34353Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34353step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw34353step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34353step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34353step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34353step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34353step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34353 raw34353Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw34353 raw34353Labels = mixedMoment B raw34353step0 raw34353step0Labels := by
      have hz : ∀ j, raw34353 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34353step0 = (fun i j => raw34353 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34353step0 raw34353; decide +kernel
      have hl : raw34353step0Labels = raw34353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34353 raw34353Labels permutation346 hz
    mixedMoment B raw34353step0 raw34353step0Labels = mixedMoment B raw34353step1 raw34353step1Labels := by
      have ha : raw34353step1 = (fun i j => raw34353step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34353step1 raw34353step0; decide +kernel
      have hl : raw34353step1Labels = raw34353step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34353step0 raw34353step0Labels permutation32 permutation7
    mixedMoment B raw34353step1 raw34353step1Labels = mixedMoment B raw34353step2 raw34353step2Labels := by
      have ha : raw34353step2 = -raw34353step1 := by apply Matrix.ext; change ∀ i j, raw34353step2 i j = -(raw34353step1 i j); unfold raw34353step2 raw34353step1; decide +kernel
      have hl : raw34353step2Labels = raw34353step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34353step2 raw34353step2Labels = mixedMoment B raw34353step3 raw34353step3Labels := by
      have ha : raw34353step3 = raw34353step2 := by apply Matrix.ext; unfold raw34353step3 raw34353step2; decide +kernel
      have hl : raw34353step2Labels = labelEmbedding1 ∘ raw34353step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34353step2 raw34353step2Labels raw34353step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw34354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34354Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw34354step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34354step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34354step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34354step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34354step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34354 raw34354Labels = mixedMoment B node2139 node2139Labels := by
  calc
    mixedMoment B raw34354 raw34354Labels = mixedMoment B raw34354step0 raw34354step0Labels := by
      have ha : raw34354step0 = (fun i j => raw34354 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34354step0 raw34354; decide +kernel
      have hl : raw34354step0Labels = raw34354Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34354 raw34354Labels permutation152 permutation7
    mixedMoment B raw34354step0 raw34354step0Labels = mixedMoment B raw34354step1 raw34354step1Labels := by
      have ha : raw34354step1 = -raw34354step0 := by apply Matrix.ext; change ∀ i j, raw34354step1 i j = -(raw34354step0 i j); unfold raw34354step1 raw34354step0; decide +kernel
      have hl : raw34354step1Labels = raw34354step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34354step1 raw34354step1Labels = mixedMoment B raw34354step2 raw34354step2Labels := by
      have ha : raw34354step2 = raw34354step1 := by apply Matrix.ext; unfold raw34354step2 raw34354step1; decide +kernel
      have hl : raw34354step1Labels = labelEmbedding1 ∘ raw34354step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34354step1 raw34354step1Labels raw34354step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2139 node2139Labels := by rfl

def raw34355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw34355Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34355step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw34355step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34355step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34355step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34355step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34355step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34355 raw34355Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw34355 raw34355Labels = mixedMoment B raw34355step0 raw34355step0Labels := by
      have hz : ∀ j, raw34355 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34355step0 = (fun i j => raw34355 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34355step0 raw34355; decide +kernel
      have hl : raw34355step0Labels = raw34355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34355 raw34355Labels permutation520 hz
    mixedMoment B raw34355step0 raw34355step0Labels = mixedMoment B raw34355step1 raw34355step1Labels := by
      have ha : raw34355step1 = (fun i j => raw34355step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34355step1 raw34355step0; decide +kernel
      have hl : raw34355step1Labels = raw34355step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34355step0 raw34355step0Labels permutation32 permutation7
    mixedMoment B raw34355step1 raw34355step1Labels = mixedMoment B raw34355step2 raw34355step2Labels := by
      have ha : raw34355step2 = -raw34355step1 := by apply Matrix.ext; change ∀ i j, raw34355step2 i j = -(raw34355step1 i j); unfold raw34355step2 raw34355step1; decide +kernel
      have hl : raw34355step2Labels = raw34355step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34355step2 raw34355step2Labels = mixedMoment B raw34355step3 raw34355step3Labels := by
      have ha : raw34355step3 = raw34355step2 := by apply Matrix.ext; unfold raw34355step3 raw34355step2; decide +kernel
      have hl : raw34355step2Labels = labelEmbedding1 ∘ raw34355step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34355step2 raw34355step2Labels raw34355step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2193 node2193Labels := by rfl

def raw34356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34356Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34356step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw34356step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34356step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34356step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34356step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw34356step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34356 raw34356Labels = mixedMoment B node2187 node2187Labels := by
  calc
    mixedMoment B raw34356 raw34356Labels = mixedMoment B raw34356step0 raw34356step0Labels := by
      have ha : raw34356step0 = (fun i j => raw34356 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34356step0 raw34356; decide +kernel
      have hl : raw34356step0Labels = raw34356Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34356 raw34356Labels permutation152 permutation7
    mixedMoment B raw34356step0 raw34356step0Labels = mixedMoment B raw34356step1 raw34356step1Labels := by
      have ha : raw34356step1 = -raw34356step0 := by apply Matrix.ext; change ∀ i j, raw34356step1 i j = -(raw34356step0 i j); unfold raw34356step1 raw34356step0; decide +kernel
      have hl : raw34356step1Labels = raw34356step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34356step1 raw34356step1Labels = mixedMoment B raw34356step2 raw34356step2Labels := by
      have ha : raw34356step2 = raw34356step1 := by apply Matrix.ext; unfold raw34356step2 raw34356step1; decide +kernel
      have hl : raw34356step1Labels = labelEmbedding1 ∘ raw34356step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34356step1 raw34356step1Labels raw34356step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2187 node2187Labels := by rfl

def raw34357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34357Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34357step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw34357step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34357step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw34357step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34357step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw34357step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34357 raw34357Labels = mixedMoment B node2146 node2146Labels := by
  calc
    mixedMoment B raw34357 raw34357Labels = mixedMoment B raw34357step0 raw34357step0Labels := by
      have hz : ∀ j, raw34357 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34357step0 = (fun i j => raw34357 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34357step0 raw34357; decide +kernel
      have hl : raw34357step0Labels = raw34357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34357 raw34357Labels permutation346 hz
    mixedMoment B raw34357step0 raw34357step0Labels = mixedMoment B raw34357step1 raw34357step1Labels := by
      have ha : raw34357step1 = (fun i j => raw34357step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34357step1 raw34357step0; decide +kernel
      have hl : raw34357step1Labels = raw34357step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34357step0 raw34357step0Labels permutation34 permutation7
    mixedMoment B raw34357step1 raw34357step1Labels = mixedMoment B raw34357step2 raw34357step2Labels := by
      have ha : raw34357step2 = -raw34357step1 := by apply Matrix.ext; change ∀ i j, raw34357step2 i j = -(raw34357step1 i j); unfold raw34357step2 raw34357step1; decide +kernel
      have hl : raw34357step2Labels = raw34357step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34357step2 raw34357step2Labels = mixedMoment B raw34357step3 raw34357step3Labels := by
      have ha : raw34357step3 = raw34357step2 := by apply Matrix.ext; unfold raw34357step3 raw34357step2; decide +kernel
      have hl : raw34357step2Labels = labelEmbedding1 ∘ raw34357step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34357step2 raw34357step2Labels raw34357step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2146 node2146Labels := by rfl

def raw34358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34358Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34358step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw34358step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34358step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw34358step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34358step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw34358step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34358 raw34358Labels = mixedMoment B node2171 node2171Labels := by
  calc
    mixedMoment B raw34358 raw34358Labels = mixedMoment B raw34358step0 raw34358step0Labels := by
      have ha : raw34358step0 = (fun i j => raw34358 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34358step0 raw34358; decide +kernel
      have hl : raw34358step0Labels = raw34358Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34358 raw34358Labels permutation154 permutation7
    mixedMoment B raw34358step0 raw34358step0Labels = mixedMoment B raw34358step1 raw34358step1Labels := by
      have ha : raw34358step1 = -raw34358step0 := by apply Matrix.ext; change ∀ i j, raw34358step1 i j = -(raw34358step0 i j); unfold raw34358step1 raw34358step0; decide +kernel
      have hl : raw34358step1Labels = raw34358step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34358step1 raw34358step1Labels = mixedMoment B raw34358step2 raw34358step2Labels := by
      have ha : raw34358step2 = raw34358step1 := by apply Matrix.ext; unfold raw34358step2 raw34358step1; decide +kernel
      have hl : raw34358step1Labels = labelEmbedding1 ∘ raw34358step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34358step1 raw34358step1Labels raw34358step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2171 node2171Labels := by rfl

def raw34359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 1, -3]]
def raw34359Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34359step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34359step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34359step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34359step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw34359step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34359step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw34359step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34359step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw34359step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34359 raw34359Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw34359 raw34359Labels = mixedMoment B raw34359step0 raw34359step0Labels := by
      have hz : ∀ j, raw34359 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34359step0 = (fun i j => raw34359 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34359step0 raw34359; decide +kernel
      have hl : raw34359step0Labels = raw34359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34359 raw34359Labels permutation520 hz
    mixedMoment B raw34359step0 raw34359step0Labels = mixedMoment B raw34359step1 raw34359step1Labels := by
      have hz : ∀ j, raw34359step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34359step1 = (fun i j => raw34359step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34359step1 raw34359step0; decide +kernel
      have hl : raw34359step1Labels = raw34359step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34359step0 raw34359step0Labels permutation80 hz
    mixedMoment B raw34359step1 raw34359step1Labels = mixedMoment B raw34359step2 raw34359step2Labels := by
      have ha : raw34359step2 = (fun i j => raw34359step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34359step2 raw34359step1; decide +kernel
      have hl : raw34359step2Labels = raw34359step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34359step1 raw34359step1Labels permutation8 permutation7
    mixedMoment B raw34359step2 raw34359step2Labels = mixedMoment B raw34359step3 raw34359step3Labels := by
      have ha : raw34359step3 = -raw34359step2 := by apply Matrix.ext; change ∀ i j, raw34359step3 i j = -(raw34359step2 i j); unfold raw34359step3 raw34359step2; decide +kernel
      have hl : raw34359step3Labels = raw34359step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34359step3 raw34359step3Labels = mixedMoment B raw34359step4 raw34359step4Labels := by
      have ha : raw34359step4 = raw34359step3 := by apply Matrix.ext; unfold raw34359step4 raw34359step3; decide +kernel
      have hl : raw34359step3Labels = labelEmbedding1 ∘ raw34359step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34359step3 raw34359step3Labels raw34359step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2218 node2218Labels := by rfl

def raw34360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34360Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34360step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw34360step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34360step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw34360step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34360step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw34360step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34360 raw34360Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw34360 raw34360Labels = mixedMoment B raw34360step0 raw34360step0Labels := by
      have hz : ∀ j, raw34360 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34360step0 = (fun i j => raw34360 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34360step0 raw34360; decide +kernel
      have hl : raw34360step0Labels = raw34360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34360 raw34360Labels permutation346 hz
    mixedMoment B raw34360step0 raw34360step0Labels = mixedMoment B raw34360step1 raw34360step1Labels := by
      have ha : raw34360step1 = (fun i j => raw34360step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34360step1 raw34360step0; decide +kernel
      have hl : raw34360step1Labels = raw34360step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34360step0 raw34360step0Labels permutation34 permutation7
    mixedMoment B raw34360step1 raw34360step1Labels = mixedMoment B raw34360step2 raw34360step2Labels := by
      have ha : raw34360step2 = -raw34360step1 := by apply Matrix.ext; change ∀ i j, raw34360step2 i j = -(raw34360step1 i j); unfold raw34360step2 raw34360step1; decide +kernel
      have hl : raw34360step2Labels = raw34360step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34360step2 raw34360step2Labels = mixedMoment B raw34360step3 raw34360step3Labels := by
      have ha : raw34360step3 = raw34360step2 := by apply Matrix.ext; unfold raw34360step3 raw34360step2; decide +kernel
      have hl : raw34360step2Labels = labelEmbedding1 ∘ raw34360step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34360step2 raw34360step2Labels raw34360step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2197 node2197Labels := by rfl

def raw34361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34361Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34361step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw34361step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34361step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw34361step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34361step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw34361step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34361 raw34361Labels = mixedMoment B node2146 node2146Labels := by
  calc
    mixedMoment B raw34361 raw34361Labels = mixedMoment B raw34361step0 raw34361step0Labels := by
      have hz : ∀ j, raw34361 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34361step0 = (fun i j => raw34361 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34361step0 raw34361; decide +kernel
      have hl : raw34361step0Labels = raw34361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34361 raw34361Labels permutation346 hz
    mixedMoment B raw34361step0 raw34361step0Labels = mixedMoment B raw34361step1 raw34361step1Labels := by
      have ha : raw34361step1 = (fun i j => raw34361step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34361step1 raw34361step0; decide +kernel
      have hl : raw34361step1Labels = raw34361step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34361step0 raw34361step0Labels permutation32 permutation7
    mixedMoment B raw34361step1 raw34361step1Labels = mixedMoment B raw34361step2 raw34361step2Labels := by
      have ha : raw34361step2 = -raw34361step1 := by apply Matrix.ext; change ∀ i j, raw34361step2 i j = -(raw34361step1 i j); unfold raw34361step2 raw34361step1; decide +kernel
      have hl : raw34361step2Labels = raw34361step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34361step2 raw34361step2Labels = mixedMoment B raw34361step3 raw34361step3Labels := by
      have ha : raw34361step3 = raw34361step2 := by apply Matrix.ext; unfold raw34361step3 raw34361step2; decide +kernel
      have hl : raw34361step2Labels = labelEmbedding1 ∘ raw34361step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34361step2 raw34361step2Labels raw34361step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2146 node2146Labels := by rfl

def raw34362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34362Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw34362step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34362step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw34362step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34362step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw34362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34362 raw34362Labels = mixedMoment B node2171 node2171Labels := by
  calc
    mixedMoment B raw34362 raw34362Labels = mixedMoment B raw34362step0 raw34362step0Labels := by
      have ha : raw34362step0 = (fun i j => raw34362 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34362step0 raw34362; decide +kernel
      have hl : raw34362step0Labels = raw34362Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34362 raw34362Labels permutation152 permutation7
    mixedMoment B raw34362step0 raw34362step0Labels = mixedMoment B raw34362step1 raw34362step1Labels := by
      have ha : raw34362step1 = -raw34362step0 := by apply Matrix.ext; change ∀ i j, raw34362step1 i j = -(raw34362step0 i j); unfold raw34362step1 raw34362step0; decide +kernel
      have hl : raw34362step1Labels = raw34362step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34362step1 raw34362step1Labels = mixedMoment B raw34362step2 raw34362step2Labels := by
      have ha : raw34362step2 = raw34362step1 := by apply Matrix.ext; unfold raw34362step2 raw34362step1; decide +kernel
      have hl : raw34362step1Labels = labelEmbedding1 ∘ raw34362step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34362step1 raw34362step1Labels raw34362step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2171 node2171Labels := by rfl

def raw34363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw34363Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw34363step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw34363step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw34363step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34363step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw34363step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34363 raw34363Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw34363 raw34363Labels = mixedMoment B raw34363step0 raw34363step0Labels := by
      have hz : ∀ j, raw34363 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34363step0 = (fun i j => raw34363 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34363step0 raw34363; decide +kernel
      have hl : raw34363step0Labels = raw34363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34363 raw34363Labels permutation346 hz
    mixedMoment B raw34363step0 raw34363step0Labels = mixedMoment B raw34363step1 raw34363step1Labels := by
      have ha : raw34363step1 = (fun i j => raw34363step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34363step1 raw34363step0; decide +kernel
      have hl : raw34363step1Labels = raw34363step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34363step0 raw34363step0Labels permutation32 permutation7
    mixedMoment B raw34363step1 raw34363step1Labels = mixedMoment B raw34363step2 raw34363step2Labels := by
      have ha : raw34363step2 = -raw34363step1 := by apply Matrix.ext; change ∀ i j, raw34363step2 i j = -(raw34363step1 i j); unfold raw34363step2 raw34363step1; decide +kernel
      have hl : raw34363step2Labels = raw34363step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34363step2 raw34363step2Labels = mixedMoment B raw34363step3 raw34363step3Labels := by
      have ha : raw34363step3 = raw34363step2 := by apply Matrix.ext; unfold raw34363step3 raw34363step2; decide +kernel
      have hl : raw34363step2Labels = labelEmbedding1 ∘ raw34363step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34363step2 raw34363step2Labels raw34363step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2197 node2197Labels := by rfl

def raw34364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34364Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34364 raw34364Labels = mixedMoment B node3389 node3389Labels := by
  calc
    mixedMoment B raw34364 raw34364Labels = mixedMoment B raw34364step0 raw34364step0Labels := by
      have hz : ∀ j, raw34364 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34364step0 = (fun i j => raw34364 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34364step0 raw34364; decide +kernel
      have hl : raw34364step0Labels = raw34364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34364 raw34364Labels permutation346 hz
    _ = mixedMoment B node3389 node3389Labels := by rfl

def raw34365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34365Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34365step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34365 raw34365Labels = mixedMoment B node2052 node2052Labels := by
  calc
    mixedMoment B raw34365 raw34365Labels = mixedMoment B raw34365step0 raw34365step0Labels := by
      have hz : ∀ j, raw34365 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34365step0 = (fun i j => raw34365 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34365step0 raw34365; decide +kernel
      have hl : raw34365step0Labels = raw34365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34365 raw34365Labels permutation346 hz
    _ = mixedMoment B node2052 node2052Labels := by rfl

def raw34366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34366 raw34366Labels = mixedMoment B node1801 node1801Labels := by
  calc
    _ = mixedMoment B node1801 node1801Labels := by rfl

def raw34367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34367 raw34367Labels = mixedMoment B node1809 node1809Labels := by
  calc
    mixedMoment B raw34367 raw34367Labels = mixedMoment B raw34367step0 raw34367step0Labels := by
      have hz : ∀ j, raw34367 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34367step0 = (fun i j => raw34367 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34367step0 raw34367; decide +kernel
      have hl : raw34367step0Labels = raw34367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34367 raw34367Labels permutation346 hz
    mixedMoment B raw34367step0 raw34367step0Labels = mixedMoment B raw34367step1 raw34367step1Labels := by
      have ha : raw34367step1 = (fun i j => raw34367step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34367step1 raw34367step0; decide +kernel
      have hl : raw34367step1Labels = raw34367step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34367step0 raw34367step0Labels permutation34 permutation2
    _ = mixedMoment B node1809 node1809Labels := by rfl

def raw34368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34368 raw34368Labels = mixedMoment B node1809 node1809Labels := by
  calc
    mixedMoment B raw34368 raw34368Labels = mixedMoment B raw34368step0 raw34368step0Labels := by
      have hz : ∀ j, raw34368 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34368step0 = (fun i j => raw34368 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34368step0 raw34368; decide +kernel
      have hl : raw34368step0Labels = raw34368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34368 raw34368Labels permutation346 hz
    _ = mixedMoment B node1809 node1809Labels := by rfl

def raw34369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34369 raw34369Labels = mixedMoment B node918 node918Labels := by
  calc
    _ = mixedMoment B node918 node918Labels := by rfl

def raw34370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34370step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34370 raw34370Labels = mixedMoment B node2052 node2052Labels := by
  calc
    mixedMoment B raw34370 raw34370Labels = mixedMoment B raw34370step0 raw34370step0Labels := by
      have hz : ∀ j, raw34370 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34370step0 = (fun i j => raw34370 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34370step0 raw34370; decide +kernel
      have hl : raw34370step0Labels = raw34370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34370 raw34370Labels permutation434 hz
    _ = mixedMoment B node2052 node2052Labels := by rfl

def raw34371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw34371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw34371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34371 raw34371Labels = mixedMoment B node2052 node2052Labels := by
  calc
    mixedMoment B raw34371 raw34371Labels = mixedMoment B raw34371step0 raw34371step0Labels := by
      have hz : ∀ j, raw34371 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34371step0 = (fun i j => raw34371 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34371step0 raw34371; decide +kernel
      have hl : raw34371step0Labels = raw34371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34371 raw34371Labels permutation520 hz
    _ = mixedMoment B node2052 node2052Labels := by rfl

def raw34372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34372 raw34372Labels = mixedMoment B node2050 node2050Labels := by
  calc
    _ = mixedMoment B node2050 node2050Labels := by rfl

def raw34373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34373Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34373step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34373step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34373step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34373step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34373 raw34373Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw34373 raw34373Labels = mixedMoment B raw34373step0 raw34373step0Labels := by
      have ha : raw34373step0 = (fun i j => raw34373 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34373step0 raw34373; decide +kernel
      have hl : raw34373step0Labels = raw34373Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34373 raw34373Labels permutation176 permutation7
    mixedMoment B raw34373step0 raw34373step0Labels = mixedMoment B raw34373step1 raw34373step1Labels := by
      have ha : raw34373step1 = -raw34373step0 := by apply Matrix.ext; change ∀ i j, raw34373step1 i j = -(raw34373step0 i j); unfold raw34373step1 raw34373step0; decide +kernel
      have hl : raw34373step1Labels = raw34373step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34373step1 raw34373step1Labels = mixedMoment B raw34373step2 raw34373step2Labels := by
      have ha : raw34373step2 = raw34373step1 := by apply Matrix.ext; unfold raw34373step2 raw34373step1; decide +kernel
      have hl : raw34373step1Labels = labelEmbedding10 ∘ raw34373step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34373step1 raw34373step1Labels raw34373step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

def raw34374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34374step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34374step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34374step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34374step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34374step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34374 raw34374Labels = mixedMoment B node5058 node5058Labels := by
  calc
    mixedMoment B raw34374 raw34374Labels = mixedMoment B raw34374step0 raw34374step0Labels := by
      have ha : raw34374step0 = (fun i j => raw34374 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34374step0 raw34374; decide +kernel
      have hl : raw34374step0Labels = raw34374Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34374 raw34374Labels permutation176 permutation7
    mixedMoment B raw34374step0 raw34374step0Labels = mixedMoment B raw34374step1 raw34374step1Labels := by
      have ha : raw34374step1 = -raw34374step0 := by apply Matrix.ext; change ∀ i j, raw34374step1 i j = -(raw34374step0 i j); unfold raw34374step1 raw34374step0; decide +kernel
      have hl : raw34374step1Labels = raw34374step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34374step1 raw34374step1Labels = mixedMoment B raw34374step2 raw34374step2Labels := by
      have ha : raw34374step2 = raw34374step1 := by apply Matrix.ext; unfold raw34374step2 raw34374step1; decide +kernel
      have hl : raw34374step1Labels = labelEmbedding10 ∘ raw34374step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34374step1 raw34374step1Labels raw34374step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5058 node5058Labels := by rfl

def raw34375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw34375step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34375step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34375step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34375step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34375step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34375 raw34375Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw34375 raw34375Labels = mixedMoment B raw34375step0 raw34375step0Labels := by
      have ha : raw34375step0 = (fun i j => raw34375 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34375step0 raw34375; decide +kernel
      have hl : raw34375step0Labels = raw34375Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34375 raw34375Labels permutation176 permutation7
    mixedMoment B raw34375step0 raw34375step0Labels = mixedMoment B raw34375step1 raw34375step1Labels := by
      have ha : raw34375step1 = -raw34375step0 := by apply Matrix.ext; change ∀ i j, raw34375step1 i j = -(raw34375step0 i j); unfold raw34375step1 raw34375step0; decide +kernel
      have hl : raw34375step1Labels = raw34375step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34375step1 raw34375step1Labels = mixedMoment B raw34375step2 raw34375step2Labels := by
      have ha : raw34375step2 = raw34375step1 := by apply Matrix.ext; unfold raw34375step2 raw34375step1; decide +kernel
      have hl : raw34375step1Labels = labelEmbedding10 ∘ raw34375step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34375step1 raw34375step1Labels raw34375step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw34376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw34376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw34376step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34376step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34376step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34376step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34376step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34376 raw34376Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw34376 raw34376Labels = mixedMoment B raw34376step0 raw34376step0Labels := by
      have ha : raw34376step0 = (fun i j => raw34376 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34376step0 raw34376; decide +kernel
      have hl : raw34376step0Labels = raw34376Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34376 raw34376Labels permutation178 permutation7
    mixedMoment B raw34376step0 raw34376step0Labels = mixedMoment B raw34376step1 raw34376step1Labels := by
      have ha : raw34376step1 = -raw34376step0 := by apply Matrix.ext; change ∀ i j, raw34376step1 i j = -(raw34376step0 i j); unfold raw34376step1 raw34376step0; decide +kernel
      have hl : raw34376step1Labels = raw34376step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34376step1 raw34376step1Labels = mixedMoment B raw34376step2 raw34376step2Labels := by
      have ha : raw34376step2 = raw34376step1 := by apply Matrix.ext; unfold raw34376step2 raw34376step1; decide +kernel
      have hl : raw34376step1Labels = labelEmbedding10 ∘ raw34376step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34376step1 raw34376step1Labels raw34376step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw34377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34377step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34377step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34377step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34377step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34377step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34377 raw34377Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw34377 raw34377Labels = mixedMoment B raw34377step0 raw34377step0Labels := by
      have ha : raw34377step0 = (fun i j => raw34377 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34377step0 raw34377; decide +kernel
      have hl : raw34377step0Labels = raw34377Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34377 raw34377Labels permutation176 permutation7
    mixedMoment B raw34377step0 raw34377step0Labels = mixedMoment B raw34377step1 raw34377step1Labels := by
      have ha : raw34377step1 = -raw34377step0 := by apply Matrix.ext; change ∀ i j, raw34377step1 i j = -(raw34377step0 i j); unfold raw34377step1 raw34377step0; decide +kernel
      have hl : raw34377step1Labels = raw34377step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34377step1 raw34377step1Labels = mixedMoment B raw34377step2 raw34377step2Labels := by
      have ha : raw34377step2 = raw34377step1 := by apply Matrix.ext; unfold raw34377step2 raw34377step1; decide +kernel
      have hl : raw34377step1Labels = labelEmbedding10 ∘ raw34377step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34377step1 raw34377step1Labels raw34377step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5137 node5137Labels := by rfl

def raw34378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34378step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34378 raw34378Labels = mixedMoment B node4423 node4423Labels := by
  calc
    mixedMoment B raw34378 raw34378Labels = mixedMoment B raw34378step0 raw34378step0Labels := by
      have hz : ∀ j, raw34378 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw34378step0 = (fun i j => raw34378 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw34378step0 raw34378; decide +kernel
      have hl : raw34378step0Labels = raw34378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34378 raw34378Labels permutation265 hz
    _ = mixedMoment B node4423 node4423Labels := by rfl

def raw34379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34379 raw34379Labels = mixedMoment B node4672 node4672Labels := by
  calc
    _ = mixedMoment B node4672 node4672Labels := by rfl

def raw34380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34380step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34380 raw34380Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw34380 raw34380Labels = mixedMoment B raw34380step0 raw34380step0Labels := by
      have ha : raw34380step0 = (fun i j => raw34380 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34380step0 raw34380; decide +kernel
      have hl : raw34380step0Labels = raw34380Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34380 raw34380Labels permutation158 permutation2
    _ = mixedMoment B node4798 node4798Labels := by rfl

def raw34381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw34381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34381step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34381 raw34381Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw34381 raw34381Labels = mixedMoment B raw34381step0 raw34381step0Labels := by
      have ha : raw34381step0 = (fun i j => raw34381 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34381step0 raw34381; decide +kernel
      have hl : raw34381step0Labels = raw34381Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34381 raw34381Labels permutation164 permutation2
    _ = mixedMoment B node4798 node4798Labels := by rfl

def raw34382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34382 raw34382Labels = mixedMoment B node4826 node4826Labels := by
  calc
    _ = mixedMoment B node4826 node4826Labels := by rfl

def raw34383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34383 raw34383Labels = mixedMoment B node4661 node4661Labels := by
  calc
    mixedMoment B raw34383 raw34383Labels = mixedMoment B raw34383step0 raw34383step0Labels := by
      have ha : raw34383step0 = (fun i j => raw34383 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34383step0 raw34383; decide +kernel
      have hl : raw34383step0Labels = raw34383Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34383 raw34383Labels permutation154 permutation2
    _ = mixedMoment B node4661 node4661Labels := by rfl

def raw34384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34384 raw34384Labels = mixedMoment B node4715 node4715Labels := by
  calc
    mixedMoment B raw34384 raw34384Labels = mixedMoment B raw34384step0 raw34384step0Labels := by
      have ha : raw34384step0 = (fun i j => raw34384 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34384step0 raw34384; decide +kernel
      have hl : raw34384step0Labels = raw34384Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34384 raw34384Labels permutation178 permutation2
    _ = mixedMoment B node4715 node4715Labels := by rfl

def raw34385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw34385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34385 raw34385Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw34385 raw34385Labels = mixedMoment B raw34385step0 raw34385step0Labels := by
      have ha : raw34385step0 = (fun i j => raw34385 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34385step0 raw34385; decide +kernel
      have hl : raw34385step0Labels = raw34385Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34385 raw34385Labels permutation154 permutation2
    _ = mixedMoment B node4782 node4782Labels := by rfl

def raw34386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34386step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34386 raw34386Labels = mixedMoment B node4787 node4787Labels := by
  calc
    mixedMoment B raw34386 raw34386Labels = mixedMoment B raw34386step0 raw34386step0Labels := by
      have ha : raw34386step0 = (fun i j => raw34386 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34386step0 raw34386; decide +kernel
      have hl : raw34386step0Labels = raw34386Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34386 raw34386Labels permutation155 permutation2
    _ = mixedMoment B node4787 node4787Labels := by rfl

def raw34387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34387 raw34387Labels = mixedMoment B node4661 node4661Labels := by
  calc
    _ = mixedMoment B node4661 node4661Labels := by rfl

def raw34388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34388 raw34388Labels = mixedMoment B node4715 node4715Labels := by
  calc
    mixedMoment B raw34388 raw34388Labels = mixedMoment B raw34388step0 raw34388step0Labels := by
      have ha : raw34388step0 = (fun i j => raw34388 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34388step0 raw34388; decide +kernel
      have hl : raw34388step0Labels = raw34388Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34388 raw34388Labels permutation176 permutation2
    _ = mixedMoment B node4715 node4715Labels := by rfl

def raw34389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34389 raw34389Labels = mixedMoment B node4782 node4782Labels := by
  calc
    _ = mixedMoment B node4782 node4782Labels := by rfl

def raw34390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 1, -2]]
def raw34390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34390step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34390 raw34390Labels = mixedMoment B node4787 node4787Labels := by
  calc
    mixedMoment B raw34390 raw34390Labels = mixedMoment B raw34390step0 raw34390step0Labels := by
      have ha : raw34390step0 = (fun i j => raw34390 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34390step0 raw34390; decide +kernel
      have hl : raw34390step0Labels = raw34390Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34390 raw34390Labels permutation153 permutation2
    _ = mixedMoment B node4787 node4787Labels := by rfl

def raw34391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw34391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34391 raw34391Labels = mixedMoment B node4660 node4660Labels := by
  calc
    _ = mixedMoment B node4660 node4660Labels := by rfl

def raw34392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw34392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw34392step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34392 raw34392Labels = mixedMoment B node4712 node4712Labels := by
  calc
    mixedMoment B raw34392 raw34392Labels = mixedMoment B raw34392step0 raw34392step0Labels := by
      have ha : raw34392step0 = (fun i j => raw34392 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34392step0 raw34392; decide +kernel
      have hl : raw34392step0Labels = raw34392Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34392 raw34392Labels permutation176 permutation2
    _ = mixedMoment B node4712 node4712Labels := by rfl

def raw34393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw34393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34393 raw34393Labels = mixedMoment B node4779 node4779Labels := by
  calc
    _ = mixedMoment B node4779 node4779Labels := by rfl

def raw34394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -1, -2]]
def raw34394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw34394step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34394 raw34394Labels = mixedMoment B node4779 node4779Labels := by
  calc
    mixedMoment B raw34394 raw34394Labels = mixedMoment B raw34394step0 raw34394step0Labels := by
      have ha : raw34394step0 = (fun i j => raw34394 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34394step0 raw34394; decide +kernel
      have hl : raw34394step0Labels = raw34394Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34394 raw34394Labels permutation154 permutation2
    _ = mixedMoment B node4779 node4779Labels := by rfl

def raw34395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34395step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34395step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34395step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34395step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34395step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34395 raw34395Labels = mixedMoment B node4307 node4307Labels := by
  calc
    mixedMoment B raw34395 raw34395Labels = mixedMoment B raw34395step0 raw34395step0Labels := by
      have ha : raw34395step0 = (fun i j => raw34395 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34395step0 raw34395; decide +kernel
      have hl : raw34395step0Labels = raw34395Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34395 raw34395Labels permutation161 permutation4
    mixedMoment B raw34395step0 raw34395step0Labels = mixedMoment B raw34395step1 raw34395step1Labels := by
      have ha : raw34395step1 = -raw34395step0 := by apply Matrix.ext; change ∀ i j, raw34395step1 i j = -(raw34395step0 i j); unfold raw34395step1 raw34395step0; decide +kernel
      have hl : raw34395step1Labels = raw34395step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34395step1 raw34395step1Labels = mixedMoment B raw34395step2 raw34395step2Labels := by
      have ha : raw34395step2 = raw34395step1 := by apply Matrix.ext; unfold raw34395step2 raw34395step1; decide +kernel
      have hl : raw34395step1Labels = labelEmbedding7 ∘ raw34395step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34395step1 raw34395step1Labels raw34395step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4307 node4307Labels := by rfl

def raw34396 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34396step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34396step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34396step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34396step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34396 raw34396Labels = mixedMoment B node4648 node4648Labels := by
  calc
    mixedMoment B raw34396 raw34396Labels = mixedMoment B raw34396step0 raw34396step0Labels := by
      have ha : raw34396step0 = (fun i j => raw34396 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34396step0 raw34396; decide +kernel
      have hl : raw34396step0Labels = raw34396Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34396 raw34396Labels permutation161 permutation4
    mixedMoment B raw34396step0 raw34396step0Labels = mixedMoment B raw34396step1 raw34396step1Labels := by
      have ha : raw34396step1 = -raw34396step0 := by apply Matrix.ext; change ∀ i j, raw34396step1 i j = -(raw34396step0 i j); unfold raw34396step1 raw34396step0; decide +kernel
      have hl : raw34396step1Labels = raw34396step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34396step1 raw34396step1Labels = mixedMoment B raw34396step2 raw34396step2Labels := by
      have ha : raw34396step2 = raw34396step1 := by apply Matrix.ext; unfold raw34396step2 raw34396step1; decide +kernel
      have hl : raw34396step1Labels = labelEmbedding7 ∘ raw34396step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34396step1 raw34396step1Labels raw34396step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4648 node4648Labels := by rfl

def raw34397 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw34397step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34397step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34397step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34397step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34397step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34397 raw34397Labels = mixedMoment B node4740 node4740Labels := by
  calc
    mixedMoment B raw34397 raw34397Labels = mixedMoment B raw34397step0 raw34397step0Labels := by
      have ha : raw34397step0 = (fun i j => raw34397 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34397step0 raw34397; decide +kernel
      have hl : raw34397step0Labels = raw34397Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34397 raw34397Labels permutation161 permutation4
    mixedMoment B raw34397step0 raw34397step0Labels = mixedMoment B raw34397step1 raw34397step1Labels := by
      have ha : raw34397step1 = -raw34397step0 := by apply Matrix.ext; change ∀ i j, raw34397step1 i j = -(raw34397step0 i j); unfold raw34397step1 raw34397step0; decide +kernel
      have hl : raw34397step1Labels = raw34397step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34397step1 raw34397step1Labels = mixedMoment B raw34397step2 raw34397step2Labels := by
      have ha : raw34397step2 = raw34397step1 := by apply Matrix.ext; unfold raw34397step2 raw34397step1; decide +kernel
      have hl : raw34397step1Labels = labelEmbedding7 ∘ raw34397step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34397step1 raw34397step1Labels raw34397step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4740 node4740Labels := by rfl

def raw34398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34398step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34398step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34398step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34398step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34398step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34398 raw34398Labels = mixedMoment B node4301 node4301Labels := by
  calc
    mixedMoment B raw34398 raw34398Labels = mixedMoment B raw34398step0 raw34398step0Labels := by
      have ha : raw34398step0 = (fun i j => raw34398 (permutation155 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34398step0 raw34398; decide +kernel
      have hl : raw34398step0Labels = raw34398Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34398 raw34398Labels permutation155 permutation4
    mixedMoment B raw34398step0 raw34398step0Labels = mixedMoment B raw34398step1 raw34398step1Labels := by
      have ha : raw34398step1 = -raw34398step0 := by apply Matrix.ext; change ∀ i j, raw34398step1 i j = -(raw34398step0 i j); unfold raw34398step1 raw34398step0; decide +kernel
      have hl : raw34398step1Labels = raw34398step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34398step1 raw34398step1Labels = mixedMoment B raw34398step2 raw34398step2Labels := by
      have ha : raw34398step2 = raw34398step1 := by apply Matrix.ext; unfold raw34398step2 raw34398step1; decide +kernel
      have hl : raw34398step1Labels = labelEmbedding7 ∘ raw34398step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34398step1 raw34398step1Labels raw34398step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4301 node4301Labels := by rfl

def raw34399 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw34399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34399step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34399step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34399step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34399step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34399step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34399 raw34399Labels = mixedMoment B node4642 node4642Labels := by
  calc
    mixedMoment B raw34399 raw34399Labels = mixedMoment B raw34399step0 raw34399step0Labels := by
      have ha : raw34399step0 = (fun i j => raw34399 (permutation155 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34399step0 raw34399; decide +kernel
      have hl : raw34399step0Labels = raw34399Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34399 raw34399Labels permutation155 permutation4
    mixedMoment B raw34399step0 raw34399step0Labels = mixedMoment B raw34399step1 raw34399step1Labels := by
      have ha : raw34399step1 = -raw34399step0 := by apply Matrix.ext; change ∀ i j, raw34399step1 i j = -(raw34399step0 i j); unfold raw34399step1 raw34399step0; decide +kernel
      have hl : raw34399step1Labels = raw34399step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34399step1 raw34399step1Labels = mixedMoment B raw34399step2 raw34399step2Labels := by
      have ha : raw34399step2 = raw34399step1 := by apply Matrix.ext; unfold raw34399step2 raw34399step1; decide +kernel
      have hl : raw34399step1Labels = labelEmbedding7 ∘ raw34399step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34399step1 raw34399step1Labels raw34399step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4642 node4642Labels := by rfl

def raw34400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw34400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34400step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34400step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34400step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34400step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34400step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34400 raw34400Labels = mixedMoment B node4301 node4301Labels := by
  calc
    mixedMoment B raw34400 raw34400Labels = mixedMoment B raw34400step0 raw34400step0Labels := by
      have ha : raw34400step0 = (fun i j => raw34400 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34400step0 raw34400; decide +kernel
      have hl : raw34400step0Labels = raw34400Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34400 raw34400Labels permutation153 permutation4
    mixedMoment B raw34400step0 raw34400step0Labels = mixedMoment B raw34400step1 raw34400step1Labels := by
      have ha : raw34400step1 = -raw34400step0 := by apply Matrix.ext; change ∀ i j, raw34400step1 i j = -(raw34400step0 i j); unfold raw34400step1 raw34400step0; decide +kernel
      have hl : raw34400step1Labels = raw34400step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34400step1 raw34400step1Labels = mixedMoment B raw34400step2 raw34400step2Labels := by
      have ha : raw34400step2 = raw34400step1 := by apply Matrix.ext; unfold raw34400step2 raw34400step1; decide +kernel
      have hl : raw34400step1Labels = labelEmbedding7 ∘ raw34400step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34400step1 raw34400step1Labels raw34400step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4301 node4301Labels := by rfl

def raw34401 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw34401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34401step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34401step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34401step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34401step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34401step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34401 raw34401Labels = mixedMoment B node4642 node4642Labels := by
  calc
    mixedMoment B raw34401 raw34401Labels = mixedMoment B raw34401step0 raw34401step0Labels := by
      have ha : raw34401step0 = (fun i j => raw34401 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34401step0 raw34401; decide +kernel
      have hl : raw34401step0Labels = raw34401Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34401 raw34401Labels permutation153 permutation4
    mixedMoment B raw34401step0 raw34401step0Labels = mixedMoment B raw34401step1 raw34401step1Labels := by
      have ha : raw34401step1 = -raw34401step0 := by apply Matrix.ext; change ∀ i j, raw34401step1 i j = -(raw34401step0 i j); unfold raw34401step1 raw34401step0; decide +kernel
      have hl : raw34401step1Labels = raw34401step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34401step1 raw34401step1Labels = mixedMoment B raw34401step2 raw34401step2Labels := by
      have ha : raw34401step2 = raw34401step1 := by apply Matrix.ext; unfold raw34401step2 raw34401step1; decide +kernel
      have hl : raw34401step1Labels = labelEmbedding7 ∘ raw34401step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34401step1 raw34401step1Labels raw34401step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4642 node4642Labels := by rfl

def raw34402 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw34402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw34402step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34402step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34402step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34402step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34402step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34402step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34402 raw34402Labels = mixedMoment B node4752 node4752Labels := by
  calc
    mixedMoment B raw34402 raw34402Labels = mixedMoment B raw34402step0 raw34402step0Labels := by
      have hz : ∀ j, raw34402 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34402step0 = (fun i j => raw34402 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34402step0 raw34402; decide +kernel
      have hl : raw34402step0Labels = raw34402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34402 raw34402Labels permutation346 hz
    mixedMoment B raw34402step0 raw34402step0Labels = mixedMoment B raw34402step1 raw34402step1Labels := by
      have ha : raw34402step1 = (fun i j => raw34402step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34402step1 raw34402step0; decide +kernel
      have hl : raw34402step1Labels = raw34402step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34402step0 raw34402step0Labels permutation33 permutation4
    mixedMoment B raw34402step1 raw34402step1Labels = mixedMoment B raw34402step2 raw34402step2Labels := by
      have ha : raw34402step2 = -raw34402step1 := by apply Matrix.ext; change ∀ i j, raw34402step2 i j = -(raw34402step1 i j); unfold raw34402step2 raw34402step1; decide +kernel
      have hl : raw34402step2Labels = raw34402step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34402step2 raw34402step2Labels = mixedMoment B raw34402step3 raw34402step3Labels := by
      have ha : raw34402step3 = raw34402step2 := by apply Matrix.ext; unfold raw34402step3 raw34402step2; decide +kernel
      have hl : raw34402step2Labels = labelEmbedding7 ∘ raw34402step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34402step2 raw34402step2Labels raw34402step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4752 node4752Labels := by rfl

def raw34403 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw34403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw34403step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34403step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34403step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34403step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34403step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34403 raw34403Labels = mixedMoment B node4737 node4737Labels := by
  calc
    mixedMoment B raw34403 raw34403Labels = mixedMoment B raw34403step0 raw34403step0Labels := by
      have ha : raw34403step0 = (fun i j => raw34403 (permutation159 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34403step0 raw34403; decide +kernel
      have hl : raw34403step0Labels = raw34403Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34403 raw34403Labels permutation159 permutation4
    mixedMoment B raw34403step0 raw34403step0Labels = mixedMoment B raw34403step1 raw34403step1Labels := by
      have ha : raw34403step1 = -raw34403step0 := by apply Matrix.ext; change ∀ i j, raw34403step1 i j = -(raw34403step0 i j); unfold raw34403step1 raw34403step0; decide +kernel
      have hl : raw34403step1Labels = raw34403step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34403step1 raw34403step1Labels = mixedMoment B raw34403step2 raw34403step2Labels := by
      have ha : raw34403step2 = raw34403step1 := by apply Matrix.ext; unfold raw34403step2 raw34403step1; decide +kernel
      have hl : raw34403step1Labels = labelEmbedding7 ∘ raw34403step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34403step1 raw34403step1Labels raw34403step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4737 node4737Labels := by rfl

def raw34404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw34404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34404step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34404step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34404step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34404step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34404step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34404step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34404 raw34404Labels = mixedMoment B node4300 node4300Labels := by
  calc
    mixedMoment B raw34404 raw34404Labels = mixedMoment B raw34404step0 raw34404step0Labels := by
      have ha : raw34404step0 = (fun i j => raw34404 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34404step0 raw34404; decide +kernel
      have hl : raw34404step0Labels = raw34404Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34404 raw34404Labels permutation152 permutation4
    mixedMoment B raw34404step0 raw34404step0Labels = mixedMoment B raw34404step1 raw34404step1Labels := by
      have ha : raw34404step1 = -raw34404step0 := by apply Matrix.ext; change ∀ i j, raw34404step1 i j = -(raw34404step0 i j); unfold raw34404step1 raw34404step0; decide +kernel
      have hl : raw34404step1Labels = raw34404step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34404step1 raw34404step1Labels = mixedMoment B raw34404step2 raw34404step2Labels := by
      have ha : raw34404step2 = raw34404step1 := by apply Matrix.ext; unfold raw34404step2 raw34404step1; decide +kernel
      have hl : raw34404step1Labels = labelEmbedding7 ∘ raw34404step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34404step1 raw34404step1Labels raw34404step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4300 node4300Labels := by rfl

def raw34405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw34405Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34405step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw34405step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical34405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34405 raw34405Labels = mixedMoment B node4073 node4073Labels := by
  calc
    mixedMoment B raw34405 raw34405Labels = mixedMoment B raw34405step0 raw34405step0Labels := by
      have hz : ∀ i, raw34405 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34405step0 = (fun i j => raw34405 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34405step0 raw34405; decide +kernel
      have hl : raw34405step0Labels = (fun j => raw34405Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34405 raw34405Labels permutation6 hz
    _ = mixedMoment B node4073 node4073Labels := by rfl

def raw34406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw34406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw34406step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34406step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw34406step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical34406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34406 raw34406Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw34406 raw34406Labels = mixedMoment B raw34406step0 raw34406step0Labels := by
      have hz : ∀ j, raw34406 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34406step0 = (fun i j => raw34406 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34406step0 raw34406; decide +kernel
      have hl : raw34406step0Labels = raw34406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34406 raw34406Labels permutation520 hz
    mixedMoment B raw34406step0 raw34406step0Labels = mixedMoment B raw34406step1 raw34406step1Labels := by
      have hz : ∀ i, raw34406step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34406step1 = (fun i j => raw34406step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34406step1 raw34406step0; decide +kernel
      have hl : raw34406step1Labels = (fun j => raw34406step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34406step0 raw34406step0Labels permutation6 hz
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw34407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw34407Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw34407step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34407step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![1, -1], ![2, -2]]
def raw34407step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34407step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw34407step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical34407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34407 raw34407Labels = mixedMoment B node4075 node4075Labels := by
  calc
    mixedMoment B raw34407 raw34407Labels = mixedMoment B raw34407step0 raw34407step0Labels := by
      have hz : ∀ j, raw34407 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34407step0 = (fun i j => raw34407 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34407step0 raw34407; decide +kernel
      have hl : raw34407step0Labels = raw34407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34407 raw34407Labels permutation346 hz
    mixedMoment B raw34407step0 raw34407step0Labels = mixedMoment B raw34407step1 raw34407step1Labels := by
      have hz : ∀ i, raw34407step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34407step1 = (fun i j => raw34407step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34407step1 raw34407step0; decide +kernel
      have hl : raw34407step1Labels = (fun j => raw34407step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34407step0 raw34407step0Labels permutation6 hz
    mixedMoment B raw34407step1 raw34407step1Labels = mixedMoment B raw34407step2 raw34407step2Labels := by
      have ha : raw34407step2 = (fun i j => raw34407step1 (permutation34 i) (permutation0 j)) := by apply Matrix.ext; unfold raw34407step2 raw34407step1; decide +kernel
      have hl : raw34407step2Labels = raw34407step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34407step1 raw34407step1Labels permutation34 permutation0
    _ = mixedMoment B node4075 node4075Labels := by rfl

def raw34408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw34408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34408step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![2, -2]]
def raw34408step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34408step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw34408step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical34408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34408 raw34408Labels = mixedMoment B node4078 node4078Labels := by
  calc
    mixedMoment B raw34408 raw34408Labels = mixedMoment B raw34408step0 raw34408step0Labels := by
      have hz : ∀ i, raw34408 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34408step0 = (fun i j => raw34408 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34408step0 raw34408; decide +kernel
      have hl : raw34408step0Labels = (fun j => raw34408Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34408 raw34408Labels permutation6 hz
    mixedMoment B raw34408step0 raw34408step0Labels = mixedMoment B raw34408step1 raw34408step1Labels := by
      have ha : raw34408step1 = (fun i j => raw34408step0 (permutation154 i) (permutation0 j)) := by apply Matrix.ext; unfold raw34408step1 raw34408step0; decide +kernel
      have hl : raw34408step1Labels = raw34408step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34408step0 raw34408step0Labels permutation154 permutation0
    _ = mixedMoment B node4078 node4078Labels := by rfl

def raw34409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, -2, 0]]
def raw34409Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw34409step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34409step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -2, 0]]
def raw34409step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34409step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw34409step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical34409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34409 raw34409Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw34409 raw34409Labels = mixedMoment B raw34409step0 raw34409step0Labels := by
      have hz : ∀ j, raw34409 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34409step0 = (fun i j => raw34409 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34409step0 raw34409; decide +kernel
      have hl : raw34409step0Labels = raw34409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34409 raw34409Labels permutation520 hz
    mixedMoment B raw34409step0 raw34409step0Labels = mixedMoment B raw34409step1 raw34409step1Labels := by
      have hz : ∀ j, raw34409step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34409step1 = (fun i j => raw34409step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34409step1 raw34409step0; decide +kernel
      have hl : raw34409step1Labels = raw34409step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34409step0 raw34409step0Labels permutation80 hz
    mixedMoment B raw34409step1 raw34409step1Labels = mixedMoment B raw34409step2 raw34409step2Labels := by
      have hz : ∀ i, raw34409step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw34409step2 = (fun i j => raw34409step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw34409step2 raw34409step1; decide +kernel
      have hl : raw34409step2Labels = (fun j => raw34409step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw34409step1 raw34409step1Labels permutation6 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw34410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34410 raw34410Labels = mixedMoment B node3390 node3390Labels := by
  calc
    mixedMoment B raw34410 raw34410Labels = mixedMoment B raw34410step0 raw34410step0Labels := by
      have ha : raw34410step0 = (fun i j => raw34410 (permutation283 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34410step0 raw34410; decide +kernel
      have hl : raw34410step0Labels = raw34410Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34410 raw34410Labels permutation283 permutation2
    _ = mixedMoment B node3390 node3390Labels := by rfl

def raw34411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34411 raw34411Labels = mixedMoment B node3155 node3155Labels := by
  calc
    mixedMoment B raw34411 raw34411Labels = mixedMoment B raw34411step0 raw34411step0Labels := by
      have ha : raw34411step0 = (fun i j => raw34411 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34411step0 raw34411; decide +kernel
      have hl : raw34411step0Labels = raw34411Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34411 raw34411Labels permutation170 permutation2
    _ = mixedMoment B node3155 node3155Labels := by rfl

def raw34412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34412Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34412 raw34412Labels = mixedMoment B node3128 node3128Labels := by
  calc
    mixedMoment B raw34412 raw34412Labels = mixedMoment B raw34412step0 raw34412step0Labels := by
      have ha : raw34412step0 = (fun i j => raw34412 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34412step0 raw34412; decide +kernel
      have hl : raw34412step0Labels = raw34412Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34412 raw34412Labels permutation173 permutation2
    _ = mixedMoment B node3128 node3128Labels := by rfl

def raw34413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34413 raw34413Labels = mixedMoment B node3128 node3128Labels := by
  calc
    mixedMoment B raw34413 raw34413Labels = mixedMoment B raw34413step0 raw34413step0Labels := by
      have ha : raw34413step0 = (fun i j => raw34413 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34413step0 raw34413; decide +kernel
      have hl : raw34413step0Labels = raw34413Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34413 raw34413Labels permutation171 permutation2
    _ = mixedMoment B node3128 node3128Labels := by rfl

def raw34414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw34414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34414 raw34414Labels = mixedMoment B node3128 node3128Labels := by
  calc
    mixedMoment B raw34414 raw34414Labels = mixedMoment B raw34414step0 raw34414step0Labels := by
      have ha : raw34414step0 = (fun i j => raw34414 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34414step0 raw34414; decide +kernel
      have hl : raw34414step0Labels = raw34414Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34414 raw34414Labels permutation170 permutation2
    _ = mixedMoment B node3128 node3128Labels := by rfl

def raw34415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34415Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34415 raw34415Labels = mixedMoment B node3130 node3130Labels := by
  calc
    _ = mixedMoment B node3130 node3130Labels := by rfl

def raw34416 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]
def raw34416Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34416step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw34416step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34416step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw34416step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical34416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34416 raw34416Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw34416 raw34416Labels = mixedMoment B raw34416step0 raw34416step0Labels := by
      have hz : ∀ j, raw34416 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34416step0 = (fun i j => raw34416 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34416step0 raw34416; decide +kernel
      have hl : raw34416step0Labels = raw34416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34416 raw34416Labels permutation590 hz
    mixedMoment B raw34416step0 raw34416step0Labels = mixedMoment B raw34416step1 raw34416step1Labels := by
      have hz : ∀ j, raw34416step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw34416step1 = (fun i j => raw34416step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw34416step1 raw34416step0; decide +kernel
      have hl : raw34416step1Labels = raw34416step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34416step0 raw34416step0Labels permutation32 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw34417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34417step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34417 raw34417Labels = mixedMoment B node4969 node4969Labels := by
  calc
    mixedMoment B raw34417 raw34417Labels = mixedMoment B raw34417step0 raw34417step0Labels := by
      have ha : raw34417step0 = (fun i j => raw34417 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34417step0 raw34417; decide +kernel
      have hl : raw34417step0Labels = raw34417Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34417 raw34417Labels permutation161 permutation2
    _ = mixedMoment B node4969 node4969Labels := by rfl

def raw34418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34418step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34418step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34418 raw34418Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw34418 raw34418Labels = mixedMoment B raw34418step0 raw34418step0Labels := by
      have hz : ∀ j, raw34418 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34418step0 = (fun i j => raw34418 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34418step0 raw34418; decide +kernel
      have hl : raw34418step0Labels = raw34418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34418 raw34418Labels permutation434 hz
    mixedMoment B raw34418step0 raw34418step0Labels = mixedMoment B raw34418step1 raw34418step1Labels := by
      have ha : raw34418step1 = (fun i j => raw34418step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34418step1 raw34418step0; decide +kernel
      have hl : raw34418step1Labels = raw34418step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34418step0 raw34418step0Labels permutation35 permutation2
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw34419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw34419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34419step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34419step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34419 raw34419Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw34419 raw34419Labels = mixedMoment B raw34419step0 raw34419step0Labels := by
      have hz : ∀ j, raw34419 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34419step0 = (fun i j => raw34419 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34419step0 raw34419; decide +kernel
      have hl : raw34419step0Labels = raw34419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34419 raw34419Labels permutation520 hz
    mixedMoment B raw34419step0 raw34419step0Labels = mixedMoment B raw34419step1 raw34419step1Labels := by
      have ha : raw34419step1 = (fun i j => raw34419step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34419step1 raw34419step0; decide +kernel
      have hl : raw34419step1Labels = raw34419step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34419step0 raw34419step0Labels permutation35 permutation2
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw34420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw34420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34420step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw34420step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34420 raw34420Labels = mixedMoment B node5155 node5155Labels := by
  calc
    mixedMoment B raw34420 raw34420Labels = mixedMoment B raw34420step0 raw34420step0Labels := by
      have ha : raw34420step0 = (fun i j => raw34420 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34420step0 raw34420; decide +kernel
      have hl : raw34420step0Labels = raw34420Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34420 raw34420Labels permutation173 permutation2
    _ = mixedMoment B node5155 node5155Labels := by rfl

def raw34421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34421step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34421 raw34421Labels = mixedMoment B node4969 node4969Labels := by
  calc
    mixedMoment B raw34421 raw34421Labels = mixedMoment B raw34421step0 raw34421step0Labels := by
      have ha : raw34421step0 = (fun i j => raw34421 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34421step0 raw34421; decide +kernel
      have hl : raw34421step0Labels = raw34421Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34421 raw34421Labels permutation155 permutation2
    _ = mixedMoment B node4969 node4969Labels := by rfl

def raw34422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw34422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34422step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34422step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34422 raw34422Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw34422 raw34422Labels = mixedMoment B raw34422step0 raw34422step0Labels := by
      have hz : ∀ j, raw34422 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34422step0 = (fun i j => raw34422 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34422step0 raw34422; decide +kernel
      have hl : raw34422step0Labels = raw34422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34422 raw34422Labels permutation520 hz
    mixedMoment B raw34422step0 raw34422step0Labels = mixedMoment B raw34422step1 raw34422step1Labels := by
      have ha : raw34422step1 = (fun i j => raw34422step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34422step1 raw34422step0; decide +kernel
      have hl : raw34422step1Labels = raw34422step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34422step0 raw34422step0Labels permutation33 permutation2
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw34423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw34423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw34423step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34423 raw34423Labels = mixedMoment B node5155 node5155Labels := by
  calc
    mixedMoment B raw34423 raw34423Labels = mixedMoment B raw34423step0 raw34423step0Labels := by
      have ha : raw34423step0 = (fun i j => raw34423 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34423step0 raw34423; decide +kernel
      have hl : raw34423step0Labels = raw34423Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34423 raw34423Labels permutation171 permutation2
    _ = mixedMoment B node5155 node5155Labels := by rfl

def raw34424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34424step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34424 raw34424Labels = mixedMoment B node4969 node4969Labels := by
  calc
    mixedMoment B raw34424 raw34424Labels = mixedMoment B raw34424step0 raw34424step0Labels := by
      have ha : raw34424step0 = (fun i j => raw34424 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34424step0 raw34424; decide +kernel
      have hl : raw34424step0Labels = raw34424Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34424 raw34424Labels permutation153 permutation2
    _ = mixedMoment B node4969 node4969Labels := by rfl

def raw34425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw34425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34425step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw34425step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34425 raw34425Labels = mixedMoment B node5155 node5155Labels := by
  calc
    mixedMoment B raw34425 raw34425Labels = mixedMoment B raw34425step0 raw34425step0Labels := by
      have ha : raw34425step0 = (fun i j => raw34425 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34425step0 raw34425; decide +kernel
      have hl : raw34425step0Labels = raw34425Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34425 raw34425Labels permutation170 permutation2
    _ = mixedMoment B node5155 node5155Labels := by rfl

def raw34426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34426 raw34426Labels = mixedMoment B node5386 node5386Labels := by
  calc
    _ = mixedMoment B node5386 node5386Labels := by rfl

def raw34427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34427step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34427 raw34427Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw34427 raw34427Labels = mixedMoment B raw34427step0 raw34427step0Labels := by
      have hz : ∀ j, raw34427 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34427step0 = (fun i j => raw34427 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34427step0 raw34427; decide +kernel
      have hl : raw34427step0Labels = raw34427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34427 raw34427Labels permutation434 hz
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw34428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw34428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34428step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34428 raw34428Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw34428 raw34428Labels = mixedMoment B raw34428step0 raw34428step0Labels := by
      have ha : raw34428step0 = (fun i j => raw34428 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34428step0 raw34428; decide +kernel
      have hl : raw34428step0Labels = raw34428Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34428 raw34428Labels permutation164 permutation2
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw34429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw34429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34429step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34429 raw34429Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw34429 raw34429Labels = mixedMoment B raw34429step0 raw34429step0Labels := by
      have ha : raw34429step0 = (fun i j => raw34429 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34429step0 raw34429; decide +kernel
      have hl : raw34429step0Labels = raw34429Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34429 raw34429Labels permutation170 permutation2
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw34430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34430step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34430 raw34430Labels = mixedMoment B node4971 node4971Labels := by
  calc
    mixedMoment B raw34430 raw34430Labels = mixedMoment B raw34430step0 raw34430step0Labels := by
      have ha : raw34430step0 = (fun i j => raw34430 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34430step0 raw34430; decide +kernel
      have hl : raw34430step0Labels = raw34430Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34430 raw34430Labels permutation161 permutation2
    _ = mixedMoment B node4971 node4971Labels := by rfl

def raw34431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34431step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34431step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34431 raw34431Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw34431 raw34431Labels = mixedMoment B raw34431step0 raw34431step0Labels := by
      have hz : ∀ j, raw34431 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34431step0 = (fun i j => raw34431 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34431step0 raw34431; decide +kernel
      have hl : raw34431step0Labels = raw34431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34431 raw34431Labels permutation434 hz
    mixedMoment B raw34431step0 raw34431step0Labels = mixedMoment B raw34431step1 raw34431step1Labels := by
      have ha : raw34431step1 = (fun i j => raw34431step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34431step1 raw34431step0; decide +kernel
      have hl : raw34431step1Labels = raw34431step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34431step0 raw34431step0Labels permutation35 permutation2
    _ = mixedMoment B node5172 node5172Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
