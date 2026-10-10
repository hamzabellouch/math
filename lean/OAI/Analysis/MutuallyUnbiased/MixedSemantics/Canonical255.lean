import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw32640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32640Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32640step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw32640step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32640 raw32640Labels = mixedMoment B node5193 node5193Labels := by
  calc
    mixedMoment B raw32640 raw32640Labels = mixedMoment B raw32640step0 raw32640step0Labels := by
      have hz : ∀ j, raw32640 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32640step0 = (fun i j => raw32640 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32640step0 raw32640; decide +kernel
      have hl : raw32640step0Labels = raw32640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32640 raw32640Labels permutation346 hz
    mixedMoment B raw32640step0 raw32640step0Labels = mixedMoment B raw32640step1 raw32640step1Labels := by
      have ha : raw32640step1 = (fun i j => raw32640step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32640step1 raw32640step0; decide +kernel
      have hl : raw32640step1Labels = raw32640step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32640step0 raw32640step0Labels permutation34 permutation2
    _ = mixedMoment B node5193 node5193Labels := by rfl

def raw32641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, -1, 0]]
def raw32641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1], ![1, -1, 0]]
def raw32641step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32641step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32641 raw32641Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw32641 raw32641Labels = mixedMoment B raw32641step0 raw32641step0Labels := by
      have hz : ∀ j, raw32641 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32641step0 = (fun i j => raw32641 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32641step0 raw32641; decide +kernel
      have hl : raw32641step0Labels = raw32641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32641 raw32641Labels permutation346 hz
    mixedMoment B raw32641step0 raw32641step0Labels = mixedMoment B raw32641step1 raw32641step1Labels := by
      have ha : raw32641step1 = (fun i j => raw32641step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32641step1 raw32641step0; decide +kernel
      have hl : raw32641step1Labels = raw32641step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32641step0 raw32641step0Labels permutation37 permutation2
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw32642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw32642Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw32642step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32642step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32642step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32642step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32642 raw32642Labels = mixedMoment B node4518 node4518Labels := by
  calc
    mixedMoment B raw32642 raw32642Labels = mixedMoment B raw32642step0 raw32642step0Labels := by
      have hz : ∀ j, raw32642 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32642step0 = (fun i j => raw32642 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32642step0 raw32642; decide +kernel
      have hl : raw32642step0Labels = raw32642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32642 raw32642Labels permutation346 hz
    mixedMoment B raw32642step0 raw32642step0Labels = mixedMoment B raw32642step1 raw32642step1Labels := by
      have ha : raw32642step1 = (fun i j => raw32642step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32642step1 raw32642step0; decide +kernel
      have hl : raw32642step1Labels = raw32642step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32642step0 raw32642step0Labels permutation32 permutation3
    mixedMoment B raw32642step1 raw32642step1Labels = mixedMoment B raw32642step2 raw32642step2Labels := by
      have ha : raw32642step2 = raw32642step1 := by apply Matrix.ext; unfold raw32642step2 raw32642step1; decide +kernel
      have hl : raw32642step1Labels = labelEmbedding6 ∘ raw32642step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32642step1 raw32642step1Labels raw32642step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4518 node4518Labels := by rfl

def raw32643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw32643Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw32643step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32643step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32643 raw32643Labels = mixedMoment B node4983 node4983Labels := by
  calc
    mixedMoment B raw32643 raw32643Labels = mixedMoment B raw32643step0 raw32643step0Labels := by
      have hz : ∀ j, raw32643 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32643step0 = (fun i j => raw32643 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32643step0 raw32643; decide +kernel
      have hl : raw32643step0Labels = raw32643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32643 raw32643Labels permutation346 hz
    mixedMoment B raw32643step0 raw32643step0Labels = mixedMoment B raw32643step1 raw32643step1Labels := by
      have ha : raw32643step1 = (fun i j => raw32643step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32643step1 raw32643step0; decide +kernel
      have hl : raw32643step1Labels = raw32643step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32643step0 raw32643step0Labels permutation33 permutation2
    _ = mixedMoment B node4983 node4983Labels := by rfl

def raw32644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw32644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32644step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32644 raw32644Labels = mixedMoment B node5119 node5119Labels := by
  calc
    mixedMoment B raw32644 raw32644Labels = mixedMoment B raw32644step0 raw32644step0Labels := by
      have ha : raw32644step0 = (fun i j => raw32644 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32644step0 raw32644; decide +kernel
      have hl : raw32644step0Labels = raw32644Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32644 raw32644Labels permutation177 permutation2
    _ = mixedMoment B node5119 node5119Labels := by rfl

def raw32645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw32645Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw32645step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32645step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32645 raw32645Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw32645 raw32645Labels = mixedMoment B raw32645step0 raw32645step0Labels := by
      have hz : ∀ j, raw32645 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32645step0 = (fun i j => raw32645 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32645step0 raw32645; decide +kernel
      have hl : raw32645step0Labels = raw32645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32645 raw32645Labels permutation346 hz
    mixedMoment B raw32645step0 raw32645step0Labels = mixedMoment B raw32645step1 raw32645step1Labels := by
      have ha : raw32645step1 = (fun i j => raw32645step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32645step1 raw32645step0; decide +kernel
      have hl : raw32645step1Labels = raw32645step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32645step0 raw32645step0Labels permutation33 permutation2
    _ = mixedMoment B node5203 node5203Labels := by rfl

def raw32646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw32646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw32646step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw32646step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32646step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw32646step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32646step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw32646step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32646step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw32646step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32646 raw32646Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw32646 raw32646Labels = mixedMoment B raw32646step0 raw32646step0Labels := by
      have hz : ∀ j, raw32646 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32646step0 = (fun i j => raw32646 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32646step0 raw32646; decide +kernel
      have hl : raw32646step0Labels = raw32646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32646 raw32646Labels permutation434 hz
    mixedMoment B raw32646step0 raw32646step0Labels = mixedMoment B raw32646step1 raw32646step1Labels := by
      have hz : ∀ j, raw32646step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32646step1 = (fun i j => raw32646step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32646step1 raw32646step0; decide +kernel
      have hl : raw32646step1Labels = raw32646step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32646step0 raw32646step0Labels permutation80 hz
    mixedMoment B raw32646step1 raw32646step1Labels = mixedMoment B raw32646step2 raw32646step2Labels := by
      have ha : raw32646step2 = (fun i j => raw32646step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32646step2 raw32646step1; decide +kernel
      have hl : raw32646step2Labels = raw32646step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32646step1 raw32646step1Labels permutation31 permutation3
    mixedMoment B raw32646step2 raw32646step2Labels = mixedMoment B raw32646step3 raw32646step3Labels := by
      have ha : raw32646step3 = -raw32646step2 := by apply Matrix.ext; change ∀ i j, raw32646step3 i j = -(raw32646step2 i j); unfold raw32646step3 raw32646step2; decide +kernel
      have hl : raw32646step3Labels = raw32646step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32646step3 raw32646step3Labels = mixedMoment B raw32646step4 raw32646step4Labels := by
      have ha : raw32646step4 = raw32646step3 := by apply Matrix.ext; unfold raw32646step4 raw32646step3; decide +kernel
      have hl : raw32646step3Labels = labelEmbedding6 ∘ raw32646step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32646step3 raw32646step3Labels raw32646step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4843 node4843Labels := by rfl

def raw32647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32647 raw32647Labels = mixedMoment B node3391 node3391Labels := by
  calc
    mixedMoment B raw32647 raw32647Labels = mixedMoment B raw32647step0 raw32647step0Labels := by
      have hz : ∀ j, raw32647 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32647step0 = (fun i j => raw32647 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32647step0 raw32647; decide +kernel
      have hl : raw32647step0Labels = raw32647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32647 raw32647Labels permutation346 hz
    mixedMoment B raw32647step0 raw32647step0Labels = mixedMoment B raw32647step1 raw32647step1Labels := by
      have ha : raw32647step1 = (fun i j => raw32647step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32647step1 raw32647step0; decide +kernel
      have hl : raw32647step1Labels = raw32647step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32647step0 raw32647step0Labels permutation58 permutation3
    _ = mixedMoment B node3391 node3391Labels := by rfl

def raw32648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw32648step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32648 raw32648Labels = mixedMoment B node3782 node3782Labels := by
  calc
    mixedMoment B raw32648 raw32648Labels = mixedMoment B raw32648step0 raw32648step0Labels := by
      have ha : raw32648step0 = (fun i j => raw32648 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32648step0 raw32648; decide +kernel
      have hl : raw32648step0Labels = raw32648Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32648 raw32648Labels permutation664 permutation3
    mixedMoment B raw32648step0 raw32648step0Labels = mixedMoment B raw32648step1 raw32648step1Labels := by
      have ha : raw32648step1 = -raw32648step0 := by apply Matrix.ext; change ∀ i j, raw32648step1 i j = -(raw32648step0 i j); unfold raw32648step1 raw32648step0; decide +kernel
      have hl : raw32648step1Labels = raw32648step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3782 node3782Labels := by rfl

def raw32649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32649step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw32649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32649 raw32649Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw32649 raw32649Labels = mixedMoment B raw32649step0 raw32649step0Labels := by
      have hz : ∀ j, raw32649 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32649step0 = (fun i j => raw32649 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32649step0 raw32649; decide +kernel
      have hl : raw32649step0Labels = raw32649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32649 raw32649Labels permutation346 hz
    mixedMoment B raw32649step0 raw32649step0Labels = mixedMoment B raw32649step1 raw32649step1Labels := by
      have ha : raw32649step1 = (fun i j => raw32649step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32649step1 raw32649step0; decide +kernel
      have hl : raw32649step1Labels = raw32649step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32649step0 raw32649step0Labels permutation145 permutation3
    mixedMoment B raw32649step1 raw32649step1Labels = mixedMoment B raw32649step2 raw32649step2Labels := by
      have ha : raw32649step2 = -raw32649step1 := by apply Matrix.ext; change ∀ i j, raw32649step2 i j = -(raw32649step1 i j); unfold raw32649step2 raw32649step1; decide +kernel
      have hl : raw32649step2Labels = raw32649step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw32650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw32650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw32650step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32650step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32650 raw32650Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw32650 raw32650Labels = mixedMoment B raw32650step0 raw32650step0Labels := by
      have hz : ∀ j, raw32650 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32650step0 = (fun i j => raw32650 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32650step0 raw32650; decide +kernel
      have hl : raw32650step0Labels = raw32650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32650 raw32650Labels permutation346 hz
    mixedMoment B raw32650step0 raw32650step0Labels = mixedMoment B raw32650step1 raw32650step1Labels := by
      have ha : raw32650step1 = (fun i j => raw32650step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32650step1 raw32650step0; decide +kernel
      have hl : raw32650step1Labels = raw32650step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32650step0 raw32650step0Labels permutation34 permutation3
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw32651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32651Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32651step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32651step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32651 raw32651Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw32651 raw32651Labels = mixedMoment B raw32651step0 raw32651step0Labels := by
      have hz : ∀ j, raw32651 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32651step0 = (fun i j => raw32651 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32651step0 raw32651; decide +kernel
      have hl : raw32651step0Labels = raw32651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32651 raw32651Labels permutation346 hz
    mixedMoment B raw32651step0 raw32651step0Labels = mixedMoment B raw32651step1 raw32651step1Labels := by
      have ha : raw32651step1 = (fun i j => raw32651step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32651step1 raw32651step0; decide +kernel
      have hl : raw32651step1Labels = raw32651step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32651step0 raw32651step0Labels permutation34 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw32652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32652Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32652step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32652 raw32652Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw32652 raw32652Labels = mixedMoment B raw32652step0 raw32652step0Labels := by
      have ha : raw32652step0 = (fun i j => raw32652 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32652step0 raw32652; decide +kernel
      have hl : raw32652step0Labels = raw32652Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32652 raw32652Labels permutation178 permutation3
    _ = mixedMoment B node2924 node2924Labels := by rfl

def raw32653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32653Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32653step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32653 raw32653Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw32653 raw32653Labels = mixedMoment B raw32653step0 raw32653step0Labels := by
      have hz : ∀ j, raw32653 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32653step0 = (fun i j => raw32653 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32653step0 raw32653; decide +kernel
      have hl : raw32653step0Labels = raw32653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32653 raw32653Labels permutation346 hz
    mixedMoment B raw32653step0 raw32653step0Labels = mixedMoment B raw32653step1 raw32653step1Labels := by
      have ha : raw32653step1 = (fun i j => raw32653step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32653step1 raw32653step0; decide +kernel
      have hl : raw32653step1Labels = raw32653step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32653step0 raw32653step0Labels permutation34 permutation3
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw32654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw32654Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw32654step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32654 raw32654Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw32654 raw32654Labels = mixedMoment B raw32654step0 raw32654step0Labels := by
      have hz : ∀ j, raw32654 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32654step0 = (fun i j => raw32654 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32654step0 raw32654; decide +kernel
      have hl : raw32654step0Labels = raw32654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32654 raw32654Labels permutation346 hz
    mixedMoment B raw32654step0 raw32654step0Labels = mixedMoment B raw32654step1 raw32654step1Labels := by
      have ha : raw32654step1 = (fun i j => raw32654step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32654step1 raw32654step0; decide +kernel
      have hl : raw32654step1Labels = raw32654step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32654step0 raw32654step0Labels permutation34 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw32655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32655Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32655step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32655 raw32655Labels = mixedMoment B node1097 node1097Labels := by
  calc
    mixedMoment B raw32655 raw32655Labels = mixedMoment B raw32655step0 raw32655step0Labels := by
      have ha : raw32655step0 = (fun i j => raw32655 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32655step0 raw32655; decide +kernel
      have hl : raw32655step0Labels = raw32655Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32655 raw32655Labels permutation164 permutation3
    _ = mixedMoment B node1097 node1097Labels := by rfl

def raw32656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32656Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32656step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32656 raw32656Labels = mixedMoment B node2791 node2791Labels := by
  calc
    mixedMoment B raw32656 raw32656Labels = mixedMoment B raw32656step0 raw32656step0Labels := by
      have ha : raw32656step0 = (fun i j => raw32656 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32656step0 raw32656; decide +kernel
      have hl : raw32656step0Labels = raw32656Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32656 raw32656Labels permutation164 permutation3
    _ = mixedMoment B node2791 node2791Labels := by rfl

def raw32657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32657Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32657step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32657 raw32657Labels = mixedMoment B node2853 node2853Labels := by
  calc
    mixedMoment B raw32657 raw32657Labels = mixedMoment B raw32657step0 raw32657step0Labels := by
      have ha : raw32657step0 = (fun i j => raw32657 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32657step0 raw32657; decide +kernel
      have hl : raw32657step0Labels = raw32657Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32657 raw32657Labels permutation164 permutation3
    _ = mixedMoment B node2853 node2853Labels := by rfl

def raw32658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw32658Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32658step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32658 raw32658Labels = mixedMoment B node2880 node2880Labels := by
  calc
    mixedMoment B raw32658 raw32658Labels = mixedMoment B raw32658step0 raw32658step0Labels := by
      have ha : raw32658step0 = (fun i j => raw32658 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32658step0 raw32658; decide +kernel
      have hl : raw32658step0Labels = raw32658Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32658 raw32658Labels permutation164 permutation3
    _ = mixedMoment B node2880 node2880Labels := by rfl

def raw32659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32659Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32659step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32659step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw32659step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32659 raw32659Labels = mixedMoment B node1099 node1099Labels := by
  calc
    mixedMoment B raw32659 raw32659Labels = mixedMoment B raw32659step0 raw32659step0Labels := by
      have hz : ∀ j, raw32659 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32659step0 = (fun i j => raw32659 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32659step0 raw32659; decide +kernel
      have hl : raw32659step0Labels = raw32659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32659 raw32659Labels permutation346 hz
    mixedMoment B raw32659step0 raw32659step0Labels = mixedMoment B raw32659step1 raw32659step1Labels := by
      have ha : raw32659step1 = (fun i j => raw32659step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32659step1 raw32659step0; decide +kernel
      have hl : raw32659step1Labels = raw32659step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32659step0 raw32659step0Labels permutation34 permutation3
    _ = mixedMoment B node1099 node1099Labels := by rfl

def raw32660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32660Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32660step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw32660step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32660 raw32660Labels = mixedMoment B node2792 node2792Labels := by
  calc
    mixedMoment B raw32660 raw32660Labels = mixedMoment B raw32660step0 raw32660step0Labels := by
      have hz : ∀ j, raw32660 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32660step0 = (fun i j => raw32660 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32660step0 raw32660; decide +kernel
      have hl : raw32660step0Labels = raw32660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32660 raw32660Labels permutation346 hz
    mixedMoment B raw32660step0 raw32660step0Labels = mixedMoment B raw32660step1 raw32660step1Labels := by
      have ha : raw32660step1 = (fun i j => raw32660step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32660step1 raw32660step0; decide +kernel
      have hl : raw32660step1Labels = raw32660step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32660step0 raw32660step0Labels permutation34 permutation3
    _ = mixedMoment B node2792 node2792Labels := by rfl

def raw32661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32661Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32661step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw32661step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32661 raw32661Labels = mixedMoment B node2844 node2844Labels := by
  calc
    mixedMoment B raw32661 raw32661Labels = mixedMoment B raw32661step0 raw32661step0Labels := by
      have ha : raw32661step0 = (fun i j => raw32661 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32661step0 raw32661; decide +kernel
      have hl : raw32661step0Labels = raw32661Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32661 raw32661Labels permutation154 permutation3
    _ = mixedMoment B node2844 node2844Labels := by rfl

def raw32662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32662Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32662step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw32662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32662 raw32662Labels = mixedMoment B node2856 node2856Labels := by
  calc
    mixedMoment B raw32662 raw32662Labels = mixedMoment B raw32662step0 raw32662step0Labels := by
      have hz : ∀ j, raw32662 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32662step0 = (fun i j => raw32662 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32662step0 raw32662; decide +kernel
      have hl : raw32662step0Labels = raw32662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32662 raw32662Labels permutation346 hz
    mixedMoment B raw32662step0 raw32662step0Labels = mixedMoment B raw32662step1 raw32662step1Labels := by
      have ha : raw32662step1 = (fun i j => raw32662step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32662step1 raw32662step0; decide +kernel
      have hl : raw32662step1Labels = raw32662step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32662step0 raw32662step0Labels permutation34 permutation3
    _ = mixedMoment B node2856 node2856Labels := by rfl

def raw32663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, -1, 0]]
def raw32663Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1], ![1, -1, 0]]
def raw32663step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32663step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32663 raw32663Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw32663 raw32663Labels = mixedMoment B raw32663step0 raw32663step0Labels := by
      have hz : ∀ j, raw32663 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32663step0 = (fun i j => raw32663 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32663step0 raw32663; decide +kernel
      have hl : raw32663step0Labels = raw32663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32663 raw32663Labels permutation346 hz
    mixedMoment B raw32663step0 raw32663step0Labels = mixedMoment B raw32663step1 raw32663step1Labels := by
      have ha : raw32663step1 = (fun i j => raw32663step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32663step1 raw32663step0; decide +kernel
      have hl : raw32663step1Labels = raw32663step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32663step0 raw32663step0Labels permutation35 permutation3
    _ = mixedMoment B node2881 node2881Labels := by rfl

def raw32664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw32664Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw32664step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32664step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32664 raw32664Labels = mixedMoment B node1102 node1102Labels := by
  calc
    mixedMoment B raw32664 raw32664Labels = mixedMoment B raw32664step0 raw32664step0Labels := by
      have hz : ∀ j, raw32664 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32664step0 = (fun i j => raw32664 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32664step0 raw32664; decide +kernel
      have hl : raw32664step0Labels = raw32664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32664 raw32664Labels permutation346 hz
    mixedMoment B raw32664step0 raw32664step0Labels = mixedMoment B raw32664step1 raw32664step1Labels := by
      have ha : raw32664step1 = (fun i j => raw32664step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32664step1 raw32664step0; decide +kernel
      have hl : raw32664step1Labels = raw32664step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32664step0 raw32664step0Labels permutation32 permutation3
    _ = mixedMoment B node1102 node1102Labels := by rfl

def raw32665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw32665Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw32665step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32665step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32665 raw32665Labels = mixedMoment B node2794 node2794Labels := by
  calc
    mixedMoment B raw32665 raw32665Labels = mixedMoment B raw32665step0 raw32665step0Labels := by
      have hz : ∀ j, raw32665 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32665step0 = (fun i j => raw32665 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32665step0 raw32665; decide +kernel
      have hl : raw32665step0Labels = raw32665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32665 raw32665Labels permutation346 hz
    mixedMoment B raw32665step0 raw32665step0Labels = mixedMoment B raw32665step1 raw32665step1Labels := by
      have ha : raw32665step1 = (fun i j => raw32665step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32665step1 raw32665step0; decide +kernel
      have hl : raw32665step1Labels = raw32665step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32665step0 raw32665step0Labels permutation32 permutation3
    _ = mixedMoment B node2794 node2794Labels := by rfl

def raw32666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw32666Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32666step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32666 raw32666Labels = mixedMoment B node2845 node2845Labels := by
  calc
    mixedMoment B raw32666 raw32666Labels = mixedMoment B raw32666step0 raw32666step0Labels := by
      have ha : raw32666step0 = (fun i j => raw32666 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32666step0 raw32666; decide +kernel
      have hl : raw32666step0Labels = raw32666Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32666 raw32666Labels permutation152 permutation3
    _ = mixedMoment B node2845 node2845Labels := by rfl

def raw32667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw32667Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw32667step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32667step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32667 raw32667Labels = mixedMoment B node2884 node2884Labels := by
  calc
    mixedMoment B raw32667 raw32667Labels = mixedMoment B raw32667step0 raw32667step0Labels := by
      have hz : ∀ j, raw32667 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32667step0 = (fun i j => raw32667 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32667step0 raw32667; decide +kernel
      have hl : raw32667step0Labels = raw32667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32667 raw32667Labels permutation346 hz
    mixedMoment B raw32667step0 raw32667step0Labels = mixedMoment B raw32667step1 raw32667step1Labels := by
      have ha : raw32667step1 = (fun i j => raw32667step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32667step1 raw32667step0; decide +kernel
      have hl : raw32667step1Labels = raw32667step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32667step0 raw32667step0Labels permutation33 permutation3
    _ = mixedMoment B node2884 node2884Labels := by rfl

def raw32668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw32668Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw32668step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32668step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw32668step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32668step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw32668step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32668step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw32668step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32668 raw32668Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw32668 raw32668Labels = mixedMoment B raw32668step0 raw32668step0Labels := by
      have hz : ∀ j, raw32668 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32668step0 = (fun i j => raw32668 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32668step0 raw32668; decide +kernel
      have hl : raw32668step0Labels = raw32668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32668 raw32668Labels permutation434 hz
    mixedMoment B raw32668step0 raw32668step0Labels = mixedMoment B raw32668step1 raw32668step1Labels := by
      have hz : ∀ j, raw32668step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32668step1 = (fun i j => raw32668step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32668step1 raw32668step0; decide +kernel
      have hl : raw32668step1Labels = raw32668step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32668step0 raw32668step0Labels permutation80 hz
    mixedMoment B raw32668step1 raw32668step1Labels = mixedMoment B raw32668step2 raw32668step2Labels := by
      have ha : raw32668step2 = (fun i j => raw32668step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32668step2 raw32668step1; decide +kernel
      have hl : raw32668step2Labels = raw32668step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32668step1 raw32668step1Labels permutation31 permutation3
    mixedMoment B raw32668step2 raw32668step2Labels = mixedMoment B raw32668step3 raw32668step3Labels := by
      have ha : raw32668step3 = -raw32668step2 := by apply Matrix.ext; change ∀ i j, raw32668step3 i j = -(raw32668step2 i j); unfold raw32668step3 raw32668step2; decide +kernel
      have hl : raw32668step3Labels = raw32668step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2062 node2062Labels := by rfl

def raw32669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32669step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32669 raw32669Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw32669 raw32669Labels = mixedMoment B raw32669step0 raw32669step0Labels := by
      have hz : ∀ j, raw32669 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32669step0 = (fun i j => raw32669 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32669step0 raw32669; decide +kernel
      have hl : raw32669step0Labels = raw32669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32669 raw32669Labels permutation346 hz
    mixedMoment B raw32669step0 raw32669step0Labels = mixedMoment B raw32669step1 raw32669step1Labels := by
      have ha : raw32669step1 = (fun i j => raw32669step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32669step1 raw32669step0; decide +kernel
      have hl : raw32669step1Labels = raw32669step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32669step0 raw32669step0Labels permutation58 permutation2
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw32670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw32670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32670step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32670step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32670 raw32670Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw32670 raw32670Labels = mixedMoment B raw32670step0 raw32670step0Labels := by
      have ha : raw32670step0 = (fun i j => raw32670 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32670step0 raw32670; decide +kernel
      have hl : raw32670step0Labels = raw32670Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32670 raw32670Labels permutation664 permutation2
    mixedMoment B raw32670step0 raw32670step0Labels = mixedMoment B raw32670step1 raw32670step1Labels := by
      have ha : raw32670step1 = -raw32670step0 := by apply Matrix.ext; change ∀ i j, raw32670step1 i j = -(raw32670step0 i j); unfold raw32670step1 raw32670step0; decide +kernel
      have hl : raw32670step1Labels = raw32670step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw32671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw32671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32671step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32671step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32671 raw32671Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw32671 raw32671Labels = mixedMoment B raw32671step0 raw32671step0Labels := by
      have hz : ∀ j, raw32671 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32671step0 = (fun i j => raw32671 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32671step0 raw32671; decide +kernel
      have hl : raw32671step0Labels = raw32671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32671 raw32671Labels permutation346 hz
    mixedMoment B raw32671step0 raw32671step0Labels = mixedMoment B raw32671step1 raw32671step1Labels := by
      have ha : raw32671step1 = (fun i j => raw32671step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32671step1 raw32671step0; decide +kernel
      have hl : raw32671step1Labels = raw32671step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32671step0 raw32671step0Labels permutation151 permutation2
    mixedMoment B raw32671step1 raw32671step1Labels = mixedMoment B raw32671step2 raw32671step2Labels := by
      have ha : raw32671step2 = -raw32671step1 := by apply Matrix.ext; change ∀ i j, raw32671step2 i j = -(raw32671step1 i j); unfold raw32671step2 raw32671step1; decide +kernel
      have hl : raw32671step2Labels = raw32671step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw32672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32672step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw32672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32672step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw32672step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32672step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32672step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32672 raw32672Labels = mixedMoment B node5413 node5413Labels := by
  calc
    mixedMoment B raw32672 raw32672Labels = mixedMoment B raw32672step0 raw32672step0Labels := by
      have hz : ∀ j, raw32672 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32672step0 = (fun i j => raw32672 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32672step0 raw32672; decide +kernel
      have hl : raw32672step0Labels = raw32672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32672 raw32672Labels permutation520 hz
    mixedMoment B raw32672step0 raw32672step0Labels = mixedMoment B raw32672step1 raw32672step1Labels := by
      have hz : ∀ j, raw32672step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32672step1 = (fun i j => raw32672step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32672step1 raw32672step0; decide +kernel
      have hl : raw32672step1Labels = raw32672step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32672step0 raw32672step0Labels permutation80 hz
    mixedMoment B raw32672step1 raw32672step1Labels = mixedMoment B raw32672step2 raw32672step2Labels := by
      have ha : raw32672step2 = (fun i j => raw32672step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32672step2 raw32672step1; decide +kernel
      have hl : raw32672step2Labels = raw32672step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32672step1 raw32672step1Labels permutation31 permutation2
    mixedMoment B raw32672step2 raw32672step2Labels = mixedMoment B raw32672step3 raw32672step3Labels := by
      have ha : raw32672step3 = -raw32672step2 := by apply Matrix.ext; change ∀ i j, raw32672step3 i j = -(raw32672step2 i j); unfold raw32672step3 raw32672step2; decide +kernel
      have hl : raw32672step3Labels = raw32672step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5413 node5413Labels := by rfl

def raw32673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32673step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32673step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32673step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32673step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32673step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32673 raw32673Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw32673 raw32673Labels = mixedMoment B raw32673step0 raw32673step0Labels := by
      have hz : ∀ j, raw32673 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32673step0 = (fun i j => raw32673 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32673step0 raw32673; decide +kernel
      have hl : raw32673step0Labels = raw32673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32673 raw32673Labels permutation346 hz
    mixedMoment B raw32673step0 raw32673step0Labels = mixedMoment B raw32673step1 raw32673step1Labels := by
      have ha : raw32673step1 = (fun i j => raw32673step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32673step1 raw32673step0; decide +kernel
      have hl : raw32673step1Labels = raw32673step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32673step0 raw32673step0Labels permutation58 permutation7
    mixedMoment B raw32673step1 raw32673step1Labels = mixedMoment B raw32673step2 raw32673step2Labels := by
      have ha : raw32673step2 = -raw32673step1 := by apply Matrix.ext; change ∀ i j, raw32673step2 i j = -(raw32673step1 i j); unfold raw32673step2 raw32673step1; decide +kernel
      have hl : raw32673step2Labels = raw32673step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32673step2 raw32673step2Labels = mixedMoment B raw32673step3 raw32673step3Labels := by
      have ha : raw32673step3 = raw32673step2 := by apply Matrix.ext; unfold raw32673step3 raw32673step2; decide +kernel
      have hl : raw32673step2Labels = labelEmbedding10 ∘ raw32673step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32673step2 raw32673step2Labels raw32673step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw32674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32674step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32674step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32674step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32674 raw32674Labels = mixedMoment B node4475 node4475Labels := by
  calc
    mixedMoment B raw32674 raw32674Labels = mixedMoment B raw32674step0 raw32674step0Labels := by
      have hz : ∀ j, raw32674 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32674step0 = (fun i j => raw32674 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32674step0 raw32674; decide +kernel
      have hl : raw32674step0Labels = raw32674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32674 raw32674Labels permutation346 hz
    mixedMoment B raw32674step0 raw32674step0Labels = mixedMoment B raw32674step1 raw32674step1Labels := by
      have ha : raw32674step1 = (fun i j => raw32674step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32674step1 raw32674step0; decide +kernel
      have hl : raw32674step1Labels = raw32674step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32674step0 raw32674step0Labels permutation32 permutation3
    mixedMoment B raw32674step1 raw32674step1Labels = mixedMoment B raw32674step2 raw32674step2Labels := by
      have ha : raw32674step2 = raw32674step1 := by apply Matrix.ext; unfold raw32674step2 raw32674step1; decide +kernel
      have hl : raw32674step1Labels = labelEmbedding6 ∘ raw32674step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32674step1 raw32674step1Labels raw32674step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4475 node4475Labels := by rfl

def raw32675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32675step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32675step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32675step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32675 raw32675Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw32675 raw32675Labels = mixedMoment B raw32675step0 raw32675step0Labels := by
      have ha : raw32675step0 = (fun i j => raw32675 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32675step0 raw32675; decide +kernel
      have hl : raw32675step0Labels = raw32675Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32675 raw32675Labels permutation176 permutation3
    mixedMoment B raw32675step0 raw32675step0Labels = mixedMoment B raw32675step1 raw32675step1Labels := by
      have ha : raw32675step1 = raw32675step0 := by apply Matrix.ext; unfold raw32675step1 raw32675step0; decide +kernel
      have hl : raw32675step0Labels = labelEmbedding6 ∘ raw32675step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32675step0 raw32675step0Labels raw32675step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5086 node5086Labels := by rfl

def raw32676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32676step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32676step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32676step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32676 raw32676Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw32676 raw32676Labels = mixedMoment B raw32676step0 raw32676step0Labels := by
      have hz : ∀ j, raw32676 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32676step0 = (fun i j => raw32676 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32676step0 raw32676; decide +kernel
      have hl : raw32676step0Labels = raw32676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32676 raw32676Labels permutation346 hz
    mixedMoment B raw32676step0 raw32676step0Labels = mixedMoment B raw32676step1 raw32676step1Labels := by
      have ha : raw32676step1 = (fun i j => raw32676step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32676step1 raw32676step0; decide +kernel
      have hl : raw32676step1Labels = raw32676step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32676step0 raw32676step0Labels permutation38 permutation3
    mixedMoment B raw32676step1 raw32676step1Labels = mixedMoment B raw32676step2 raw32676step2Labels := by
      have ha : raw32676step2 = raw32676step1 := by apply Matrix.ext; unfold raw32676step2 raw32676step1; decide +kernel
      have hl : raw32676step1Labels = labelEmbedding6 ∘ raw32676step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32676step1 raw32676step1Labels raw32676step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw32677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32677step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw32677step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32677step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw32677step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32677step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw32677step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32677 raw32677Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw32677 raw32677Labels = mixedMoment B raw32677step0 raw32677step0Labels := by
      have hz : ∀ j, raw32677 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32677step0 = (fun i j => raw32677 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32677step0 raw32677; decide +kernel
      have hl : raw32677step0Labels = raw32677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32677 raw32677Labels permutation520 hz
    mixedMoment B raw32677step0 raw32677step0Labels = mixedMoment B raw32677step1 raw32677step1Labels := by
      have hz : ∀ j, raw32677step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32677step1 = (fun i j => raw32677step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32677step1 raw32677step0; decide +kernel
      have hl : raw32677step1Labels = raw32677step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32677step0 raw32677step0Labels permutation80 hz
    mixedMoment B raw32677step1 raw32677step1Labels = mixedMoment B raw32677step2 raw32677step2Labels := by
      have ha : raw32677step2 = (fun i j => raw32677step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32677step2 raw32677step1; decide +kernel
      have hl : raw32677step2Labels = raw32677step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32677step1 raw32677step1Labels permutation8 permutation3
    mixedMoment B raw32677step2 raw32677step2Labels = mixedMoment B raw32677step3 raw32677step3Labels := by
      have ha : raw32677step3 = raw32677step2 := by apply Matrix.ext; unfold raw32677step3 raw32677step2; decide +kernel
      have hl : raw32677step2Labels = labelEmbedding6 ∘ raw32677step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32677step2 raw32677step2Labels raw32677step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw32678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw32678step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32678step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw32678step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32678 raw32678Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw32678 raw32678Labels = mixedMoment B raw32678step0 raw32678step0Labels := by
      have hz : ∀ j, raw32678 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32678step0 = (fun i j => raw32678 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32678step0 raw32678; decide +kernel
      have hl : raw32678step0Labels = raw32678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32678 raw32678Labels permutation346 hz
    mixedMoment B raw32678step0 raw32678step0Labels = mixedMoment B raw32678step1 raw32678step1Labels := by
      have ha : raw32678step1 = (fun i j => raw32678step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32678step1 raw32678step0; decide +kernel
      have hl : raw32678step1Labels = raw32678step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32678step0 raw32678step0Labels permutation36 permutation3
    mixedMoment B raw32678step1 raw32678step1Labels = mixedMoment B raw32678step2 raw32678step2Labels := by
      have ha : raw32678step2 = raw32678step1 := by apply Matrix.ext; unfold raw32678step2 raw32678step1; decide +kernel
      have hl : raw32678step1Labels = labelEmbedding6 ∘ raw32678step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32678step1 raw32678step1Labels raw32678step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw32679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32679step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32679step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32679step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32679 raw32679Labels = mixedMoment B node4366 node4366Labels := by
  calc
    mixedMoment B raw32679 raw32679Labels = mixedMoment B raw32679step0 raw32679step0Labels := by
      have ha : raw32679step0 = (fun i j => raw32679 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32679step0 raw32679; decide +kernel
      have hl : raw32679step0Labels = raw32679Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32679 raw32679Labels permutation158 permutation3
    mixedMoment B raw32679step0 raw32679step0Labels = mixedMoment B raw32679step1 raw32679step1Labels := by
      have ha : raw32679step1 = raw32679step0 := by apply Matrix.ext; unfold raw32679step1 raw32679step0; decide +kernel
      have hl : raw32679step0Labels = labelEmbedding6 ∘ raw32679step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32679step0 raw32679step0Labels raw32679step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4366 node4366Labels := by rfl

def raw32680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32680step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32680step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32680step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32680step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32680 raw32680Labels = mixedMoment B node4971 node4971Labels := by
  calc
    mixedMoment B raw32680 raw32680Labels = mixedMoment B raw32680step0 raw32680step0Labels := by
      have ha : raw32680step0 = (fun i j => raw32680 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32680step0 raw32680; decide +kernel
      have hl : raw32680step0Labels = raw32680Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32680 raw32680Labels permutation158 permutation3
    mixedMoment B raw32680step0 raw32680step0Labels = mixedMoment B raw32680step1 raw32680step1Labels := by
      have ha : raw32680step1 = raw32680step0 := by apply Matrix.ext; unfold raw32680step1 raw32680step0; decide +kernel
      have hl : raw32680step0Labels = labelEmbedding6 ∘ raw32680step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32680step0 raw32680step0Labels raw32680step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4971 node4971Labels := by rfl

def raw32681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32681step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32681step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32681step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32681 raw32681Labels = mixedMoment B node5187 node5187Labels := by
  calc
    mixedMoment B raw32681 raw32681Labels = mixedMoment B raw32681step0 raw32681step0Labels := by
      have ha : raw32681step0 = (fun i j => raw32681 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32681step0 raw32681; decide +kernel
      have hl : raw32681step0Labels = raw32681Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32681 raw32681Labels permutation158 permutation3
    mixedMoment B raw32681step0 raw32681step0Labels = mixedMoment B raw32681step1 raw32681step1Labels := by
      have ha : raw32681step1 = raw32681step0 := by apply Matrix.ext; unfold raw32681step1 raw32681step0; decide +kernel
      have hl : raw32681step0Labels = labelEmbedding6 ∘ raw32681step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32681step0 raw32681step0Labels raw32681step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5187 node5187Labels := by rfl

def raw32682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32682step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32682step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32682 raw32682Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw32682 raw32682Labels = mixedMoment B raw32682step0 raw32682step0Labels := by
      have hz : ∀ j, raw32682 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32682step0 = (fun i j => raw32682 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32682step0 raw32682; decide +kernel
      have hl : raw32682step0Labels = raw32682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32682 raw32682Labels permutation520 hz
    mixedMoment B raw32682step0 raw32682step0Labels = mixedMoment B raw32682step1 raw32682step1Labels := by
      have ha : raw32682step1 = (fun i j => raw32682step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32682step1 raw32682step0; decide +kernel
      have hl : raw32682step1Labels = raw32682step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32682step0 raw32682step0Labels permutation34 permutation3
    mixedMoment B raw32682step1 raw32682step1Labels = mixedMoment B raw32682step2 raw32682step2Labels := by
      have ha : raw32682step2 = raw32682step1 := by apply Matrix.ext; unfold raw32682step2 raw32682step1; decide +kernel
      have hl : raw32682step1Labels = labelEmbedding6 ∘ raw32682step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32682step1 raw32682step1Labels raw32682step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw32683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32683step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32683step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32683 raw32683Labels = mixedMoment B node5197 node5197Labels := by
  calc
    mixedMoment B raw32683 raw32683Labels = mixedMoment B raw32683step0 raw32683step0Labels := by
      have ha : raw32683step0 = (fun i j => raw32683 (permutation172 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32683step0 raw32683; decide +kernel
      have hl : raw32683step0Labels = raw32683Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32683 raw32683Labels permutation172 permutation3
    mixedMoment B raw32683step0 raw32683step0Labels = mixedMoment B raw32683step1 raw32683step1Labels := by
      have ha : raw32683step1 = raw32683step0 := by apply Matrix.ext; unfold raw32683step1 raw32683step0; decide +kernel
      have hl : raw32683step0Labels = labelEmbedding6 ∘ raw32683step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32683step0 raw32683step0Labels raw32683step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5197 node5197Labels := by rfl

def raw32684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32684step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32684step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32684step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32684step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32684 raw32684Labels = mixedMoment B node4372 node4372Labels := by
  calc
    mixedMoment B raw32684 raw32684Labels = mixedMoment B raw32684step0 raw32684step0Labels := by
      have hz : ∀ j, raw32684 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32684step0 = (fun i j => raw32684 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32684step0 raw32684; decide +kernel
      have hl : raw32684step0Labels = raw32684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32684 raw32684Labels permutation346 hz
    mixedMoment B raw32684step0 raw32684step0Labels = mixedMoment B raw32684step1 raw32684step1Labels := by
      have ha : raw32684step1 = (fun i j => raw32684step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32684step1 raw32684step0; decide +kernel
      have hl : raw32684step1Labels = raw32684step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32684step0 raw32684step0Labels permutation35 permutation3
    mixedMoment B raw32684step1 raw32684step1Labels = mixedMoment B raw32684step2 raw32684step2Labels := by
      have ha : raw32684step2 = raw32684step1 := by apply Matrix.ext; unfold raw32684step2 raw32684step1; decide +kernel
      have hl : raw32684step1Labels = labelEmbedding6 ∘ raw32684step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32684step1 raw32684step1Labels raw32684step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4372 node4372Labels := by rfl

def raw32685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32685step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32685step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32685 raw32685Labels = mixedMoment B node4977 node4977Labels := by
  calc
    mixedMoment B raw32685 raw32685Labels = mixedMoment B raw32685step0 raw32685step0Labels := by
      have hz : ∀ j, raw32685 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32685step0 = (fun i j => raw32685 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32685step0 raw32685; decide +kernel
      have hl : raw32685step0Labels = raw32685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32685 raw32685Labels permutation346 hz
    mixedMoment B raw32685step0 raw32685step0Labels = mixedMoment B raw32685step1 raw32685step1Labels := by
      have ha : raw32685step1 = (fun i j => raw32685step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32685step1 raw32685step0; decide +kernel
      have hl : raw32685step1Labels = raw32685step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32685step0 raw32685step0Labels permutation35 permutation3
    mixedMoment B raw32685step1 raw32685step1Labels = mixedMoment B raw32685step2 raw32685step2Labels := by
      have ha : raw32685step2 = raw32685step1 := by apply Matrix.ext; unfold raw32685step2 raw32685step1; decide +kernel
      have hl : raw32685step1Labels = labelEmbedding6 ∘ raw32685step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32685step1 raw32685step1Labels raw32685step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4977 node4977Labels := by rfl

def raw32686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32686step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32686step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32686step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32686 raw32686Labels = mixedMoment B node5044 node5044Labels := by
  calc
    mixedMoment B raw32686 raw32686Labels = mixedMoment B raw32686step0 raw32686step0Labels := by
      have ha : raw32686step0 = (fun i j => raw32686 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32686step0 raw32686; decide +kernel
      have hl : raw32686step0Labels = raw32686Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32686 raw32686Labels permutation179 permutation3
    mixedMoment B raw32686step0 raw32686step0Labels = mixedMoment B raw32686step1 raw32686step1Labels := by
      have ha : raw32686step1 = raw32686step0 := by apply Matrix.ext; unfold raw32686step1 raw32686step0; decide +kernel
      have hl : raw32686step0Labels = labelEmbedding6 ∘ raw32686step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32686step0 raw32686step0Labels raw32686step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5044 node5044Labels := by rfl

def raw32687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32687step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw32687step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32687step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32687step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32687step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32687step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32687 raw32687Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw32687 raw32687Labels = mixedMoment B raw32687step0 raw32687step0Labels := by
      have hz : ∀ j, raw32687 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32687step0 = (fun i j => raw32687 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32687step0 raw32687; decide +kernel
      have hl : raw32687step0Labels = raw32687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32687 raw32687Labels permutation520 hz
    mixedMoment B raw32687step0 raw32687step0Labels = mixedMoment B raw32687step1 raw32687step1Labels := by
      have hz : ∀ j, raw32687step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32687step1 = (fun i j => raw32687step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32687step1 raw32687step0; decide +kernel
      have hl : raw32687step1Labels = raw32687step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32687step0 raw32687step0Labels permutation80 hz
    mixedMoment B raw32687step1 raw32687step1Labels = mixedMoment B raw32687step2 raw32687step2Labels := by
      have ha : raw32687step2 = (fun i j => raw32687step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32687step2 raw32687step1; decide +kernel
      have hl : raw32687step2Labels = raw32687step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32687step1 raw32687step1Labels permutation9 permutation3
    mixedMoment B raw32687step2 raw32687step2Labels = mixedMoment B raw32687step3 raw32687step3Labels := by
      have ha : raw32687step3 = raw32687step2 := by apply Matrix.ext; unfold raw32687step3 raw32687step2; decide +kernel
      have hl : raw32687step2Labels = labelEmbedding6 ∘ raw32687step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32687step2 raw32687step2Labels raw32687step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5207 node5207Labels := by rfl

def raw32688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32688step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32688step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32688step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32688 raw32688Labels = mixedMoment B node5199 node5199Labels := by
  calc
    mixedMoment B raw32688 raw32688Labels = mixedMoment B raw32688step0 raw32688step0Labels := by
      have hz : ∀ j, raw32688 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32688step0 = (fun i j => raw32688 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32688step0 raw32688; decide +kernel
      have hl : raw32688step0Labels = raw32688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32688 raw32688Labels permutation346 hz
    mixedMoment B raw32688step0 raw32688step0Labels = mixedMoment B raw32688step1 raw32688step1Labels := by
      have ha : raw32688step1 = (fun i j => raw32688step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32688step1 raw32688step0; decide +kernel
      have hl : raw32688step1Labels = raw32688step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32688step0 raw32688step0Labels permutation37 permutation3
    mixedMoment B raw32688step1 raw32688step1Labels = mixedMoment B raw32688step2 raw32688step2Labels := by
      have ha : raw32688step2 = raw32688step1 := by apply Matrix.ext; unfold raw32688step2 raw32688step1; decide +kernel
      have hl : raw32688step1Labels = labelEmbedding6 ∘ raw32688step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32688step1 raw32688step1Labels raw32688step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5199 node5199Labels := by rfl

def raw32689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32689step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32689step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32689step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32689 raw32689Labels = mixedMoment B node4368 node4368Labels := by
  calc
    mixedMoment B raw32689 raw32689Labels = mixedMoment B raw32689step0 raw32689step0Labels := by
      have hz : ∀ j, raw32689 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32689step0 = (fun i j => raw32689 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32689step0 raw32689; decide +kernel
      have hl : raw32689step0Labels = raw32689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32689 raw32689Labels permutation346 hz
    mixedMoment B raw32689step0 raw32689step0Labels = mixedMoment B raw32689step1 raw32689step1Labels := by
      have ha : raw32689step1 = (fun i j => raw32689step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32689step1 raw32689step0; decide +kernel
      have hl : raw32689step1Labels = raw32689step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32689step0 raw32689step0Labels permutation33 permutation3
    mixedMoment B raw32689step1 raw32689step1Labels = mixedMoment B raw32689step2 raw32689step2Labels := by
      have ha : raw32689step2 = raw32689step1 := by apply Matrix.ext; unfold raw32689step2 raw32689step1; decide +kernel
      have hl : raw32689step1Labels = labelEmbedding6 ∘ raw32689step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32689step1 raw32689step1Labels raw32689step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4368 node4368Labels := by rfl

def raw32690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32690step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32690step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32690step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32690 raw32690Labels = mixedMoment B node4973 node4973Labels := by
  calc
    mixedMoment B raw32690 raw32690Labels = mixedMoment B raw32690step0 raw32690step0Labels := by
      have hz : ∀ j, raw32690 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32690step0 = (fun i j => raw32690 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32690step0 raw32690; decide +kernel
      have hl : raw32690step0Labels = raw32690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32690 raw32690Labels permutation346 hz
    mixedMoment B raw32690step0 raw32690step0Labels = mixedMoment B raw32690step1 raw32690step1Labels := by
      have ha : raw32690step1 = (fun i j => raw32690step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32690step1 raw32690step0; decide +kernel
      have hl : raw32690step1Labels = raw32690step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32690step0 raw32690step0Labels permutation33 permutation3
    mixedMoment B raw32690step1 raw32690step1Labels = mixedMoment B raw32690step2 raw32690step2Labels := by
      have ha : raw32690step2 = raw32690step1 := by apply Matrix.ext; unfold raw32690step2 raw32690step1; decide +kernel
      have hl : raw32690step1Labels = labelEmbedding6 ∘ raw32690step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32690step1 raw32690step1Labels raw32690step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4973 node4973Labels := by rfl

def raw32691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32691step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32691step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32691step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32691 raw32691Labels = mixedMoment B node5042 node5042Labels := by
  calc
    mixedMoment B raw32691 raw32691Labels = mixedMoment B raw32691step0 raw32691step0Labels := by
      have ha : raw32691step0 = (fun i j => raw32691 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32691step0 raw32691; decide +kernel
      have hl : raw32691step0Labels = raw32691Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32691 raw32691Labels permutation177 permutation3
    mixedMoment B raw32691step0 raw32691step0Labels = mixedMoment B raw32691step1 raw32691step1Labels := by
      have ha : raw32691step1 = raw32691step0 := by apply Matrix.ext; unfold raw32691step1 raw32691step0; decide +kernel
      have hl : raw32691step0Labels = labelEmbedding6 ∘ raw32691step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32691step0 raw32691step0Labels raw32691step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5042 node5042Labels := by rfl

def raw32692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw32692step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32692step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw32692step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32692 raw32692Labels = mixedMoment B node5188 node5188Labels := by
  calc
    mixedMoment B raw32692 raw32692Labels = mixedMoment B raw32692step0 raw32692step0Labels := by
      have hz : ∀ j, raw32692 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32692step0 = (fun i j => raw32692 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32692step0 raw32692; decide +kernel
      have hl : raw32692step0Labels = raw32692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32692 raw32692Labels permutation346 hz
    mixedMoment B raw32692step0 raw32692step0Labels = mixedMoment B raw32692step1 raw32692step1Labels := by
      have ha : raw32692step1 = (fun i j => raw32692step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32692step1 raw32692step0; decide +kernel
      have hl : raw32692step1Labels = raw32692step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32692step0 raw32692step0Labels permutation33 permutation3
    mixedMoment B raw32692step1 raw32692step1Labels = mixedMoment B raw32692step2 raw32692step2Labels := by
      have ha : raw32692step2 = raw32692step1 := by apply Matrix.ext; unfold raw32692step2 raw32692step1; decide +kernel
      have hl : raw32692step1Labels = labelEmbedding6 ∘ raw32692step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32692step1 raw32692step1Labels raw32692step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5188 node5188Labels := by rfl

def raw32693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw32693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw32693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32693step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32693step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32693step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32693 raw32693Labels = mixedMoment B node5198 node5198Labels := by
  calc
    mixedMoment B raw32693 raw32693Labels = mixedMoment B raw32693step0 raw32693step0Labels := by
      have hz : ∀ j, raw32693 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32693step0 = (fun i j => raw32693 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32693step0 raw32693; decide +kernel
      have hl : raw32693step0Labels = raw32693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32693 raw32693Labels permutation346 hz
    mixedMoment B raw32693step0 raw32693step0Labels = mixedMoment B raw32693step1 raw32693step1Labels := by
      have ha : raw32693step1 = (fun i j => raw32693step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32693step1 raw32693step0; decide +kernel
      have hl : raw32693step1Labels = raw32693step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32693step0 raw32693step0Labels permutation36 permutation3
    mixedMoment B raw32693step1 raw32693step1Labels = mixedMoment B raw32693step2 raw32693step2Labels := by
      have ha : raw32693step2 = raw32693step1 := by apply Matrix.ext; unfold raw32693step2 raw32693step1; decide +kernel
      have hl : raw32693step1Labels = labelEmbedding6 ∘ raw32693step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32693step1 raw32693step1Labels raw32693step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5198 node5198Labels := by rfl

def raw32694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32694step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32694step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32694step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32694 raw32694Labels = mixedMoment B node4367 node4367Labels := by
  calc
    mixedMoment B raw32694 raw32694Labels = mixedMoment B raw32694step0 raw32694step0Labels := by
      have hz : ∀ j, raw32694 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32694step0 = (fun i j => raw32694 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32694step0 raw32694; decide +kernel
      have hl : raw32694step0Labels = raw32694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32694 raw32694Labels permutation346 hz
    mixedMoment B raw32694step0 raw32694step0Labels = mixedMoment B raw32694step1 raw32694step1Labels := by
      have ha : raw32694step1 = (fun i j => raw32694step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32694step1 raw32694step0; decide +kernel
      have hl : raw32694step1Labels = raw32694step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32694step0 raw32694step0Labels permutation32 permutation3
    mixedMoment B raw32694step1 raw32694step1Labels = mixedMoment B raw32694step2 raw32694step2Labels := by
      have ha : raw32694step2 = raw32694step1 := by apply Matrix.ext; unfold raw32694step2 raw32694step1; decide +kernel
      have hl : raw32694step1Labels = labelEmbedding6 ∘ raw32694step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32694step1 raw32694step1Labels raw32694step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4367 node4367Labels := by rfl

def raw32695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32695step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32695step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32695 raw32695Labels = mixedMoment B node4972 node4972Labels := by
  calc
    mixedMoment B raw32695 raw32695Labels = mixedMoment B raw32695step0 raw32695step0Labels := by
      have hz : ∀ j, raw32695 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32695step0 = (fun i j => raw32695 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32695step0 raw32695; decide +kernel
      have hl : raw32695step0Labels = raw32695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32695 raw32695Labels permutation346 hz
    mixedMoment B raw32695step0 raw32695step0Labels = mixedMoment B raw32695step1 raw32695step1Labels := by
      have ha : raw32695step1 = (fun i j => raw32695step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32695step1 raw32695step0; decide +kernel
      have hl : raw32695step1Labels = raw32695step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32695step0 raw32695step0Labels permutation32 permutation3
    mixedMoment B raw32695step1 raw32695step1Labels = mixedMoment B raw32695step2 raw32695step2Labels := by
      have ha : raw32695step2 = raw32695step1 := by apply Matrix.ext; unfold raw32695step2 raw32695step1; decide +kernel
      have hl : raw32695step1Labels = labelEmbedding6 ∘ raw32695step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32695step1 raw32695step1Labels raw32695step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4972 node4972Labels := by rfl

def raw32696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw32696step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32696step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw32696step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32696 raw32696Labels = mixedMoment B node5034 node5034Labels := by
  calc
    mixedMoment B raw32696 raw32696Labels = mixedMoment B raw32696step0 raw32696step0Labels := by
      have ha : raw32696step0 = (fun i j => raw32696 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32696step0 raw32696; decide +kernel
      have hl : raw32696step0Labels = raw32696Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32696 raw32696Labels permutation664 permutation2
    mixedMoment B raw32696step0 raw32696step0Labels = mixedMoment B raw32696step1 raw32696step1Labels := by
      have ha : raw32696step1 = -raw32696step0 := by apply Matrix.ext; change ∀ i j, raw32696step1 i j = -(raw32696step0 i j); unfold raw32696step1 raw32696step0; decide +kernel
      have hl : raw32696step1Labels = raw32696step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5034 node5034Labels := by rfl

def raw32697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw32697step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw32697step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32697 raw32697Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw32697 raw32697Labels = mixedMoment B raw32697step0 raw32697step0Labels := by
      have hz : ∀ j, raw32697 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32697step0 = (fun i j => raw32697 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32697step0 raw32697; decide +kernel
      have hl : raw32697step0Labels = raw32697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32697 raw32697Labels permutation346 hz
    mixedMoment B raw32697step0 raw32697step0Labels = mixedMoment B raw32697step1 raw32697step1Labels := by
      have ha : raw32697step1 = (fun i j => raw32697step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32697step1 raw32697step0; decide +kernel
      have hl : raw32697step1Labels = raw32697step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32697step0 raw32697step0Labels permutation151 permutation2
    mixedMoment B raw32697step1 raw32697step1Labels = mixedMoment B raw32697step2 raw32697step2Labels := by
      have ha : raw32697step2 = -raw32697step1 := by apply Matrix.ext; change ∀ i j, raw32697step2 i j = -(raw32697step1 i j); unfold raw32697step2 raw32697step1; decide +kernel
      have hl : raw32697step2Labels = raw32697step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5139 node5139Labels := by rfl

def raw32698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw32698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw32698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32698step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw32698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32698step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw32698step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32698step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw32698step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32698 raw32698Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw32698 raw32698Labels = mixedMoment B raw32698step0 raw32698step0Labels := by
      have hz : ∀ j, raw32698 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32698step0 = (fun i j => raw32698 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32698step0 raw32698; decide +kernel
      have hl : raw32698step0Labels = raw32698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32698 raw32698Labels permutation520 hz
    mixedMoment B raw32698step0 raw32698step0Labels = mixedMoment B raw32698step1 raw32698step1Labels := by
      have hz : ∀ j, raw32698step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32698step1 = (fun i j => raw32698step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32698step1 raw32698step0; decide +kernel
      have hl : raw32698step1Labels = raw32698step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32698step0 raw32698step0Labels permutation80 hz
    mixedMoment B raw32698step1 raw32698step1Labels = mixedMoment B raw32698step2 raw32698step2Labels := by
      have ha : raw32698step2 = (fun i j => raw32698step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32698step2 raw32698step1; decide +kernel
      have hl : raw32698step2Labels = raw32698step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32698step1 raw32698step1Labels permutation31 permutation2
    mixedMoment B raw32698step2 raw32698step2Labels = mixedMoment B raw32698step3 raw32698step3Labels := by
      have ha : raw32698step3 = -raw32698step2 := by apply Matrix.ext; change ∀ i j, raw32698step3 i j = -(raw32698step2 i j); unfold raw32698step3 raw32698step2; decide +kernel
      have hl : raw32698step3Labels = raw32698step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5109 node5109Labels := by rfl

def raw32699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32699Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32699step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32699step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32699step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32699step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32699step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32699 raw32699Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw32699 raw32699Labels = mixedMoment B raw32699step0 raw32699step0Labels := by
      have hz : ∀ j, raw32699 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32699step0 = (fun i j => raw32699 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32699step0 raw32699; decide +kernel
      have hl : raw32699step0Labels = raw32699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32699 raw32699Labels permutation346 hz
    mixedMoment B raw32699step0 raw32699step0Labels = mixedMoment B raw32699step1 raw32699step1Labels := by
      have ha : raw32699step1 = (fun i j => raw32699step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32699step1 raw32699step0; decide +kernel
      have hl : raw32699step1Labels = raw32699step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32699step0 raw32699step0Labels permutation58 permutation7
    mixedMoment B raw32699step1 raw32699step1Labels = mixedMoment B raw32699step2 raw32699step2Labels := by
      have ha : raw32699step2 = -raw32699step1 := by apply Matrix.ext; change ∀ i j, raw32699step2 i j = -(raw32699step1 i j); unfold raw32699step2 raw32699step1; decide +kernel
      have hl : raw32699step2Labels = raw32699step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32699step2 raw32699step2Labels = mixedMoment B raw32699step3 raw32699step3Labels := by
      have ha : raw32699step3 = raw32699step2 := by apply Matrix.ext; unfold raw32699step3 raw32699step2; decide +kernel
      have hl : raw32699step2Labels = labelEmbedding1 ∘ raw32699step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32699step2 raw32699step2Labels raw32699step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

def raw32700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32700Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32700step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32700step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32700step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32700 raw32700Labels = mixedMoment B node3794 node3794Labels := by
  calc
    mixedMoment B raw32700 raw32700Labels = mixedMoment B raw32700step0 raw32700step0Labels := by
      have ha : raw32700step0 = (fun i j => raw32700 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32700step0 raw32700; decide +kernel
      have hl : raw32700step0Labels = raw32700Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32700 raw32700Labels permutation663 permutation7
    mixedMoment B raw32700step0 raw32700step0Labels = mixedMoment B raw32700step1 raw32700step1Labels := by
      have ha : raw32700step1 = raw32700step0 := by apply Matrix.ext; unfold raw32700step1 raw32700step0; decide +kernel
      have hl : raw32700step0Labels = labelEmbedding1 ∘ raw32700step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32700step0 raw32700step0Labels raw32700step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3794 node3794Labels := by rfl

def raw32701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32701Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32701step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32701step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32701step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32701step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32701 raw32701Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw32701 raw32701Labels = mixedMoment B raw32701step0 raw32701step0Labels := by
      have hz : ∀ j, raw32701 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32701step0 = (fun i j => raw32701 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32701step0 raw32701; decide +kernel
      have hl : raw32701step0Labels = raw32701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32701 raw32701Labels permutation346 hz
    mixedMoment B raw32701step0 raw32701step0Labels = mixedMoment B raw32701step1 raw32701step1Labels := by
      have ha : raw32701step1 = (fun i j => raw32701step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32701step1 raw32701step0; decide +kernel
      have hl : raw32701step1Labels = raw32701step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32701step0 raw32701step0Labels permutation144 permutation7
    mixedMoment B raw32701step1 raw32701step1Labels = mixedMoment B raw32701step2 raw32701step2Labels := by
      have ha : raw32701step2 = raw32701step1 := by apply Matrix.ext; unfold raw32701step2 raw32701step1; decide +kernel
      have hl : raw32701step1Labels = labelEmbedding1 ∘ raw32701step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32701step1 raw32701step1Labels raw32701step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw32702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32702Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32702step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32702step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw32702step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32702step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32702step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32702step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32702step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32702 raw32702Labels = mixedMoment B node3817 node3817Labels := by
  calc
    mixedMoment B raw32702 raw32702Labels = mixedMoment B raw32702step0 raw32702step0Labels := by
      have hz : ∀ j, raw32702 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32702step0 = (fun i j => raw32702 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32702step0 raw32702; decide +kernel
      have hl : raw32702step0Labels = raw32702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32702 raw32702Labels permutation520 hz
    mixedMoment B raw32702step0 raw32702step0Labels = mixedMoment B raw32702step1 raw32702step1Labels := by
      have hz : ∀ j, raw32702step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32702step1 = (fun i j => raw32702step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32702step1 raw32702step0; decide +kernel
      have hl : raw32702step1Labels = raw32702step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32702step0 raw32702step0Labels permutation80 hz
    mixedMoment B raw32702step1 raw32702step1Labels = mixedMoment B raw32702step2 raw32702step2Labels := by
      have ha : raw32702step2 = (fun i j => raw32702step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32702step2 raw32702step1; decide +kernel
      have hl : raw32702step2Labels = raw32702step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32702step1 raw32702step1Labels permutation30 permutation7
    mixedMoment B raw32702step2 raw32702step2Labels = mixedMoment B raw32702step3 raw32702step3Labels := by
      have ha : raw32702step3 = raw32702step2 := by apply Matrix.ext; unfold raw32702step3 raw32702step2; decide +kernel
      have hl : raw32702step2Labels = labelEmbedding1 ∘ raw32702step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32702step2 raw32702step2Labels raw32702step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3817 node3817Labels := by rfl

def raw32703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32703Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32703step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32703step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32703step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32703step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32703step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32703 raw32703Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw32703 raw32703Labels = mixedMoment B raw32703step0 raw32703step0Labels := by
      have hz : ∀ j, raw32703 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32703step0 = (fun i j => raw32703 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32703step0 raw32703; decide +kernel
      have hl : raw32703step0Labels = raw32703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32703 raw32703Labels permutation346 hz
    mixedMoment B raw32703step0 raw32703step0Labels = mixedMoment B raw32703step1 raw32703step1Labels := by
      have ha : raw32703step1 = (fun i j => raw32703step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32703step1 raw32703step0; decide +kernel
      have hl : raw32703step1Labels = raw32703step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32703step0 raw32703step0Labels permutation58 permutation7
    mixedMoment B raw32703step1 raw32703step1Labels = mixedMoment B raw32703step2 raw32703step2Labels := by
      have ha : raw32703step2 = -raw32703step1 := by apply Matrix.ext; change ∀ i j, raw32703step2 i j = -(raw32703step1 i j); unfold raw32703step2 raw32703step1; decide +kernel
      have hl : raw32703step2Labels = raw32703step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32703step2 raw32703step2Labels = mixedMoment B raw32703step3 raw32703step3Labels := by
      have ha : raw32703step3 = raw32703step2 := by apply Matrix.ext; unfold raw32703step3 raw32703step2; decide +kernel
      have hl : raw32703step2Labels = labelEmbedding1 ∘ raw32703step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32703step2 raw32703step2Labels raw32703step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw32704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32704Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32704step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw32704step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32704step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32704step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32704step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32704step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32704 raw32704Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw32704 raw32704Labels = mixedMoment B raw32704step0 raw32704step0Labels := by
      have hz : ∀ j, raw32704 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32704step0 = (fun i j => raw32704 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32704step0 raw32704; decide +kernel
      have hl : raw32704step0Labels = raw32704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32704 raw32704Labels permutation346 hz
    mixedMoment B raw32704step0 raw32704step0Labels = mixedMoment B raw32704step1 raw32704step1Labels := by
      have ha : raw32704step1 = (fun i j => raw32704step0 (permutation43 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32704step1 raw32704step0; decide +kernel
      have hl : raw32704step1Labels = raw32704step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32704step0 raw32704step0Labels permutation43 permutation5
    mixedMoment B raw32704step1 raw32704step1Labels = mixedMoment B raw32704step2 raw32704step2Labels := by
      have ha : raw32704step2 = -raw32704step1 := by apply Matrix.ext; change ∀ i j, raw32704step2 i j = -(raw32704step1 i j); unfold raw32704step2 raw32704step1; decide +kernel
      have hl : raw32704step2Labels = raw32704step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32704step2 raw32704step2Labels = mixedMoment B raw32704step3 raw32704step3Labels := by
      have ha : raw32704step3 = raw32704step2 := by apply Matrix.ext; unfold raw32704step3 raw32704step2; decide +kernel
      have hl : raw32704step2Labels = labelEmbedding1 ∘ raw32704step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32704step2 raw32704step2Labels raw32704step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1715 node1715Labels := by rfl

def raw32705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32705Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw32705step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32705step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32705step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32705step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32705step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32705 raw32705Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw32705 raw32705Labels = mixedMoment B raw32705step0 raw32705step0Labels := by
      have ha : raw32705step0 = (fun i j => raw32705 (permutation187 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32705step0 raw32705; decide +kernel
      have hl : raw32705step0Labels = raw32705Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32705 raw32705Labels permutation187 permutation5
    mixedMoment B raw32705step0 raw32705step0Labels = mixedMoment B raw32705step1 raw32705step1Labels := by
      have ha : raw32705step1 = -raw32705step0 := by apply Matrix.ext; change ∀ i j, raw32705step1 i j = -(raw32705step0 i j); unfold raw32705step1 raw32705step0; decide +kernel
      have hl : raw32705step1Labels = raw32705step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32705step1 raw32705step1Labels = mixedMoment B raw32705step2 raw32705step2Labels := by
      have ha : raw32705step2 = raw32705step1 := by apply Matrix.ext; unfold raw32705step2 raw32705step1; decide +kernel
      have hl : raw32705step1Labels = labelEmbedding1 ∘ raw32705step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32705step1 raw32705step1Labels raw32705step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3464 node3464Labels := by rfl

def raw32706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32706Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32706step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw32706step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32706step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32706step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32706step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32706 raw32706Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw32706 raw32706Labels = mixedMoment B raw32706step0 raw32706step0Labels := by
      have hz : ∀ j, raw32706 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32706step0 = (fun i j => raw32706 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32706step0 raw32706; decide +kernel
      have hl : raw32706step0Labels = raw32706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32706 raw32706Labels permutation346 hz
    mixedMoment B raw32706step0 raw32706step0Labels = mixedMoment B raw32706step1 raw32706step1Labels := by
      have ha : raw32706step1 = (fun i j => raw32706step0 (permutation43 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32706step1 raw32706step0; decide +kernel
      have hl : raw32706step1Labels = raw32706step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32706step0 raw32706step0Labels permutation43 permutation5
    mixedMoment B raw32706step1 raw32706step1Labels = mixedMoment B raw32706step2 raw32706step2Labels := by
      have ha : raw32706step2 = -raw32706step1 := by apply Matrix.ext; change ∀ i j, raw32706step2 i j = -(raw32706step1 i j); unfold raw32706step2 raw32706step1; decide +kernel
      have hl : raw32706step2Labels = raw32706step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32706step2 raw32706step2Labels = mixedMoment B raw32706step3 raw32706step3Labels := by
      have ha : raw32706step3 = raw32706step2 := by apply Matrix.ext; unfold raw32706step3 raw32706step2; decide +kernel
      have hl : raw32706step2Labels = labelEmbedding1 ∘ raw32706step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32706step2 raw32706step2Labels raw32706step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw32707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32707Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32707step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32707step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw32707step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32707step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw32707step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32707step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw32707step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32707step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw32707step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32707 raw32707Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw32707 raw32707Labels = mixedMoment B raw32707step0 raw32707step0Labels := by
      have hz : ∀ j, raw32707 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32707step0 = (fun i j => raw32707 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32707step0 raw32707; decide +kernel
      have hl : raw32707step0Labels = raw32707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32707 raw32707Labels permutation520 hz
    mixedMoment B raw32707step0 raw32707step0Labels = mixedMoment B raw32707step1 raw32707step1Labels := by
      have hz : ∀ j, raw32707step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32707step1 = (fun i j => raw32707step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32707step1 raw32707step0; decide +kernel
      have hl : raw32707step1Labels = raw32707step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32707step0 raw32707step0Labels permutation80 hz
    mixedMoment B raw32707step1 raw32707step1Labels = mixedMoment B raw32707step2 raw32707step2Labels := by
      have ha : raw32707step2 = (fun i j => raw32707step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32707step2 raw32707step1; decide +kernel
      have hl : raw32707step2Labels = raw32707step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32707step1 raw32707step1Labels permutation11 permutation5
    mixedMoment B raw32707step2 raw32707step2Labels = mixedMoment B raw32707step3 raw32707step3Labels := by
      have ha : raw32707step3 = -raw32707step2 := by apply Matrix.ext; change ∀ i j, raw32707step3 i j = -(raw32707step2 i j); unfold raw32707step3 raw32707step2; decide +kernel
      have hl : raw32707step3Labels = raw32707step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32707step3 raw32707step3Labels = mixedMoment B raw32707step4 raw32707step4Labels := by
      have ha : raw32707step4 = raw32707step3 := by apply Matrix.ext; unfold raw32707step4 raw32707step3; decide +kernel
      have hl : raw32707step3Labels = labelEmbedding1 ∘ raw32707step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32707step3 raw32707step3Labels raw32707step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3626 node3626Labels := by rfl

def raw32708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32708Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32708step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw32708step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32708step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32708step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32708step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32708step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32708 raw32708Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw32708 raw32708Labels = mixedMoment B raw32708step0 raw32708step0Labels := by
      have hz : ∀ j, raw32708 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32708step0 = (fun i j => raw32708 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32708step0 raw32708; decide +kernel
      have hl : raw32708step0Labels = raw32708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32708 raw32708Labels permutation346 hz
    mixedMoment B raw32708step0 raw32708step0Labels = mixedMoment B raw32708step1 raw32708step1Labels := by
      have ha : raw32708step1 = (fun i j => raw32708step0 (permutation53 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32708step1 raw32708step0; decide +kernel
      have hl : raw32708step1Labels = raw32708step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32708step0 raw32708step0Labels permutation53 permutation5
    mixedMoment B raw32708step1 raw32708step1Labels = mixedMoment B raw32708step2 raw32708step2Labels := by
      have ha : raw32708step2 = -raw32708step1 := by apply Matrix.ext; change ∀ i j, raw32708step2 i j = -(raw32708step1 i j); unfold raw32708step2 raw32708step1; decide +kernel
      have hl : raw32708step2Labels = raw32708step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32708step2 raw32708step2Labels = mixedMoment B raw32708step3 raw32708step3Labels := by
      have ha : raw32708step3 = raw32708step2 := by apply Matrix.ext; unfold raw32708step3 raw32708step2; decide +kernel
      have hl : raw32708step2Labels = labelEmbedding1 ∘ raw32708step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32708step2 raw32708step2Labels raw32708step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw32709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32709Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw32709step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32709step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw32709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32709step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw32709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32709 raw32709Labels = mixedMoment B node1711 node1711Labels := by
  calc
    mixedMoment B raw32709 raw32709Labels = mixedMoment B raw32709step0 raw32709step0Labels := by
      have ha : raw32709step0 = (fun i j => raw32709 (permutation218 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32709step0 raw32709; decide +kernel
      have hl : raw32709step0Labels = raw32709Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32709 raw32709Labels permutation218 permutation5
    mixedMoment B raw32709step0 raw32709step0Labels = mixedMoment B raw32709step1 raw32709step1Labels := by
      have ha : raw32709step1 = -raw32709step0 := by apply Matrix.ext; change ∀ i j, raw32709step1 i j = -(raw32709step0 i j); unfold raw32709step1 raw32709step0; decide +kernel
      have hl : raw32709step1Labels = raw32709step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32709step1 raw32709step1Labels = mixedMoment B raw32709step2 raw32709step2Labels := by
      have ha : raw32709step2 = raw32709step1 := by apply Matrix.ext; unfold raw32709step2 raw32709step1; decide +kernel
      have hl : raw32709step1Labels = labelEmbedding1 ∘ raw32709step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32709step1 raw32709step1Labels raw32709step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1711 node1711Labels := by rfl

def raw32710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32710step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1]]
def raw32710step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32710step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw32710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32710step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw32710step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32710 raw32710Labels = mixedMoment B node3590 node3590Labels := by
  calc
    mixedMoment B raw32710 raw32710Labels = mixedMoment B raw32710step0 raw32710step0Labels := by
      have ha : raw32710step0 = (fun i j => raw32710 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32710step0 raw32710; decide +kernel
      have hl : raw32710step0Labels = raw32710Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32710 raw32710Labels permutation162 permutation5
    mixedMoment B raw32710step0 raw32710step0Labels = mixedMoment B raw32710step1 raw32710step1Labels := by
      have ha : raw32710step1 = -raw32710step0 := by apply Matrix.ext; change ∀ i j, raw32710step1 i j = -(raw32710step0 i j); unfold raw32710step1 raw32710step0; decide +kernel
      have hl : raw32710step1Labels = raw32710step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32710step1 raw32710step1Labels = mixedMoment B raw32710step2 raw32710step2Labels := by
      have ha : raw32710step2 = raw32710step1 := by apply Matrix.ext; unfold raw32710step2 raw32710step1; decide +kernel
      have hl : raw32710step1Labels = labelEmbedding1 ∘ raw32710step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32710step1 raw32710step1Labels raw32710step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3590 node3590Labels := by rfl

def raw32711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32711Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw32711step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32711step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw32711step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32711step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw32711step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32711 raw32711Labels = mixedMoment B node3537 node3537Labels := by
  calc
    mixedMoment B raw32711 raw32711Labels = mixedMoment B raw32711step0 raw32711step0Labels := by
      have ha : raw32711step0 = (fun i j => raw32711 (permutation218 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32711step0 raw32711; decide +kernel
      have hl : raw32711step0Labels = raw32711Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32711 raw32711Labels permutation218 permutation5
    mixedMoment B raw32711step0 raw32711step0Labels = mixedMoment B raw32711step1 raw32711step1Labels := by
      have ha : raw32711step1 = -raw32711step0 := by apply Matrix.ext; change ∀ i j, raw32711step1 i j = -(raw32711step0 i j); unfold raw32711step1 raw32711step0; decide +kernel
      have hl : raw32711step1Labels = raw32711step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32711step1 raw32711step1Labels = mixedMoment B raw32711step2 raw32711step2Labels := by
      have ha : raw32711step2 = raw32711step1 := by apply Matrix.ext; unfold raw32711step2 raw32711step1; decide +kernel
      have hl : raw32711step1Labels = labelEmbedding1 ∘ raw32711step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32711step1 raw32711step1Labels raw32711step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3537 node3537Labels := by rfl

def raw32712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32712Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32712step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw32712step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw32712step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32712step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw32712step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32712 raw32712Labels = mixedMoment B node3624 node3624Labels := by
  calc
    mixedMoment B raw32712 raw32712Labels = mixedMoment B raw32712step0 raw32712step0Labels := by
      have hz : ∀ j, raw32712 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32712step0 = (fun i j => raw32712 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32712step0 raw32712; decide +kernel
      have hl : raw32712step0Labels = raw32712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32712 raw32712Labels permutation520 hz
    mixedMoment B raw32712step0 raw32712step0Labels = mixedMoment B raw32712step1 raw32712step1Labels := by
      have ha : raw32712step1 = (fun i j => raw32712step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32712step1 raw32712step0; decide +kernel
      have hl : raw32712step1Labels = raw32712step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32712step0 raw32712step0Labels permutation48 permutation5
    mixedMoment B raw32712step1 raw32712step1Labels = mixedMoment B raw32712step2 raw32712step2Labels := by
      have ha : raw32712step2 = -raw32712step1 := by apply Matrix.ext; change ∀ i j, raw32712step2 i j = -(raw32712step1 i j); unfold raw32712step2 raw32712step1; decide +kernel
      have hl : raw32712step2Labels = raw32712step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32712step2 raw32712step2Labels = mixedMoment B raw32712step3 raw32712step3Labels := by
      have ha : raw32712step3 = raw32712step2 := by apply Matrix.ext; unfold raw32712step3 raw32712step2; decide +kernel
      have hl : raw32712step2Labels = labelEmbedding1 ∘ raw32712step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32712step2 raw32712step2Labels raw32712step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3624 node3624Labels := by rfl

def raw32713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw32713step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32713step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw32713step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32713step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw32713step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32713 raw32713Labels = mixedMoment B node3569 node3569Labels := by
  calc
    mixedMoment B raw32713 raw32713Labels = mixedMoment B raw32713step0 raw32713step0Labels := by
      have ha : raw32713step0 = (fun i j => raw32713 (permutation257 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32713step0 raw32713; decide +kernel
      have hl : raw32713step0Labels = raw32713Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32713 raw32713Labels permutation257 permutation5
    mixedMoment B raw32713step0 raw32713step0Labels = mixedMoment B raw32713step1 raw32713step1Labels := by
      have ha : raw32713step1 = -raw32713step0 := by apply Matrix.ext; change ∀ i j, raw32713step1 i j = -(raw32713step0 i j); unfold raw32713step1 raw32713step0; decide +kernel
      have hl : raw32713step1Labels = raw32713step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32713step1 raw32713step1Labels = mixedMoment B raw32713step2 raw32713step2Labels := by
      have ha : raw32713step2 = raw32713step1 := by apply Matrix.ext; unfold raw32713step2 raw32713step1; decide +kernel
      have hl : raw32713step1Labels = labelEmbedding1 ∘ raw32713step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32713step1 raw32713step1Labels raw32713step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3569 node3569Labels := by rfl

def raw32714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32714step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32714step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32714step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32714step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32714step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32714step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32714 raw32714Labels = mixedMoment B node1734 node1734Labels := by
  calc
    mixedMoment B raw32714 raw32714Labels = mixedMoment B raw32714step0 raw32714step0Labels := by
      have hz : ∀ j, raw32714 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32714step0 = (fun i j => raw32714 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32714step0 raw32714; decide +kernel
      have hl : raw32714step0Labels = raw32714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32714 raw32714Labels permutation346 hz
    mixedMoment B raw32714step0 raw32714step0Labels = mixedMoment B raw32714step1 raw32714step1Labels := by
      have ha : raw32714step1 = (fun i j => raw32714step0 (permutation51 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32714step1 raw32714step0; decide +kernel
      have hl : raw32714step1Labels = raw32714step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32714step0 raw32714step0Labels permutation51 permutation5
    mixedMoment B raw32714step1 raw32714step1Labels = mixedMoment B raw32714step2 raw32714step2Labels := by
      have ha : raw32714step2 = -raw32714step1 := by apply Matrix.ext; change ∀ i j, raw32714step2 i j = -(raw32714step1 i j); unfold raw32714step2 raw32714step1; decide +kernel
      have hl : raw32714step2Labels = raw32714step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32714step2 raw32714step2Labels = mixedMoment B raw32714step3 raw32714step3Labels := by
      have ha : raw32714step3 = raw32714step2 := by apply Matrix.ext; unfold raw32714step3 raw32714step2; decide +kernel
      have hl : raw32714step2Labels = labelEmbedding1 ∘ raw32714step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32714step2 raw32714step2Labels raw32714step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1734 node1734Labels := by rfl

def raw32715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32715step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, -1, 2]]
def raw32715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32715step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw32715step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32715step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw32715step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32715 raw32715Labels = mixedMoment B node3595 node3595Labels := by
  calc
    mixedMoment B raw32715 raw32715Labels = mixedMoment B raw32715step0 raw32715step0Labels := by
      have hz : ∀ j, raw32715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32715step0 = (fun i j => raw32715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32715step0 raw32715; decide +kernel
      have hl : raw32715step0Labels = raw32715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32715 raw32715Labels permutation346 hz
    mixedMoment B raw32715step0 raw32715step0Labels = mixedMoment B raw32715step1 raw32715step1Labels := by
      have ha : raw32715step1 = (fun i j => raw32715step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32715step1 raw32715step0; decide +kernel
      have hl : raw32715step1Labels = raw32715step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32715step0 raw32715step0Labels permutation37 permutation5
    mixedMoment B raw32715step1 raw32715step1Labels = mixedMoment B raw32715step2 raw32715step2Labels := by
      have ha : raw32715step2 = -raw32715step1 := by apply Matrix.ext; change ∀ i j, raw32715step2 i j = -(raw32715step1 i j); unfold raw32715step2 raw32715step1; decide +kernel
      have hl : raw32715step2Labels = raw32715step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32715step2 raw32715step2Labels = mixedMoment B raw32715step3 raw32715step3Labels := by
      have ha : raw32715step3 = raw32715step2 := by apply Matrix.ext; unfold raw32715step3 raw32715step2; decide +kernel
      have hl : raw32715step2Labels = labelEmbedding1 ∘ raw32715step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32715step2 raw32715step2Labels raw32715step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3595 node3595Labels := by rfl

def raw32716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32716step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32716step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32716step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32716step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32716 raw32716Labels = mixedMoment B node3474 node3474Labels := by
  calc
    mixedMoment B raw32716 raw32716Labels = mixedMoment B raw32716step0 raw32716step0Labels := by
      have ha : raw32716step0 = (fun i j => raw32716 (permutation195 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32716step0 raw32716; decide +kernel
      have hl : raw32716step0Labels = raw32716Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32716 raw32716Labels permutation195 permutation5
    mixedMoment B raw32716step0 raw32716step0Labels = mixedMoment B raw32716step1 raw32716step1Labels := by
      have ha : raw32716step1 = -raw32716step0 := by apply Matrix.ext; change ∀ i j, raw32716step1 i j = -(raw32716step0 i j); unfold raw32716step1 raw32716step0; decide +kernel
      have hl : raw32716step1Labels = raw32716step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32716step1 raw32716step1Labels = mixedMoment B raw32716step2 raw32716step2Labels := by
      have ha : raw32716step2 = raw32716step1 := by apply Matrix.ext; unfold raw32716step2 raw32716step1; decide +kernel
      have hl : raw32716step1Labels = labelEmbedding1 ∘ raw32716step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32716step1 raw32716step1Labels raw32716step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3474 node3474Labels := by rfl

def raw32717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw32717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32717step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32717step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw32717step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32717step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, -1, 2]]
def raw32717step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32717step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw32717step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32717step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw32717step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32717 raw32717Labels = mixedMoment B node3631 node3631Labels := by
  calc
    mixedMoment B raw32717 raw32717Labels = mixedMoment B raw32717step0 raw32717step0Labels := by
      have hz : ∀ j, raw32717 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32717step0 = (fun i j => raw32717 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32717step0 raw32717; decide +kernel
      have hl : raw32717step0Labels = raw32717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32717 raw32717Labels permutation520 hz
    mixedMoment B raw32717step0 raw32717step0Labels = mixedMoment B raw32717step1 raw32717step1Labels := by
      have hz : ∀ j, raw32717step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32717step1 = (fun i j => raw32717step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32717step1 raw32717step0; decide +kernel
      have hl : raw32717step1Labels = raw32717step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32717step0 raw32717step0Labels permutation80 hz
    mixedMoment B raw32717step1 raw32717step1Labels = mixedMoment B raw32717step2 raw32717step2Labels := by
      have ha : raw32717step2 = (fun i j => raw32717step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32717step2 raw32717step1; decide +kernel
      have hl : raw32717step2Labels = raw32717step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32717step1 raw32717step1Labels permutation12 permutation5
    mixedMoment B raw32717step2 raw32717step2Labels = mixedMoment B raw32717step3 raw32717step3Labels := by
      have ha : raw32717step3 = -raw32717step2 := by apply Matrix.ext; change ∀ i j, raw32717step3 i j = -(raw32717step2 i j); unfold raw32717step3 raw32717step2; decide +kernel
      have hl : raw32717step3Labels = raw32717step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32717step3 raw32717step3Labels = mixedMoment B raw32717step4 raw32717step4Labels := by
      have ha : raw32717step4 = raw32717step3 := by apply Matrix.ext; unfold raw32717step4 raw32717step3; decide +kernel
      have hl : raw32717step3Labels = labelEmbedding1 ∘ raw32717step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32717step3 raw32717step3Labels raw32717step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3631 node3631Labels := by rfl

def raw32718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw32718step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32718step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32718step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32718step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32718 raw32718Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw32718 raw32718Labels = mixedMoment B raw32718step0 raw32718step0Labels := by
      have hz : ∀ j, raw32718 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32718step0 = (fun i j => raw32718 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32718step0 raw32718; decide +kernel
      have hl : raw32718step0Labels = raw32718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32718 raw32718Labels permutation346 hz
    mixedMoment B raw32718step0 raw32718step0Labels = mixedMoment B raw32718step1 raw32718step1Labels := by
      have ha : raw32718step1 = (fun i j => raw32718step0 (permutation51 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32718step1 raw32718step0; decide +kernel
      have hl : raw32718step1Labels = raw32718step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32718step0 raw32718step0Labels permutation51 permutation5
    mixedMoment B raw32718step1 raw32718step1Labels = mixedMoment B raw32718step2 raw32718step2Labels := by
      have ha : raw32718step2 = -raw32718step1 := by apply Matrix.ext; change ∀ i j, raw32718step2 i j = -(raw32718step1 i j); unfold raw32718step2 raw32718step1; decide +kernel
      have hl : raw32718step2Labels = raw32718step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32718step2 raw32718step2Labels = mixedMoment B raw32718step3 raw32718step3Labels := by
      have ha : raw32718step3 = raw32718step2 := by apply Matrix.ext; unfold raw32718step3 raw32718step2; decide +kernel
      have hl : raw32718step2Labels = labelEmbedding1 ∘ raw32718step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32718step2 raw32718step2Labels raw32718step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

def raw32719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32719step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw32719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32719step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32719step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32719step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32719step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32719 raw32719Labels = mixedMoment B node1712 node1712Labels := by
  calc
    mixedMoment B raw32719 raw32719Labels = mixedMoment B raw32719step0 raw32719step0Labels := by
      have hz : ∀ j, raw32719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32719step0 = (fun i j => raw32719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32719step0 raw32719; decide +kernel
      have hl : raw32719step0Labels = raw32719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32719 raw32719Labels permutation346 hz
    mixedMoment B raw32719step0 raw32719step0Labels = mixedMoment B raw32719step1 raw32719step1Labels := by
      have ha : raw32719step1 = (fun i j => raw32719step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32719step1 raw32719step0; decide +kernel
      have hl : raw32719step1Labels = raw32719step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32719step0 raw32719step0Labels permutation42 permutation5
    mixedMoment B raw32719step1 raw32719step1Labels = mixedMoment B raw32719step2 raw32719step2Labels := by
      have ha : raw32719step2 = -raw32719step1 := by apply Matrix.ext; change ∀ i j, raw32719step2 i j = -(raw32719step1 i j); unfold raw32719step2 raw32719step1; decide +kernel
      have hl : raw32719step2Labels = raw32719step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32719step2 raw32719step2Labels = mixedMoment B raw32719step3 raw32719step3Labels := by
      have ha : raw32719step3 = raw32719step2 := by apply Matrix.ext; unfold raw32719step3 raw32719step2; decide +kernel
      have hl : raw32719step2Labels = labelEmbedding1 ∘ raw32719step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32719step2 raw32719step2Labels raw32719step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1712 node1712Labels := by rfl

def raw32720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw32720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw32720step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32720step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw32720step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32720 raw32720Labels = mixedMoment B node3591 node3591Labels := by
  calc
    mixedMoment B raw32720 raw32720Labels = mixedMoment B raw32720step0 raw32720step0Labels := by
      have hz : ∀ j, raw32720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32720step0 = (fun i j => raw32720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32720step0 raw32720; decide +kernel
      have hl : raw32720step0Labels = raw32720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32720 raw32720Labels permutation346 hz
    mixedMoment B raw32720step0 raw32720step0Labels = mixedMoment B raw32720step1 raw32720step1Labels := by
      have ha : raw32720step1 = (fun i j => raw32720step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32720step1 raw32720step0; decide +kernel
      have hl : raw32720step1Labels = raw32720step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32720step0 raw32720step0Labels permutation33 permutation5
    mixedMoment B raw32720step1 raw32720step1Labels = mixedMoment B raw32720step2 raw32720step2Labels := by
      have ha : raw32720step2 = -raw32720step1 := by apply Matrix.ext; change ∀ i j, raw32720step2 i j = -(raw32720step1 i j); unfold raw32720step2 raw32720step1; decide +kernel
      have hl : raw32720step2Labels = raw32720step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32720step2 raw32720step2Labels = mixedMoment B raw32720step3 raw32720step3Labels := by
      have ha : raw32720step3 = raw32720step2 := by apply Matrix.ext; unfold raw32720step3 raw32720step2; decide +kernel
      have hl : raw32720step2Labels = labelEmbedding1 ∘ raw32720step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32720step2 raw32720step2Labels raw32720step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3591 node3591Labels := by rfl

def raw32721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw32721step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32721step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32721step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32721step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32721 raw32721Labels = mixedMoment B node3462 node3462Labels := by
  calc
    mixedMoment B raw32721 raw32721Labels = mixedMoment B raw32721step0 raw32721step0Labels := by
      have ha : raw32721step0 = (fun i j => raw32721 (permutation186 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32721step0 raw32721; decide +kernel
      have hl : raw32721step0Labels = raw32721Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32721 raw32721Labels permutation186 permutation5
    mixedMoment B raw32721step0 raw32721step0Labels = mixedMoment B raw32721step1 raw32721step1Labels := by
      have ha : raw32721step1 = -raw32721step0 := by apply Matrix.ext; change ∀ i j, raw32721step1 i j = -(raw32721step0 i j); unfold raw32721step1 raw32721step0; decide +kernel
      have hl : raw32721step1Labels = raw32721step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32721step1 raw32721step1Labels = mixedMoment B raw32721step2 raw32721step2Labels := by
      have ha : raw32721step2 = raw32721step1 := by apply Matrix.ext; unfold raw32721step2 raw32721step1; decide +kernel
      have hl : raw32721step1Labels = labelEmbedding1 ∘ raw32721step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32721step1 raw32721step1Labels raw32721step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3462 node3462Labels := by rfl

def raw32722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32722step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw32722step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32722step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32722step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32722step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32722step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32722 raw32722Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw32722 raw32722Labels = mixedMoment B raw32722step0 raw32722step0Labels := by
      have hz : ∀ j, raw32722 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32722step0 = (fun i j => raw32722 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32722step0 raw32722; decide +kernel
      have hl : raw32722step0Labels = raw32722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32722 raw32722Labels permutation346 hz
    mixedMoment B raw32722step0 raw32722step0Labels = mixedMoment B raw32722step1 raw32722step1Labels := by
      have ha : raw32722step1 = (fun i j => raw32722step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32722step1 raw32722step0; decide +kernel
      have hl : raw32722step1Labels = raw32722step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32722step0 raw32722step0Labels permutation42 permutation5
    mixedMoment B raw32722step1 raw32722step1Labels = mixedMoment B raw32722step2 raw32722step2Labels := by
      have ha : raw32722step2 = -raw32722step1 := by apply Matrix.ext; change ∀ i j, raw32722step2 i j = -(raw32722step1 i j); unfold raw32722step2 raw32722step1; decide +kernel
      have hl : raw32722step2Labels = raw32722step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32722step2 raw32722step2Labels = mixedMoment B raw32722step3 raw32722step3Labels := by
      have ha : raw32722step3 = raw32722step2 := by apply Matrix.ext; unfold raw32722step3 raw32722step2; decide +kernel
      have hl : raw32722step2Labels = labelEmbedding1 ∘ raw32722step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32722step2 raw32722step2Labels raw32722step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3538 node3538Labels := by rfl

def raw32723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw32723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw32723step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw32723step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32723step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32723step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32723step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32723 raw32723Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw32723 raw32723Labels = mixedMoment B raw32723step0 raw32723step0Labels := by
      have hz : ∀ j, raw32723 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32723step0 = (fun i j => raw32723 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32723step0 raw32723; decide +kernel
      have hl : raw32723step0Labels = raw32723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32723 raw32723Labels permutation346 hz
    mixedMoment B raw32723step0 raw32723step0Labels = mixedMoment B raw32723step1 raw32723step1Labels := by
      have ha : raw32723step1 = (fun i j => raw32723step0 (permutation52 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32723step1 raw32723step0; decide +kernel
      have hl : raw32723step1Labels = raw32723step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32723step0 raw32723step0Labels permutation52 permutation5
    mixedMoment B raw32723step1 raw32723step1Labels = mixedMoment B raw32723step2 raw32723step2Labels := by
      have ha : raw32723step2 = -raw32723step1 := by apply Matrix.ext; change ∀ i j, raw32723step2 i j = -(raw32723step1 i j); unfold raw32723step2 raw32723step1; decide +kernel
      have hl : raw32723step2Labels = raw32723step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32723step2 raw32723step2Labels = mixedMoment B raw32723step3 raw32723step3Labels := by
      have ha : raw32723step3 = raw32723step2 := by apply Matrix.ext; unfold raw32723step3 raw32723step2; decide +kernel
      have hl : raw32723step2Labels = labelEmbedding1 ∘ raw32723step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32723step2 raw32723step2Labels raw32723step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3570 node3570Labels := by rfl

def raw32724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32724Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32724step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw32724step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw32724step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32724step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw32724step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32724 raw32724Labels = mixedMoment B node1720 node1720Labels := by
  calc
    mixedMoment B raw32724 raw32724Labels = mixedMoment B raw32724step0 raw32724step0Labels := by
      have hz : ∀ j, raw32724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32724step0 = (fun i j => raw32724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32724step0 raw32724; decide +kernel
      have hl : raw32724step0Labels = raw32724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32724 raw32724Labels permutation346 hz
    mixedMoment B raw32724step0 raw32724step0Labels = mixedMoment B raw32724step1 raw32724step1Labels := by
      have ha : raw32724step1 = (fun i j => raw32724step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32724step1 raw32724step0; decide +kernel
      have hl : raw32724step1Labels = raw32724step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32724step0 raw32724step0Labels permutation38 permutation5
    mixedMoment B raw32724step1 raw32724step1Labels = mixedMoment B raw32724step2 raw32724step2Labels := by
      have ha : raw32724step2 = -raw32724step1 := by apply Matrix.ext; change ∀ i j, raw32724step2 i j = -(raw32724step1 i j); unfold raw32724step2 raw32724step1; decide +kernel
      have hl : raw32724step2Labels = raw32724step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32724step2 raw32724step2Labels = mixedMoment B raw32724step3 raw32724step3Labels := by
      have ha : raw32724step3 = raw32724step2 := by apply Matrix.ext; unfold raw32724step3 raw32724step2; decide +kernel
      have hl : raw32724step2Labels = labelEmbedding1 ∘ raw32724step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32724step2 raw32724step2Labels raw32724step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1720 node1720Labels := by rfl

def raw32725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32725Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32725step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw32725step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw32725step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32725 raw32725Labels = mixedMoment B node3457 node3457Labels := by
  calc
    mixedMoment B raw32725 raw32725Labels = mixedMoment B raw32725step0 raw32725step0Labels := by
      have hz : ∀ j, raw32725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32725step0 = (fun i j => raw32725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32725step0 raw32725; decide +kernel
      have hl : raw32725step0Labels = raw32725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32725 raw32725Labels permutation346 hz
    mixedMoment B raw32725step0 raw32725step0Labels = mixedMoment B raw32725step1 raw32725step1Labels := by
      have ha : raw32725step1 = (fun i j => raw32725step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32725step1 raw32725step0; decide +kernel
      have hl : raw32725step1Labels = raw32725step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32725step0 raw32725step0Labels permutation144 permutation7
    mixedMoment B raw32725step1 raw32725step1Labels = mixedMoment B raw32725step2 raw32725step2Labels := by
      have ha : raw32725step2 = raw32725step1 := by apply Matrix.ext; unfold raw32725step2 raw32725step1; decide +kernel
      have hl : raw32725step1Labels = labelEmbedding1 ∘ raw32725step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32725step1 raw32725step1Labels raw32725step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3457 node3457Labels := by rfl

def raw32726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32726Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw32726step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32726step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw32726step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32726 raw32726Labels = mixedMoment B node3451 node3451Labels := by
  calc
    mixedMoment B raw32726 raw32726Labels = mixedMoment B raw32726step0 raw32726step0Labels := by
      have ha : raw32726step0 = (fun i j => raw32726 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32726step0 raw32726; decide +kernel
      have hl : raw32726step0Labels = raw32726Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32726 raw32726Labels permutation663 permutation7
    mixedMoment B raw32726step0 raw32726step0Labels = mixedMoment B raw32726step1 raw32726step1Labels := by
      have ha : raw32726step1 = raw32726step0 := by apply Matrix.ext; unfold raw32726step1 raw32726step0; decide +kernel
      have hl : raw32726step0Labels = labelEmbedding1 ∘ raw32726step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32726step0 raw32726step0Labels raw32726step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3451 node3451Labels := by rfl

def raw32727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32727step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw32727step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32727step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw32727step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32727 raw32727Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw32727 raw32727Labels = mixedMoment B raw32727step0 raw32727step0Labels := by
      have hz : ∀ j, raw32727 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32727step0 = (fun i j => raw32727 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32727step0 raw32727; decide +kernel
      have hl : raw32727step0Labels = raw32727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32727 raw32727Labels permutation346 hz
    mixedMoment B raw32727step0 raw32727step0Labels = mixedMoment B raw32727step1 raw32727step1Labels := by
      have ha : raw32727step1 = (fun i j => raw32727step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32727step1 raw32727step0; decide +kernel
      have hl : raw32727step1Labels = raw32727step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32727step0 raw32727step0Labels permutation144 permutation7
    mixedMoment B raw32727step1 raw32727step1Labels = mixedMoment B raw32727step2 raw32727step2Labels := by
      have ha : raw32727step2 = raw32727step1 := by apply Matrix.ext; unfold raw32727step2 raw32727step1; decide +kernel
      have hl : raw32727step1Labels = labelEmbedding1 ∘ raw32727step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32727step1 raw32727step1Labels raw32727step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

def raw32728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw32728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw32728step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw32728step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw32728step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32728step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw32728step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32728 raw32728Labels = mixedMoment B node3486 node3486Labels := by
  calc
    mixedMoment B raw32728 raw32728Labels = mixedMoment B raw32728step0 raw32728step0Labels := by
      have hz : ∀ j, raw32728 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32728step0 = (fun i j => raw32728 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32728step0 raw32728; decide +kernel
      have hl : raw32728step0Labels = raw32728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32728 raw32728Labels permutation520 hz
    mixedMoment B raw32728step0 raw32728step0Labels = mixedMoment B raw32728step1 raw32728step1Labels := by
      have hz : ∀ j, raw32728step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32728step1 = (fun i j => raw32728step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32728step1 raw32728step0; decide +kernel
      have hl : raw32728step1Labels = raw32728step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32728step0 raw32728step0Labels permutation80 hz
    mixedMoment B raw32728step1 raw32728step1Labels = mixedMoment B raw32728step2 raw32728step2Labels := by
      have ha : raw32728step2 = (fun i j => raw32728step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32728step2 raw32728step1; decide +kernel
      have hl : raw32728step2Labels = raw32728step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32728step1 raw32728step1Labels permutation30 permutation7
    mixedMoment B raw32728step2 raw32728step2Labels = mixedMoment B raw32728step3 raw32728step3Labels := by
      have ha : raw32728step3 = raw32728step2 := by apply Matrix.ext; unfold raw32728step3 raw32728step2; decide +kernel
      have hl : raw32728step2Labels = labelEmbedding1 ∘ raw32728step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32728step2 raw32728step2Labels raw32728step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3486 node3486Labels := by rfl

def raw32729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32729Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32729step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw32729step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32729step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32729 raw32729Labels = mixedMoment B node3498 node3498Labels := by
  calc
    mixedMoment B raw32729 raw32729Labels = mixedMoment B raw32729step0 raw32729step0Labels := by
      have hz : ∀ j, raw32729 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32729step0 = (fun i j => raw32729 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32729step0 raw32729; decide +kernel
      have hl : raw32729step0Labels = raw32729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32729 raw32729Labels permutation346 hz
    mixedMoment B raw32729step0 raw32729step0Labels = mixedMoment B raw32729step1 raw32729step1Labels := by
      have ha : raw32729step1 = (fun i j => raw32729step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32729step1 raw32729step0; decide +kernel
      have hl : raw32729step1Labels = raw32729step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32729step0 raw32729step0Labels permutation144 permutation2
    mixedMoment B raw32729step1 raw32729step1Labels = mixedMoment B raw32729step2 raw32729step2Labels := by
      have ha : raw32729step2 = -raw32729step1 := by apply Matrix.ext; change ∀ i j, raw32729step2 i j = -(raw32729step1 i j); unfold raw32729step2 raw32729step1; decide +kernel
      have hl : raw32729step2Labels = raw32729step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3498 node3498Labels := by rfl

def raw32730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32730Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32730step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32730 raw32730Labels = mixedMoment B node2879 node2879Labels := by
  calc
    mixedMoment B raw32730 raw32730Labels = mixedMoment B raw32730step0 raw32730step0Labels := by
      have hz : ∀ j, raw32730 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32730step0 = (fun i j => raw32730 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32730step0 raw32730; decide +kernel
      have hl : raw32730step0Labels = raw32730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32730 raw32730Labels permutation346 hz
    _ = mixedMoment B node2879 node2879Labels := by rfl

def raw32731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32731Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32731 raw32731Labels = mixedMoment B node2806 node2806Labels := by
  calc
    _ = mixedMoment B node2806 node2806Labels := by rfl

def raw32732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32732Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32732step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw32732step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32732 raw32732Labels = mixedMoment B node2812 node2812Labels := by
  calc
    mixedMoment B raw32732 raw32732Labels = mixedMoment B raw32732step0 raw32732step0Labels := by
      have hz : ∀ j, raw32732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32732step0 = (fun i j => raw32732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32732step0 raw32732; decide +kernel
      have hl : raw32732step0Labels = raw32732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32732 raw32732Labels permutation346 hz
    mixedMoment B raw32732step0 raw32732step0Labels = mixedMoment B raw32732step1 raw32732step1Labels := by
      have ha : raw32732step1 = (fun i j => raw32732step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32732step1 raw32732step0; decide +kernel
      have hl : raw32732step1Labels = raw32732step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32732step0 raw32732step0Labels permutation34 permutation2
    _ = mixedMoment B node2812 node2812Labels := by rfl

def raw32733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw32733Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw32733step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32733 raw32733Labels = mixedMoment B node2812 node2812Labels := by
  calc
    mixedMoment B raw32733 raw32733Labels = mixedMoment B raw32733step0 raw32733step0Labels := by
      have hz : ∀ j, raw32733 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32733step0 = (fun i j => raw32733 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32733step0 raw32733; decide +kernel
      have hl : raw32733step0Labels = raw32733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32733 raw32733Labels permutation346 hz
    _ = mixedMoment B node2812 node2812Labels := by rfl

def raw32734 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32734Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0]]
def raw32734step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]
def raw32734step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32734 raw32734Labels = mixedMoment B node3620 node3620Labels := by
  calc
    mixedMoment B raw32734 raw32734Labels = mixedMoment B raw32734step0 raw32734step0Labels := by
      have ha : raw32734step0 = (fun i j => raw32734 (permutation216 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32734step0 raw32734; decide +kernel
      have hl : raw32734step0Labels = raw32734Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32734 raw32734Labels permutation216 permutation4
    mixedMoment B raw32734step0 raw32734step0Labels = mixedMoment B raw32734step1 raw32734step1Labels := by
      have ha : raw32734step1 = -raw32734step0 := by apply Matrix.ext; change ∀ i j, raw32734step1 i j = -(raw32734step0 i j); unfold raw32734step1 raw32734step0; decide +kernel
      have hl : raw32734step1Labels = raw32734step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3620 node3620Labels := by rfl

def raw32735 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32735Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32735step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32735step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32735 raw32735Labels = mixedMoment B node3356 node3356Labels := by
  calc
    mixedMoment B raw32735 raw32735Labels = mixedMoment B raw32735step0 raw32735step0Labels := by
      have hz : ∀ j, raw32735 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32735step0 = (fun i j => raw32735 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32735step0 raw32735; decide +kernel
      have hl : raw32735step0Labels = raw32735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32735 raw32735Labels permutation346 hz
    mixedMoment B raw32735step0 raw32735step0Labels = mixedMoment B raw32735step1 raw32735step1Labels := by
      have ha : raw32735step1 = -raw32735step0 := by apply Matrix.ext; change ∀ i j, raw32735step1 i j = -(raw32735step0 i j); unfold raw32735step1 raw32735step0; decide +kernel
      have hl : raw32735step1Labels = raw32735step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3356 node3356Labels := by rfl

def raw32736 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32736Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw32736step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32736 raw32736Labels = mixedMoment B node3333 node3333Labels := by
  calc
    mixedMoment B raw32736 raw32736Labels = mixedMoment B raw32736step0 raw32736step0Labels := by
      have ha : raw32736step0 = (fun i j => raw32736 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32736step0 raw32736; decide +kernel
      have hl : raw32736step0Labels = raw32736Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32736 raw32736Labels permutation154 permutation2
    mixedMoment B raw32736step0 raw32736step0Labels = mixedMoment B raw32736step1 raw32736step1Labels := by
      have ha : raw32736step1 = -raw32736step0 := by apply Matrix.ext; change ∀ i j, raw32736step1 i j = -(raw32736step0 i j); unfold raw32736step1 raw32736step0; decide +kernel
      have hl : raw32736step1Labels = raw32736step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3333 node3333Labels := by rfl

def raw32737 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw32737Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32737step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32737 raw32737Labels = mixedMoment B node3333 node3333Labels := by
  calc
    mixedMoment B raw32737 raw32737Labels = mixedMoment B raw32737step0 raw32737step0Labels := by
      have ha : raw32737step0 = -raw32737 := by apply Matrix.ext; change ∀ i j, raw32737step0 i j = -(raw32737 i j); unfold raw32737step0 raw32737; decide +kernel
      have hl : raw32737step0Labels = raw32737Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3333 node3333Labels := by rfl

def raw32738 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw32738Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw32738step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32738 raw32738Labels = mixedMoment B node2413 node2413Labels := by
  calc
    mixedMoment B raw32738 raw32738Labels = mixedMoment B raw32738step0 raw32738step0Labels := by
      have ha : raw32738step0 = (fun i j => raw32738 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32738step0 raw32738; decide +kernel
      have hl : raw32738step0Labels = raw32738Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32738 raw32738Labels permutation664 permutation2
    _ = mixedMoment B node2413 node2413Labels := by rfl

def raw32739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32739Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw32739step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32739step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32739 raw32739Labels = mixedMoment B node3067 node3067Labels := by
  calc
    mixedMoment B raw32739 raw32739Labels = mixedMoment B raw32739step0 raw32739step0Labels := by
      have ha : raw32739step0 = (fun i j => raw32739 (permutation314 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32739step0 raw32739; decide +kernel
      have hl : raw32739step0Labels = raw32739Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32739 raw32739Labels permutation314 permutation4
    mixedMoment B raw32739step0 raw32739step0Labels = mixedMoment B raw32739step1 raw32739step1Labels := by
      have ha : raw32739step1 = -raw32739step0 := by apply Matrix.ext; change ∀ i j, raw32739step1 i j = -(raw32739step0 i j); unfold raw32739step1 raw32739step0; decide +kernel
      have hl : raw32739step1Labels = raw32739step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3067 node3067Labels := by rfl

def raw32740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32740Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32740 raw32740Labels = mixedMoment B node3751 node3751Labels := by
  calc
    mixedMoment B raw32740 raw32740Labels = mixedMoment B raw32740step0 raw32740step0Labels := by
      have ha : raw32740step0 = (fun i j => raw32740 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32740step0 raw32740; decide +kernel
      have hl : raw32740step0Labels = raw32740Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32740 raw32740Labels permutation176 permutation2
    _ = mixedMoment B node3751 node3751Labels := by rfl

def raw32741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32741 raw32741Labels = mixedMoment B node3866 node3866Labels := by
  calc
    _ = mixedMoment B node3866 node3866Labels := by rfl

def raw32742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32742 raw32742Labels = mixedMoment B node3866 node3866Labels := by
  calc
    mixedMoment B raw32742 raw32742Labels = mixedMoment B raw32742step0 raw32742step0Labels := by
      have ha : raw32742step0 = (fun i j => raw32742 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32742step0 raw32742; decide +kernel
      have hl : raw32742step0Labels = raw32742Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32742 raw32742Labels permutation154 permutation2
    _ = mixedMoment B node3866 node3866Labels := by rfl

def raw32743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32743Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32743 raw32743Labels = mixedMoment B node3867 node3867Labels := by
  calc
    _ = mixedMoment B node3867 node3867Labels := by rfl

def raw32744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32744step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32744step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32744 raw32744Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw32744 raw32744Labels = mixedMoment B raw32744step0 raw32744step0Labels := by
      have hz : ∀ j, raw32744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32744step0 = (fun i j => raw32744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32744step0 raw32744; decide +kernel
      have hl : raw32744step0Labels = raw32744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32744 raw32744Labels permutation346 hz
    mixedMoment B raw32744step0 raw32744step0Labels = mixedMoment B raw32744step1 raw32744step1Labels := by
      have ha : raw32744step1 = (fun i j => raw32744step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32744step1 raw32744step0; decide +kernel
      have hl : raw32744step1Labels = raw32744step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32744step0 raw32744step0Labels permutation34 permutation2
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw32745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32745Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw32745step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32745step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32745step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32745 raw32745Labels = mixedMoment B node5400 node5400Labels := by
  calc
    mixedMoment B raw32745 raw32745Labels = mixedMoment B raw32745step0 raw32745step0Labels := by
      have ha : raw32745step0 = (fun i j => raw32745 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32745step0 raw32745; decide +kernel
      have hl : raw32745step0Labels = raw32745Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32745 raw32745Labels permutation662 permutation2
    mixedMoment B raw32745step0 raw32745step0Labels = mixedMoment B raw32745step1 raw32745step1Labels := by
      have ha : raw32745step1 = -raw32745step0 := by apply Matrix.ext; change ∀ i j, raw32745step1 i j = -(raw32745step0 i j); unfold raw32745step1 raw32745step0; decide +kernel
      have hl : raw32745step1Labels = raw32745step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5400 node5400Labels := by rfl

def raw32746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32746step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32746 raw32746Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw32746 raw32746Labels = mixedMoment B raw32746step0 raw32746step0Labels := by
      have hz : ∀ j, raw32746 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32746step0 = (fun i j => raw32746 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32746step0 raw32746; decide +kernel
      have hl : raw32746step0Labels = raw32746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32746 raw32746Labels permutation346 hz
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw32747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32747step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw32747step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32747step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32747 raw32747Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw32747 raw32747Labels = mixedMoment B raw32747step0 raw32747step0Labels := by
      have hz : ∀ j, raw32747 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32747step0 = (fun i j => raw32747 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32747step0 raw32747; decide +kernel
      have hl : raw32747step0Labels = raw32747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32747 raw32747Labels permutation346 hz
    mixedMoment B raw32747step0 raw32747step0Labels = mixedMoment B raw32747step1 raw32747step1Labels := by
      have ha : raw32747step1 = (fun i j => raw32747step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32747step1 raw32747step0; decide +kernel
      have hl : raw32747step1Labels = raw32747step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32747step0 raw32747step0Labels permutation145 permutation2
    mixedMoment B raw32747step1 raw32747step1Labels = mixedMoment B raw32747step2 raw32747step2Labels := by
      have ha : raw32747step2 = -raw32747step1 := by apply Matrix.ext; change ∀ i j, raw32747step2 i j = -(raw32747step1 i j); unfold raw32747step2 raw32747step1; decide +kernel
      have hl : raw32747step2Labels = raw32747step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5409 node5409Labels := by rfl

def raw32748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32748Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32748step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32748step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32748 raw32748Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw32748 raw32748Labels = mixedMoment B raw32748step0 raw32748step0Labels := by
      have hz : ∀ j, raw32748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32748step0 = (fun i j => raw32748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32748step0 raw32748; decide +kernel
      have hl : raw32748step0Labels = raw32748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32748 raw32748Labels permutation346 hz
    mixedMoment B raw32748step0 raw32748step0Labels = mixedMoment B raw32748step1 raw32748step1Labels := by
      have ha : raw32748step1 = (fun i j => raw32748step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32748step1 raw32748step0; decide +kernel
      have hl : raw32748step1Labels = raw32748step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32748step0 raw32748step0Labels permutation34 permutation2
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw32749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32749step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32749step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32749step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32749step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32749 raw32749Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw32749 raw32749Labels = mixedMoment B raw32749step0 raw32749step0Labels := by
      have hz : ∀ j, raw32749 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32749step0 = (fun i j => raw32749 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32749step0 raw32749; decide +kernel
      have hl : raw32749step0Labels = raw32749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32749 raw32749Labels permutation346 hz
    mixedMoment B raw32749step0 raw32749step0Labels = mixedMoment B raw32749step1 raw32749step1Labels := by
      have hz : ∀ j, raw32749step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw32749step1 = (fun i j => raw32749step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw32749step1 raw32749step0; decide +kernel
      have hl : raw32749step1Labels = raw32749step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32749step0 raw32749step0Labels permutation56 hz
    mixedMoment B raw32749step1 raw32749step1Labels = mixedMoment B raw32749step2 raw32749step2Labels := by
      have ha : raw32749step2 = (fun i j => raw32749step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32749step2 raw32749step1; decide +kernel
      have hl : raw32749step2Labels = raw32749step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32749step1 raw32749step1Labels permutation10 permutation2
    _ = mixedMoment B node4619 node4619Labels := by rfl

def raw32750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32750step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32750 raw32750Labels = mixedMoment B node4963 node4963Labels := by
  calc
    mixedMoment B raw32750 raw32750Labels = mixedMoment B raw32750step0 raw32750step0Labels := by
      have ha : raw32750step0 = (fun i j => raw32750 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32750step0 raw32750; decide +kernel
      have hl : raw32750step0Labels = raw32750Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32750 raw32750Labels permutation164 permutation2
    _ = mixedMoment B node4963 node4963Labels := by rfl

def raw32751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32751step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32751 raw32751Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw32751 raw32751Labels = mixedMoment B raw32751step0 raw32751step0Labels := by
      have ha : raw32751step0 = (fun i j => raw32751 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32751step0 raw32751; decide +kernel
      have hl : raw32751step0Labels = raw32751Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32751 raw32751Labels permutation160 permutation2
    _ = mixedMoment B node5144 node5144Labels := by rfl

def raw32752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32752step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32752 raw32752Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw32752 raw32752Labels = mixedMoment B raw32752step0 raw32752step0Labels := by
      have ha : raw32752step0 = (fun i j => raw32752 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32752step0 raw32752; decide +kernel
      have hl : raw32752step0Labels = raw32752Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32752 raw32752Labels permutation164 permutation2
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw32753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32753 raw32753Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw32753 raw32753Labels = mixedMoment B raw32753step0 raw32753step0Labels := by
      have ha : raw32753step0 = (fun i j => raw32753 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32753step0 raw32753; decide +kernel
      have hl : raw32753step0Labels = raw32753Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32753 raw32753Labels permutation164 permutation2
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw32754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32754step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32754step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32754 raw32754Labels = mixedMoment B node4966 node4966Labels := by
  calc
    mixedMoment B raw32754 raw32754Labels = mixedMoment B raw32754step0 raw32754step0Labels := by
      have hz : ∀ j, raw32754 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32754step0 = (fun i j => raw32754 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32754step0 raw32754; decide +kernel
      have hl : raw32754step0Labels = raw32754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32754 raw32754Labels permutation346 hz
    mixedMoment B raw32754step0 raw32754step0Labels = mixedMoment B raw32754step1 raw32754step1Labels := by
      have ha : raw32754step1 = (fun i j => raw32754step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32754step1 raw32754step0; decide +kernel
      have hl : raw32754step1Labels = raw32754step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32754step0 raw32754step0Labels permutation34 permutation2
    _ = mixedMoment B node4966 node4966Labels := by rfl

def raw32755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32755step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32755 raw32755Labels = mixedMoment B node5112 node5112Labels := by
  calc
    mixedMoment B raw32755 raw32755Labels = mixedMoment B raw32755step0 raw32755step0Labels := by
      have ha : raw32755step0 = (fun i j => raw32755 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32755step0 raw32755; decide +kernel
      have hl : raw32755step0Labels = raw32755Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32755 raw32755Labels permutation154 permutation2
    _ = mixedMoment B node5112 node5112Labels := by rfl

def raw32756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32756step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32756step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32756 raw32756Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw32756 raw32756Labels = mixedMoment B raw32756step0 raw32756step0Labels := by
      have hz : ∀ j, raw32756 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32756step0 = (fun i j => raw32756 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32756step0 raw32756; decide +kernel
      have hl : raw32756step0Labels = raw32756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32756 raw32756Labels permutation346 hz
    mixedMoment B raw32756step0 raw32756step0Labels = mixedMoment B raw32756step1 raw32756step1Labels := by
      have ha : raw32756step1 = (fun i j => raw32756step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32756step1 raw32756step0; decide +kernel
      have hl : raw32756step1Labels = raw32756step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32756step0 raw32756step0Labels permutation34 permutation2
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw32757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32757step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32757step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32757 raw32757Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw32757 raw32757Labels = mixedMoment B raw32757step0 raw32757step0Labels := by
      have hz : ∀ j, raw32757 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32757step0 = (fun i j => raw32757 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32757step0 raw32757; decide +kernel
      have hl : raw32757step0Labels = raw32757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32757 raw32757Labels permutation346 hz
    mixedMoment B raw32757step0 raw32757step0Labels = mixedMoment B raw32757step1 raw32757step1Labels := by
      have ha : raw32757step1 = (fun i j => raw32757step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32757step1 raw32757step0; decide +kernel
      have hl : raw32757step1Labels = raw32757step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32757step0 raw32757step0Labels permutation35 permutation2
    _ = mixedMoment B node5164 node5164Labels := by rfl

def raw32758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32758step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32758 raw32758Labels = mixedMoment B node4976 node4976Labels := by
  calc
    mixedMoment B raw32758 raw32758Labels = mixedMoment B raw32758step0 raw32758step0Labels := by
      have hz : ∀ j, raw32758 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32758step0 = (fun i j => raw32758 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32758step0 raw32758; decide +kernel
      have hl : raw32758step0Labels = raw32758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32758 raw32758Labels permutation346 hz
    _ = mixedMoment B node4976 node4976Labels := by rfl

def raw32759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32759 raw32759Labels = mixedMoment B node5116 node5116Labels := by
  calc
    _ = mixedMoment B node5116 node5116Labels := by rfl

def raw32760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32760step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32760 raw32760Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw32760 raw32760Labels = mixedMoment B raw32760step0 raw32760step0Labels := by
      have hz : ∀ j, raw32760 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32760step0 = (fun i j => raw32760 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32760step0 raw32760; decide +kernel
      have hl : raw32760step0Labels = raw32760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32760 raw32760Labels permutation346 hz
    _ = mixedMoment B node5151 node5151Labels := by rfl

def raw32761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw32761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw32761step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw32761step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32761 raw32761Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw32761 raw32761Labels = mixedMoment B raw32761step0 raw32761step0Labels := by
      have hz : ∀ j, raw32761 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32761step0 = (fun i j => raw32761 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32761step0 raw32761; decide +kernel
      have hl : raw32761step0Labels = raw32761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32761 raw32761Labels permutation346 hz
    mixedMoment B raw32761step0 raw32761step0Labels = mixedMoment B raw32761step1 raw32761step1Labels := by
      have ha : raw32761step1 = (fun i j => raw32761step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32761step1 raw32761step0; decide +kernel
      have hl : raw32761step1Labels = raw32761step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32761step0 raw32761step0Labels permutation33 permutation2
    _ = mixedMoment B node5173 node5173Labels := by rfl

def raw32762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32762step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw32762step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32762 raw32762Labels = mixedMoment B node4965 node4965Labels := by
  calc
    mixedMoment B raw32762 raw32762Labels = mixedMoment B raw32762step0 raw32762step0Labels := by
      have hz : ∀ j, raw32762 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32762step0 = (fun i j => raw32762 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32762step0 raw32762; decide +kernel
      have hl : raw32762step0Labels = raw32762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32762 raw32762Labels permutation346 hz
    mixedMoment B raw32762step0 raw32762step0Labels = mixedMoment B raw32762step1 raw32762step1Labels := by
      have ha : raw32762step1 = (fun i j => raw32762step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32762step1 raw32762step0; decide +kernel
      have hl : raw32762step1Labels = raw32762step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32762step0 raw32762step0Labels permutation34 permutation2
    _ = mixedMoment B node4965 node4965Labels := by rfl

def raw32763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 1, 2]]
def raw32763step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32763step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32763 raw32763Labels = mixedMoment B node5041 node5041Labels := by
  calc
    mixedMoment B raw32763 raw32763Labels = mixedMoment B raw32763step0 raw32763step0Labels := by
      have ha : raw32763step0 = (fun i j => raw32763 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32763step0 raw32763; decide +kernel
      have hl : raw32763step0Labels = raw32763Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32763 raw32763Labels permutation662 permutation2
    mixedMoment B raw32763step0 raw32763step0Labels = mixedMoment B raw32763step1 raw32763step1Labels := by
      have ha : raw32763step1 = -raw32763step0 := by apply Matrix.ext; change ∀ i j, raw32763step1 i j = -(raw32763step0 i j); unfold raw32763step1 raw32763step0; decide +kernel
      have hl : raw32763step1Labels = raw32763step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5041 node5041Labels := by rfl

def raw32764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32764step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32764 raw32764Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw32764 raw32764Labels = mixedMoment B raw32764step0 raw32764step0Labels := by
      have hz : ∀ j, raw32764 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32764step0 = (fun i j => raw32764 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32764step0 raw32764; decide +kernel
      have hl : raw32764step0Labels = raw32764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32764 raw32764Labels permutation346 hz
    _ = mixedMoment B node5147 node5147Labels := by rfl

def raw32765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw32765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw32765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw32765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32765step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw32765step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32765 raw32765Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw32765 raw32765Labels = mixedMoment B raw32765step0 raw32765step0Labels := by
      have hz : ∀ j, raw32765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32765step0 = (fun i j => raw32765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32765step0 raw32765; decide +kernel
      have hl : raw32765step0Labels = raw32765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32765 raw32765Labels permutation346 hz
    mixedMoment B raw32765step0 raw32765step0Labels = mixedMoment B raw32765step1 raw32765step1Labels := by
      have ha : raw32765step1 = (fun i j => raw32765step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32765step1 raw32765step0; decide +kernel
      have hl : raw32765step1Labels = raw32765step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32765step0 raw32765step0Labels permutation145 permutation2
    mixedMoment B raw32765step1 raw32765step1Labels = mixedMoment B raw32765step2 raw32765step2Labels := by
      have ha : raw32765step2 = -raw32765step1 := by apply Matrix.ext; change ∀ i j, raw32765step2 i j = -(raw32765step1 i j); unfold raw32765step2 raw32765step1; decide +kernel
      have hl : raw32765step2Labels = raw32765step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw32766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32766Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32766step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32766step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32766step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32766 raw32766Labels = mixedMoment B node3811 node3811Labels := by
  calc
    mixedMoment B raw32766 raw32766Labels = mixedMoment B raw32766step0 raw32766step0Labels := by
      have hz : ∀ j, raw32766 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32766step0 = (fun i j => raw32766 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32766step0 raw32766; decide +kernel
      have hl : raw32766step0Labels = raw32766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32766 raw32766Labels permutation346 hz
    mixedMoment B raw32766step0 raw32766step0Labels = mixedMoment B raw32766step1 raw32766step1Labels := by
      have ha : raw32766step1 = (fun i j => raw32766step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32766step1 raw32766step0; decide +kernel
      have hl : raw32766step1Labels = raw32766step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32766step0 raw32766step0Labels permutation143 permutation7
    mixedMoment B raw32766step1 raw32766step1Labels = mixedMoment B raw32766step2 raw32766step2Labels := by
      have ha : raw32766step2 = raw32766step1 := by apply Matrix.ext; unfold raw32766step2 raw32766step1; decide +kernel
      have hl : raw32766step1Labels = labelEmbedding1 ∘ raw32766step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32766step1 raw32766step1Labels raw32766step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3811 node3811Labels := by rfl

def raw32767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32767Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32767step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32767step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32767step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32767 raw32767Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw32767 raw32767Labels = mixedMoment B raw32767step0 raw32767step0Labels := by
      have ha : raw32767step0 = (fun i j => raw32767 (permutation653 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32767step0 raw32767; decide +kernel
      have hl : raw32767step0Labels = raw32767Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32767 raw32767Labels permutation653 permutation7
    mixedMoment B raw32767step0 raw32767step0Labels = mixedMoment B raw32767step1 raw32767step1Labels := by
      have ha : raw32767step1 = raw32767step0 := by apply Matrix.ext; unfold raw32767step1 raw32767step0; decide +kernel
      have hl : raw32767step0Labels = labelEmbedding1 ∘ raw32767step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32767step0 raw32767step0Labels raw32767step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3799 node3799Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
