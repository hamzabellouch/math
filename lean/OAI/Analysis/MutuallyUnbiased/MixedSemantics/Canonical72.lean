import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw9216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9216Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9216step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9216step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9216step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9216step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9216 raw9216Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw9216 raw9216Labels = mixedMoment B raw9216step0 raw9216step0Labels := by
      have hz : ∀ j, raw9216 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9216step0 = (fun i j => raw9216 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9216step0 raw9216; decide +kernel
      have hl : raw9216step0Labels = raw9216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9216 raw9216Labels permutation265 hz
    mixedMoment B raw9216step0 raw9216step0Labels = mixedMoment B raw9216step1 raw9216step1Labels := by
      have ha : raw9216step1 = (fun i j => raw9216step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9216step1 raw9216step0; decide +kernel
      have hl : raw9216step1Labels = raw9216step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9216step0 raw9216step0Labels permutation149 permutation7
    mixedMoment B raw9216step1 raw9216step1Labels = mixedMoment B raw9216step2 raw9216step2Labels := by
      have ha : raw9216step2 = raw9216step1 := by apply Matrix.ext; unfold raw9216step2 raw9216step1; decide +kernel
      have hl : raw9216step1Labels = labelEmbedding1 ∘ raw9216step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9216step1 raw9216step1Labels raw9216step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

def raw9217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9217Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9217step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw9217step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9217step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9217step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9217step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9217step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9217 raw9217Labels = mixedMoment B node3543 node3543Labels := by
  calc
    mixedMoment B raw9217 raw9217Labels = mixedMoment B raw9217step0 raw9217step0Labels := by
      have hz : ∀ j, raw9217 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9217step0 = (fun i j => raw9217 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9217step0 raw9217; decide +kernel
      have hl : raw9217step0Labels = raw9217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9217 raw9217Labels permutation265 hz
    mixedMoment B raw9217step0 raw9217step0Labels = mixedMoment B raw9217step1 raw9217step1Labels := by
      have ha : raw9217step1 = (fun i j => raw9217step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9217step1 raw9217step0; decide +kernel
      have hl : raw9217step1Labels = raw9217step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9217step0 raw9217step0Labels permutation44 permutation5
    mixedMoment B raw9217step1 raw9217step1Labels = mixedMoment B raw9217step2 raw9217step2Labels := by
      have ha : raw9217step2 = -raw9217step1 := by apply Matrix.ext; change ∀ i j, raw9217step2 i j = -(raw9217step1 i j); unfold raw9217step2 raw9217step1; decide +kernel
      have hl : raw9217step2Labels = raw9217step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9217step2 raw9217step2Labels = mixedMoment B raw9217step3 raw9217step3Labels := by
      have ha : raw9217step3 = raw9217step2 := by apply Matrix.ext; unfold raw9217step3 raw9217step2; decide +kernel
      have hl : raw9217step2Labels = labelEmbedding1 ∘ raw9217step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9217step2 raw9217step2Labels raw9217step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3543 node3543Labels := by rfl

def raw9218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9218 raw9218Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw9218 raw9218Labels = mixedMoment B raw9218step0 raw9218step0Labels := by
      have hz : ∀ j, raw9218 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9218step0 = (fun i j => raw9218 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9218step0 raw9218; decide +kernel
      have hl : raw9218step0Labels = raw9218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9218 raw9218Labels permutation265 hz
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw9219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9219Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9219step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9219step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9219step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9219 raw9219Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw9219 raw9219Labels = mixedMoment B raw9219step0 raw9219step0Labels := by
      have ha : raw9219step0 = (fun i j => raw9219 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9219step0 raw9219; decide +kernel
      have hl : raw9219step0Labels = raw9219Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9219 raw9219Labels permutation682 permutation2
    mixedMoment B raw9219step0 raw9219step0Labels = mixedMoment B raw9219step1 raw9219step1Labels := by
      have ha : raw9219step1 = -raw9219step0 := by apply Matrix.ext; change ∀ i j, raw9219step1 i j = -(raw9219step0 i j); unfold raw9219step1 raw9219step0; decide +kernel
      have hl : raw9219step1Labels = raw9219step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3800 node3800Labels := by rfl

def raw9220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9220Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9220step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw9220step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9220step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9220 raw9220Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw9220 raw9220Labels = mixedMoment B raw9220step0 raw9220step0Labels := by
      have hz : ∀ j, raw9220 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9220step0 = (fun i j => raw9220 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9220step0 raw9220; decide +kernel
      have hl : raw9220step0Labels = raw9220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9220 raw9220Labels permutation265 hz
    mixedMoment B raw9220step0 raw9220step0Labels = mixedMoment B raw9220step1 raw9220step1Labels := by
      have ha : raw9220step1 = (fun i j => raw9220step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9220step1 raw9220step0; decide +kernel
      have hl : raw9220step1Labels = raw9220step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9220step0 raw9220step0Labels permutation151 permutation2
    mixedMoment B raw9220step1 raw9220step1Labels = mixedMoment B raw9220step2 raw9220step2Labels := by
      have ha : raw9220step2 = -raw9220step1 := by apply Matrix.ext; change ∀ i j, raw9220step2 i j = -(raw9220step1 i j); unfold raw9220step2 raw9220step1; decide +kernel
      have hl : raw9220step2Labels = raw9220step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3808 node3808Labels := by rfl

def raw9221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9221Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9221step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9221step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw9221step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9221step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9221step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9221 raw9221Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw9221 raw9221Labels = mixedMoment B raw9221step0 raw9221step0Labels := by
      have hz : ∀ j, raw9221 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9221step0 = (fun i j => raw9221 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9221step0 raw9221; decide +kernel
      have hl : raw9221step0Labels = raw9221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9221 raw9221Labels permutation265 hz
    mixedMoment B raw9221step0 raw9221step0Labels = mixedMoment B raw9221step1 raw9221step1Labels := by
      have ha : raw9221step1 = (fun i j => raw9221step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9221step1 raw9221step0; decide +kernel
      have hl : raw9221step1Labels = raw9221step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9221step0 raw9221step0Labels permutation149 permutation2
    mixedMoment B raw9221step1 raw9221step1Labels = mixedMoment B raw9221step2 raw9221step2Labels := by
      have ha : raw9221step2 = -raw9221step1 := by apply Matrix.ext; change ∀ i j, raw9221step2 i j = -(raw9221step1 i j); unfold raw9221step2 raw9221step1; decide +kernel
      have hl : raw9221step2Labels = raw9221step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3808 node3808Labels := by rfl

def raw9222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9222Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9222step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw9222step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9222step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw9222step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9222 raw9222Labels = mixedMoment B node3902 node3902Labels := by
  calc
    mixedMoment B raw9222 raw9222Labels = mixedMoment B raw9222step0 raw9222step0Labels := by
      have hz : ∀ j, raw9222 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9222step0 = (fun i j => raw9222 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9222step0 raw9222; decide +kernel
      have hl : raw9222step0Labels = raw9222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9222 raw9222Labels permutation265 hz
    mixedMoment B raw9222step0 raw9222step0Labels = mixedMoment B raw9222step1 raw9222step1Labels := by
      have ha : raw9222step1 = (fun i j => raw9222step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9222step1 raw9222step0; decide +kernel
      have hl : raw9222step1Labels = raw9222step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9222step0 raw9222step0Labels permutation149 permutation2
    mixedMoment B raw9222step1 raw9222step1Labels = mixedMoment B raw9222step2 raw9222step2Labels := by
      have ha : raw9222step2 = -raw9222step1 := by apply Matrix.ext; change ∀ i j, raw9222step2 i j = -(raw9222step1 i j); unfold raw9222step2 raw9222step1; decide +kernel
      have hl : raw9222step2Labels = raw9222step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3902 node3902Labels := by rfl

def raw9223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9223Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9223step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9223 raw9223Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw9223 raw9223Labels = mixedMoment B raw9223step0 raw9223step0Labels := by
      have hz : ∀ j, raw9223 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9223step0 = (fun i j => raw9223 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9223step0 raw9223; decide +kernel
      have hl : raw9223step0Labels = raw9223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9223 raw9223Labels permutation265 hz
    _ = mixedMoment B node4010 node4010Labels := by rfl

def raw9224 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw9224Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9224step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw9224step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9224step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw9224step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw9224step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw9224step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical9224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9224 raw9224Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw9224 raw9224Labels = mixedMoment B raw9224step0 raw9224step0Labels := by
      have hz : ∀ j, raw9224 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9224step0 = (fun i j => raw9224 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9224step0 raw9224; decide +kernel
      have hl : raw9224step0Labels = raw9224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9224 raw9224Labels permutation265 hz
    mixedMoment B raw9224step0 raw9224step0Labels = mixedMoment B raw9224step1 raw9224step1Labels := by
      have ha : raw9224step1 = (fun i j => raw9224step0 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw9224step1 raw9224step0; decide +kernel
      have hl : raw9224step1Labels = raw9224step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9224step0 raw9224step0Labels permutation146 permutation0
    mixedMoment B raw9224step1 raw9224step1Labels = mixedMoment B raw9224step2 raw9224step2Labels := by
      have ha : raw9224step2 = -raw9224step1 := by apply Matrix.ext; change ∀ i j, raw9224step2 i j = -(raw9224step1 i j); unfold raw9224step2 raw9224step1; decide +kernel
      have hl : raw9224step2Labels = raw9224step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw9225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9225Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9225step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9225 raw9225Labels = mixedMoment B node1383 node1383Labels := by
  calc
    mixedMoment B raw9225 raw9225Labels = mixedMoment B raw9225step0 raw9225step0Labels := by
      have ha : raw9225step0 = (fun i j => raw9225 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9225step0 raw9225; decide +kernel
      have hl : raw9225step0Labels = raw9225Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9225 raw9225Labels permutation182 permutation2
    _ = mixedMoment B node1383 node1383Labels := by rfl

def raw9226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9226Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9226step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9226step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9226 raw9226Labels = mixedMoment B node1406 node1406Labels := by
  calc
    mixedMoment B raw9226 raw9226Labels = mixedMoment B raw9226step0 raw9226step0Labels := by
      have hz : ∀ j, raw9226 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9226step0 = (fun i j => raw9226 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9226step0 raw9226; decide +kernel
      have hl : raw9226step0Labels = raw9226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9226 raw9226Labels permutation265 hz
    mixedMoment B raw9226step0 raw9226step0Labels = mixedMoment B raw9226step1 raw9226step1Labels := by
      have ha : raw9226step1 = (fun i j => raw9226step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9226step1 raw9226step0; decide +kernel
      have hl : raw9226step1Labels = raw9226step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9226step0 raw9226step0Labels permutation38 permutation2
    _ = mixedMoment B node1406 node1406Labels := by rfl

def raw9227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9227step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9227 raw9227Labels = mixedMoment B node1406 node1406Labels := by
  calc
    mixedMoment B raw9227 raw9227Labels = mixedMoment B raw9227step0 raw9227step0Labels := by
      have hz : ∀ j, raw9227 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9227step0 = (fun i j => raw9227 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9227step0 raw9227; decide +kernel
      have hl : raw9227step0Labels = raw9227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9227 raw9227Labels permutation265 hz
    _ = mixedMoment B node1406 node1406Labels := by rfl

def raw9228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9228Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9228step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9228 raw9228Labels = mixedMoment B node1391 node1391Labels := by
  calc
    mixedMoment B raw9228 raw9228Labels = mixedMoment B raw9228step0 raw9228step0Labels := by
      have hz : ∀ j, raw9228 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9228step0 = (fun i j => raw9228 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9228step0 raw9228; decide +kernel
      have hl : raw9228step0Labels = raw9228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9228 raw9228Labels permutation265 hz
    _ = mixedMoment B node1391 node1391Labels := by rfl

def raw9229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9229Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9229step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9229 raw9229Labels = mixedMoment B node1388 node1388Labels := by
  calc
    mixedMoment B raw9229 raw9229Labels = mixedMoment B raw9229step0 raw9229step0Labels := by
      have hz : ∀ j, raw9229 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9229step0 = (fun i j => raw9229 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9229step0 raw9229; decide +kernel
      have hl : raw9229step0Labels = raw9229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9229 raw9229Labels permutation265 hz
    _ = mixedMoment B node1388 node1388Labels := by rfl

def raw9230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9230Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9230step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9230 raw9230Labels = mixedMoment B node2984 node2984Labels := by
  calc
    mixedMoment B raw9230 raw9230Labels = mixedMoment B raw9230step0 raw9230step0Labels := by
      have ha : raw9230step0 = (fun i j => raw9230 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9230step0 raw9230; decide +kernel
      have hl : raw9230step0Labels = raw9230Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9230 raw9230Labels permutation158 permutation2
    _ = mixedMoment B node2984 node2984Labels := by rfl

def raw9231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9231Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9231 raw9231Labels = mixedMoment B node2984 node2984Labels := by
  calc
    _ = mixedMoment B node2984 node2984Labels := by rfl

def raw9232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9232Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9232 raw9232Labels = mixedMoment B node2981 node2981Labels := by
  calc
    _ = mixedMoment B node2981 node2981Labels := by rfl

def raw9233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9233Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9233step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw9233step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9233step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9233step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9233 raw9233Labels = mixedMoment B node2470 node2470Labels := by
  calc
    mixedMoment B raw9233 raw9233Labels = mixedMoment B raw9233step0 raw9233step0Labels := by
      have ha : raw9233step0 = (fun i j => raw9233 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9233step0 raw9233; decide +kernel
      have hl : raw9233step0Labels = raw9233Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9233 raw9233Labels permutation682 permutation2
    mixedMoment B raw9233step0 raw9233step0Labels = mixedMoment B raw9233step1 raw9233step1Labels := by
      have ha : raw9233step1 = -raw9233step0 := by apply Matrix.ext; change ∀ i j, raw9233step1 i j = -(raw9233step0 i j); unfold raw9233step1 raw9233step0; decide +kernel
      have hl : raw9233step1Labels = raw9233step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2470 node2470Labels := by rfl

def raw9234 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9234step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9234step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9234step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9234step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9234step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9234 raw9234Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw9234 raw9234Labels = mixedMoment B raw9234step0 raw9234step0Labels := by
      have hz : ∀ j, raw9234 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9234step0 = (fun i j => raw9234 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9234step0 raw9234; decide +kernel
      have hl : raw9234step0Labels = raw9234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9234 raw9234Labels permutation434 hz
    mixedMoment B raw9234step0 raw9234step0Labels = mixedMoment B raw9234step1 raw9234step1Labels := by
      have hz : ∀ j, raw9234step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9234step1 = (fun i j => raw9234step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9234step1 raw9234step0; decide +kernel
      have hl : raw9234step1Labels = raw9234step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9234step0 raw9234step0Labels permutation56 hz
    mixedMoment B raw9234step1 raw9234step1Labels = mixedMoment B raw9234step2 raw9234step2Labels := by
      have ha : raw9234step2 = (fun i j => raw9234step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9234step2 raw9234step1; decide +kernel
      have hl : raw9234step2Labels = raw9234step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9234step1 raw9234step1Labels permutation8 permutation7
    mixedMoment B raw9234step2 raw9234step2Labels = mixedMoment B raw9234step3 raw9234step3Labels := by
      have ha : raw9234step3 = raw9234step2 := by apply Matrix.ext; unfold raw9234step3 raw9234step2; decide +kernel
      have hl : raw9234step2Labels = labelEmbedding10 ∘ raw9234step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9234step2 raw9234step2Labels raw9234step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw9235 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9235 raw9235Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw9235 raw9235Labels = mixedMoment B raw9235step0 raw9235step0Labels := by
      have hz : ∀ j, raw9235 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9235step0 = (fun i j => raw9235 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9235step0 raw9235; decide +kernel
      have hl : raw9235step0Labels = raw9235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9235 raw9235Labels permutation265 hz
    mixedMoment B raw9235step0 raw9235step0Labels = mixedMoment B raw9235step1 raw9235step1Labels := by
      have ha : raw9235step1 = (fun i j => raw9235step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9235step1 raw9235step0; decide +kernel
      have hl : raw9235step1Labels = raw9235step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9235step0 raw9235step0Labels permutation149 permutation2
    _ = mixedMoment B node5099 node5099Labels := by rfl

def raw9236 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9236step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9236step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9236 raw9236Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw9236 raw9236Labels = mixedMoment B raw9236step0 raw9236step0Labels := by
      have ha : raw9236step0 = (fun i j => raw9236 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9236step0 raw9236; decide +kernel
      have hl : raw9236step0Labels = raw9236Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9236 raw9236Labels permutation152 permutation6
    mixedMoment B raw9236step0 raw9236step0Labels = mixedMoment B raw9236step1 raw9236step1Labels := by
      have ha : raw9236step1 = raw9236step0 := by apply Matrix.ext; unfold raw9236step1 raw9236step0; decide +kernel
      have hl : raw9236step0Labels = labelEmbedding9 ∘ raw9236step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9236step0 raw9236step0Labels raw9236step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4885 node4885Labels := by rfl

def raw9237 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9237step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9237step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9237step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw9237step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw9237step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw9237step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9237 raw9237Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw9237 raw9237Labels = mixedMoment B raw9237step0 raw9237step0Labels := by
      have hz : ∀ j, raw9237 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9237step0 = (fun i j => raw9237 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9237step0 raw9237; decide +kernel
      have hl : raw9237step0Labels = raw9237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9237 raw9237Labels permutation434 hz
    mixedMoment B raw9237step0 raw9237step0Labels = mixedMoment B raw9237step1 raw9237step1Labels := by
      have hz : ∀ j, raw9237step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9237step1 = (fun i j => raw9237step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9237step1 raw9237step0; decide +kernel
      have hl : raw9237step1Labels = raw9237step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9237step0 raw9237step0Labels permutation56 hz
    mixedMoment B raw9237step1 raw9237step1Labels = mixedMoment B raw9237step2 raw9237step2Labels := by
      have ha : raw9237step2 = (fun i j => raw9237step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9237step2 raw9237step1; decide +kernel
      have hl : raw9237step2Labels = raw9237step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9237step1 raw9237step1Labels permutation8 permutation6
    mixedMoment B raw9237step2 raw9237step2Labels = mixedMoment B raw9237step3 raw9237step3Labels := by
      have ha : raw9237step3 = raw9237step2 := by apply Matrix.ext; unfold raw9237step3 raw9237step2; decide +kernel
      have hl : raw9237step2Labels = labelEmbedding9 ∘ raw9237step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9237step2 raw9237step2Labels raw9237step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw9238 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw9238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9238 raw9238Labels = mixedMoment B node5103 node5103Labels := by
  calc
    mixedMoment B raw9238 raw9238Labels = mixedMoment B raw9238step0 raw9238step0Labels := by
      have hz : ∀ j, raw9238 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9238step0 = (fun i j => raw9238 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9238step0 raw9238; decide +kernel
      have hl : raw9238step0Labels = raw9238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9238 raw9238Labels permutation265 hz
    mixedMoment B raw9238step0 raw9238step0Labels = mixedMoment B raw9238step1 raw9238step1Labels := by
      have ha : raw9238step1 = (fun i j => raw9238step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9238step1 raw9238step0; decide +kernel
      have hl : raw9238step1Labels = raw9238step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9238step0 raw9238step0Labels permutation150 permutation2
    _ = mixedMoment B node5103 node5103Labels := by rfl

def raw9239 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9239Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9239step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9239step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9239step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9239step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9239step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9239 raw9239Labels = mixedMoment B node3112 node3112Labels := by
  calc
    mixedMoment B raw9239 raw9239Labels = mixedMoment B raw9239step0 raw9239step0Labels := by
      have hz : ∀ j, raw9239 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9239step0 = (fun i j => raw9239 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9239step0 raw9239; decide +kernel
      have hl : raw9239step0Labels = raw9239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9239 raw9239Labels permutation434 hz
    mixedMoment B raw9239step0 raw9239step0Labels = mixedMoment B raw9239step1 raw9239step1Labels := by
      have hz : ∀ j, raw9239step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9239step1 = (fun i j => raw9239step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9239step1 raw9239step0; decide +kernel
      have hl : raw9239step1Labels = raw9239step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9239step0 raw9239step0Labels permutation56 hz
    mixedMoment B raw9239step1 raw9239step1Labels = mixedMoment B raw9239step2 raw9239step2Labels := by
      have ha : raw9239step2 = (fun i j => raw9239step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9239step2 raw9239step1; decide +kernel
      have hl : raw9239step2Labels = raw9239step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9239step1 raw9239step1Labels permutation8 permutation6
    _ = mixedMoment B node3112 node3112Labels := by rfl

def raw9240 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9240Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9240step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9240step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9240 raw9240Labels = mixedMoment B node3003 node3003Labels := by
  calc
    mixedMoment B raw9240 raw9240Labels = mixedMoment B raw9240step0 raw9240step0Labels := by
      have hz : ∀ j, raw9240 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9240step0 = (fun i j => raw9240 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9240step0 raw9240; decide +kernel
      have hl : raw9240step0Labels = raw9240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9240 raw9240Labels permutation265 hz
    mixedMoment B raw9240step0 raw9240step0Labels = mixedMoment B raw9240step1 raw9240step1Labels := by
      have ha : raw9240step1 = (fun i j => raw9240step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9240step1 raw9240step0; decide +kernel
      have hl : raw9240step1Labels = raw9240step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9240step0 raw9240step0Labels permutation149 permutation3
    _ = mixedMoment B node3003 node3003Labels := by rfl

def raw9241 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9241Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9241step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9241 raw9241Labels = mixedMoment B node2233 node2233Labels := by
  calc
    mixedMoment B raw9241 raw9241Labels = mixedMoment B raw9241step0 raw9241step0Labels := by
      have ha : raw9241step0 = (fun i j => raw9241 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9241step0 raw9241; decide +kernel
      have hl : raw9241step0Labels = raw9241Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9241 raw9241Labels permutation152 permutation6
    _ = mixedMoment B node2233 node2233Labels := by rfl

def raw9242 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9242Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9242step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9242step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9242step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw9242step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9242 raw9242Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw9242 raw9242Labels = mixedMoment B raw9242step0 raw9242step0Labels := by
      have hz : ∀ j, raw9242 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9242step0 = (fun i j => raw9242 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9242step0 raw9242; decide +kernel
      have hl : raw9242step0Labels = raw9242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9242 raw9242Labels permutation434 hz
    mixedMoment B raw9242step0 raw9242step0Labels = mixedMoment B raw9242step1 raw9242step1Labels := by
      have hz : ∀ j, raw9242step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9242step1 = (fun i j => raw9242step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9242step1 raw9242step0; decide +kernel
      have hl : raw9242step1Labels = raw9242step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9242step0 raw9242step0Labels permutation56 hz
    mixedMoment B raw9242step1 raw9242step1Labels = mixedMoment B raw9242step2 raw9242step2Labels := by
      have ha : raw9242step2 = (fun i j => raw9242step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9242step2 raw9242step1; decide +kernel
      have hl : raw9242step2Labels = raw9242step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9242step1 raw9242step1Labels permutation8 permutation6
    _ = mixedMoment B node2776 node2776Labels := by rfl

def raw9243 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9243Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9243step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw9243step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9243 raw9243Labels = mixedMoment B node2759 node2759Labels := by
  calc
    mixedMoment B raw9243 raw9243Labels = mixedMoment B raw9243step0 raw9243step0Labels := by
      have hz : ∀ j, raw9243 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9243step0 = (fun i j => raw9243 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9243step0 raw9243; decide +kernel
      have hl : raw9243step0Labels = raw9243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9243 raw9243Labels permutation265 hz
    mixedMoment B raw9243step0 raw9243step0Labels = mixedMoment B raw9243step1 raw9243step1Labels := by
      have ha : raw9243step1 = (fun i j => raw9243step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9243step1 raw9243step0; decide +kernel
      have hl : raw9243step1Labels = raw9243step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9243step0 raw9243step0Labels permutation38 permutation6
    _ = mixedMoment B node2759 node2759Labels := by rfl

def raw9244 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9244Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9244step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw9244step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9244 raw9244Labels = mixedMoment B node2759 node2759Labels := by
  calc
    mixedMoment B raw9244 raw9244Labels = mixedMoment B raw9244step0 raw9244step0Labels := by
      have hz : ∀ j, raw9244 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9244step0 = (fun i j => raw9244 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9244step0 raw9244; decide +kernel
      have hl : raw9244step0Labels = raw9244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9244 raw9244Labels permutation265 hz
    mixedMoment B raw9244step0 raw9244step0Labels = mixedMoment B raw9244step1 raw9244step1Labels := by
      have ha : raw9244step1 = (fun i j => raw9244step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9244step1 raw9244step0; decide +kernel
      have hl : raw9244step1Labels = raw9244step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9244step0 raw9244step0Labels permutation32 permutation6
    _ = mixedMoment B node2759 node2759Labels := by rfl

def raw9245 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9245Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9245step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9245step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9245step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9245step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9245step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9245step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9245 raw9245Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw9245 raw9245Labels = mixedMoment B raw9245step0 raw9245step0Labels := by
      have hz : ∀ j, raw9245 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9245step0 = (fun i j => raw9245 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9245step0 raw9245; decide +kernel
      have hl : raw9245step0Labels = raw9245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9245 raw9245Labels permutation434 hz
    mixedMoment B raw9245step0 raw9245step0Labels = mixedMoment B raw9245step1 raw9245step1Labels := by
      have hz : ∀ j, raw9245step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9245step1 = (fun i j => raw9245step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9245step1 raw9245step0; decide +kernel
      have hl : raw9245step1Labels = raw9245step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9245step0 raw9245step0Labels permutation56 hz
    mixedMoment B raw9245step1 raw9245step1Labels = mixedMoment B raw9245step2 raw9245step2Labels := by
      have ha : raw9245step2 = (fun i j => raw9245step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9245step2 raw9245step1; decide +kernel
      have hl : raw9245step2Labels = raw9245step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9245step1 raw9245step1Labels permutation8 permutation7
    mixedMoment B raw9245step2 raw9245step2Labels = mixedMoment B raw9245step3 raw9245step3Labels := by
      have ha : raw9245step3 = raw9245step2 := by apply Matrix.ext; unfold raw9245step3 raw9245step2; decide +kernel
      have hl : raw9245step2Labels = labelEmbedding1 ∘ raw9245step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9245step2 raw9245step2Labels raw9245step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2742 node2742Labels := by rfl

def raw9246 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9246Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9246step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw9246step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9246step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw9246step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9246 raw9246Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw9246 raw9246Labels = mixedMoment B raw9246step0 raw9246step0Labels := by
      have hz : ∀ j, raw9246 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9246step0 = (fun i j => raw9246 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9246step0 raw9246; decide +kernel
      have hl : raw9246step0Labels = raw9246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9246 raw9246Labels permutation265 hz
    mixedMoment B raw9246step0 raw9246step0Labels = mixedMoment B raw9246step1 raw9246step1Labels := by
      have ha : raw9246step1 = (fun i j => raw9246step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9246step1 raw9246step0; decide +kernel
      have hl : raw9246step1Labels = raw9246step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9246step0 raw9246step0Labels permutation32 permutation7
    mixedMoment B raw9246step1 raw9246step1Labels = mixedMoment B raw9246step2 raw9246step2Labels := by
      have ha : raw9246step2 = raw9246step1 := by apply Matrix.ext; unfold raw9246step2 raw9246step1; decide +kernel
      have hl : raw9246step1Labels = labelEmbedding1 ∘ raw9246step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9246step1 raw9246step1Labels raw9246step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2704 node2704Labels := by rfl

def raw9247 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9247Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw9247step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9247step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw9247step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9247step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw9247step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9247 raw9247Labels = mixedMoment B node3221 node3221Labels := by
  calc
    mixedMoment B raw9247 raw9247Labels = mixedMoment B raw9247step0 raw9247step0Labels := by
      have ha : raw9247step0 = (fun i j => raw9247 (permutation260 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9247step0 raw9247; decide +kernel
      have hl : raw9247step0Labels = raw9247Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9247 raw9247Labels permutation260 permutation5
    mixedMoment B raw9247step0 raw9247step0Labels = mixedMoment B raw9247step1 raw9247step1Labels := by
      have ha : raw9247step1 = -raw9247step0 := by apply Matrix.ext; change ∀ i j, raw9247step1 i j = -(raw9247step0 i j); unfold raw9247step1 raw9247step0; decide +kernel
      have hl : raw9247step1Labels = raw9247step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9247step1 raw9247step1Labels = mixedMoment B raw9247step2 raw9247step2Labels := by
      have ha : raw9247step2 = raw9247step1 := by apply Matrix.ext; unfold raw9247step2 raw9247step1; decide +kernel
      have hl : raw9247step1Labels = labelEmbedding1 ∘ raw9247step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9247step1 raw9247step1Labels raw9247step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3221 node3221Labels := by rfl

def raw9248 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9248Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9248step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9248step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9248step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9248step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw9248step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9248step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw9248step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9248 raw9248Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw9248 raw9248Labels = mixedMoment B raw9248step0 raw9248step0Labels := by
      have hz : ∀ j, raw9248 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9248step0 = (fun i j => raw9248 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9248step0 raw9248; decide +kernel
      have hl : raw9248step0Labels = raw9248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9248 raw9248Labels permutation434 hz
    mixedMoment B raw9248step0 raw9248step0Labels = mixedMoment B raw9248step1 raw9248step1Labels := by
      have hz : ∀ j, raw9248step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9248step1 = (fun i j => raw9248step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9248step1 raw9248step0; decide +kernel
      have hl : raw9248step1Labels = raw9248step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9248step0 raw9248step0Labels permutation56 hz
    mixedMoment B raw9248step1 raw9248step1Labels = mixedMoment B raw9248step2 raw9248step2Labels := by
      have ha : raw9248step2 = (fun i j => raw9248step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9248step2 raw9248step1; decide +kernel
      have hl : raw9248step2Labels = raw9248step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9248step1 raw9248step1Labels permutation8 permutation7
    mixedMoment B raw9248step2 raw9248step2Labels = mixedMoment B raw9248step3 raw9248step3Labels := by
      have ha : raw9248step3 = raw9248step2 := by apply Matrix.ext; unfold raw9248step3 raw9248step2; decide +kernel
      have hl : raw9248step2Labels = labelEmbedding1 ∘ raw9248step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9248step2 raw9248step2Labels raw9248step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw9249 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9249Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9249step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw9249step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9249step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw9249step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9249 raw9249Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw9249 raw9249Labels = mixedMoment B raw9249step0 raw9249step0Labels := by
      have hz : ∀ j, raw9249 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9249step0 = (fun i j => raw9249 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9249step0 raw9249; decide +kernel
      have hl : raw9249step0Labels = raw9249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9249 raw9249Labels permutation265 hz
    mixedMoment B raw9249step0 raw9249step0Labels = mixedMoment B raw9249step1 raw9249step1Labels := by
      have ha : raw9249step1 = (fun i j => raw9249step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9249step1 raw9249step0; decide +kernel
      have hl : raw9249step1Labels = raw9249step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9249step0 raw9249step0Labels permutation32 permutation7
    mixedMoment B raw9249step1 raw9249step1Labels = mixedMoment B raw9249step2 raw9249step2Labels := by
      have ha : raw9249step2 = raw9249step1 := by apply Matrix.ext; unfold raw9249step2 raw9249step1; decide +kernel
      have hl : raw9249step1Labels = labelEmbedding1 ∘ raw9249step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9249step1 raw9249step1Labels raw9249step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3024 node3024Labels := by rfl

def raw9250 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9250Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9250step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9250step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw9250step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9250step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9250step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9250 raw9250Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw9250 raw9250Labels = mixedMoment B raw9250step0 raw9250step0Labels := by
      have hz : ∀ j, raw9250 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw9250step0 = (fun i j => raw9250 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw9250step0 raw9250; decide +kernel
      have hl : raw9250step0Labels = raw9250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9250 raw9250Labels permutation434 hz
    mixedMoment B raw9250step0 raw9250step0Labels = mixedMoment B raw9250step1 raw9250step1Labels := by
      have hz : ∀ j, raw9250step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9250step1 = (fun i j => raw9250step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9250step1 raw9250step0; decide +kernel
      have hl : raw9250step1Labels = raw9250step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9250step0 raw9250step0Labels permutation56 hz
    mixedMoment B raw9250step1 raw9250step1Labels = mixedMoment B raw9250step2 raw9250step2Labels := by
      have ha : raw9250step2 = -raw9250step1 := by apply Matrix.ext; change ∀ i j, raw9250step2 i j = -(raw9250step1 i j); unfold raw9250step2 raw9250step1; decide +kernel
      have hl : raw9250step2Labels = raw9250step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3547 node3547Labels := by rfl

def raw9251 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9251Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw9251step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9251step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9251 raw9251Labels = mixedMoment B node2509 node2509Labels := by
  calc
    mixedMoment B raw9251 raw9251Labels = mixedMoment B raw9251step0 raw9251step0Labels := by
      have hz : ∀ j, raw9251 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9251step0 = (fun i j => raw9251 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9251step0 raw9251; decide +kernel
      have hl : raw9251step0Labels = raw9251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9251 raw9251Labels permutation265 hz
    mixedMoment B raw9251step0 raw9251step0Labels = mixedMoment B raw9251step1 raw9251step1Labels := by
      have ha : raw9251step1 = (fun i j => raw9251step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9251step1 raw9251step0; decide +kernel
      have hl : raw9251step1Labels = raw9251step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9251step0 raw9251step0Labels permutation149 permutation2
    _ = mixedMoment B node2509 node2509Labels := by rfl

def raw9252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9252step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9252step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9252step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9252step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9252 raw9252Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw9252 raw9252Labels = mixedMoment B raw9252step0 raw9252step0Labels := by
      have ha : raw9252step0 = (fun i j => raw9252 (permutation668 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9252step0 raw9252; decide +kernel
      have hl : raw9252step0Labels = raw9252Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9252 raw9252Labels permutation668 permutation5
    mixedMoment B raw9252step0 raw9252step0Labels = mixedMoment B raw9252step1 raw9252step1Labels := by
      have ha : raw9252step1 = raw9252step0 := by apply Matrix.ext; unfold raw9252step1 raw9252step0; decide +kernel
      have hl : raw9252step0Labels = labelEmbedding8 ∘ raw9252step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9252step0 raw9252step0Labels raw9252step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw9253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9253step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9253step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9253step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9253 raw9253Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw9253 raw9253Labels = mixedMoment B raw9253step0 raw9253step0Labels := by
      have hz : ∀ j, raw9253 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9253step0 = (fun i j => raw9253 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9253step0 raw9253; decide +kernel
      have hl : raw9253step0Labels = raw9253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9253 raw9253Labels permutation265 hz
    mixedMoment B raw9253step0 raw9253step0Labels = mixedMoment B raw9253step1 raw9253step1Labels := by
      have ha : raw9253step1 = (fun i j => raw9253step0 (permutation147 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9253step1 raw9253step0; decide +kernel
      have hl : raw9253step1Labels = raw9253step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9253step0 raw9253step0Labels permutation147 permutation5
    mixedMoment B raw9253step1 raw9253step1Labels = mixedMoment B raw9253step2 raw9253step2Labels := by
      have ha : raw9253step2 = raw9253step1 := by apply Matrix.ext; unfold raw9253step2 raw9253step1; decide +kernel
      have hl : raw9253step1Labels = labelEmbedding8 ∘ raw9253step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9253step1 raw9253step1Labels raw9253step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw9254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9254step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9254step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9254step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9254step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9254 raw9254Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw9254 raw9254Labels = mixedMoment B raw9254step0 raw9254step0Labels := by
      have hz : ∀ j, raw9254 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9254step0 = (fun i j => raw9254 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9254step0 raw9254; decide +kernel
      have hl : raw9254step0Labels = raw9254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9254 raw9254Labels permutation265 hz
    mixedMoment B raw9254step0 raw9254step0Labels = mixedMoment B raw9254step1 raw9254step1Labels := by
      have ha : raw9254step1 = (fun i j => raw9254step0 (permutation146 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9254step1 raw9254step0; decide +kernel
      have hl : raw9254step1Labels = raw9254step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9254step0 raw9254step0Labels permutation146 permutation5
    mixedMoment B raw9254step1 raw9254step1Labels = mixedMoment B raw9254step2 raw9254step2Labels := by
      have ha : raw9254step2 = raw9254step1 := by apply Matrix.ext; unfold raw9254step2 raw9254step1; decide +kernel
      have hl : raw9254step1Labels = labelEmbedding8 ∘ raw9254step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9254step1 raw9254step1Labels raw9254step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw9255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw9255step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9255step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw9255step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9255 raw9255Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw9255 raw9255Labels = mixedMoment B raw9255step0 raw9255step0Labels := by
      have hz : ∀ j, raw9255 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9255step0 = (fun i j => raw9255 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9255step0 raw9255; decide +kernel
      have hl : raw9255step0Labels = raw9255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9255 raw9255Labels permutation265 hz
    mixedMoment B raw9255step0 raw9255step0Labels = mixedMoment B raw9255step1 raw9255step1Labels := by
      have ha : raw9255step1 = (fun i j => raw9255step0 (permutation128 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9255step1 raw9255step0; decide +kernel
      have hl : raw9255step1Labels = raw9255step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9255step0 raw9255step0Labels permutation128 permutation5
    mixedMoment B raw9255step1 raw9255step1Labels = mixedMoment B raw9255step2 raw9255step2Labels := by
      have ha : raw9255step2 = raw9255step1 := by apply Matrix.ext; unfold raw9255step2 raw9255step1; decide +kernel
      have hl : raw9255step1Labels = labelEmbedding8 ∘ raw9255step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9255step1 raw9255step1Labels raw9255step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw9256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9256step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw9256step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9256step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9256step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9256step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9256 raw9256Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw9256 raw9256Labels = mixedMoment B raw9256step0 raw9256step0Labels := by
      have hz : ∀ j, raw9256 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9256step0 = (fun i j => raw9256 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9256step0 raw9256; decide +kernel
      have hl : raw9256step0Labels = raw9256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9256 raw9256Labels permutation265 hz
    mixedMoment B raw9256step0 raw9256step0Labels = mixedMoment B raw9256step1 raw9256step1Labels := by
      have ha : raw9256step1 = (fun i j => raw9256step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9256step1 raw9256step0; decide +kernel
      have hl : raw9256step1Labels = raw9256step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9256step0 raw9256step0Labels permutation50 permutation7
    mixedMoment B raw9256step1 raw9256step1Labels = mixedMoment B raw9256step2 raw9256step2Labels := by
      have ha : raw9256step2 = -raw9256step1 := by apply Matrix.ext; change ∀ i j, raw9256step2 i j = -(raw9256step1 i j); unfold raw9256step2 raw9256step1; decide +kernel
      have hl : raw9256step2Labels = raw9256step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9256step2 raw9256step2Labels = mixedMoment B raw9256step3 raw9256step3Labels := by
      have ha : raw9256step3 = raw9256step2 := by apply Matrix.ext; unfold raw9256step3 raw9256step2; decide +kernel
      have hl : raw9256step2Labels = labelEmbedding10 ∘ raw9256step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9256step2 raw9256step2Labels raw9256step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw9257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw9257step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9257step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw9257step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9257 raw9257Labels = mixedMoment B node4579 node4579Labels := by
  calc
    mixedMoment B raw9257 raw9257Labels = mixedMoment B raw9257step0 raw9257step0Labels := by
      have ha : raw9257step0 = (fun i j => raw9257 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9257step0 raw9257; decide +kernel
      have hl : raw9257step0Labels = raw9257Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9257 raw9257Labels permutation184 permutation3
    mixedMoment B raw9257step0 raw9257step0Labels = mixedMoment B raw9257step1 raw9257step1Labels := by
      have ha : raw9257step1 = raw9257step0 := by apply Matrix.ext; unfold raw9257step1 raw9257step0; decide +kernel
      have hl : raw9257step0Labels = labelEmbedding6 ∘ raw9257step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9257step0 raw9257step0Labels raw9257step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4579 node4579Labels := by rfl

def raw9258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9258step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9258step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9258step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9258step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9258 raw9258Labels = mixedMoment B node5057 node5057Labels := by
  calc
    mixedMoment B raw9258 raw9258Labels = mixedMoment B raw9258step0 raw9258step0Labels := by
      have ha : raw9258step0 = (fun i j => raw9258 (permutation621 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9258step0 raw9258; decide +kernel
      have hl : raw9258step0Labels = raw9258Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9258 raw9258Labels permutation621 permutation5
    mixedMoment B raw9258step0 raw9258step0Labels = mixedMoment B raw9258step1 raw9258step1Labels := by
      have ha : raw9258step1 = raw9258step0 := by apply Matrix.ext; unfold raw9258step1 raw9258step0; decide +kernel
      have hl : raw9258step0Labels = labelEmbedding8 ∘ raw9258step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9258step0 raw9258step0Labels raw9258step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5057 node5057Labels := by rfl

def raw9259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9259step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9259step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9259 raw9259Labels = mixedMoment B node5057 node5057Labels := by
  calc
    mixedMoment B raw9259 raw9259Labels = mixedMoment B raw9259step0 raw9259step0Labels := by
      have ha : raw9259step0 = (fun i j => raw9259 (permutation619 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9259step0 raw9259; decide +kernel
      have hl : raw9259step0Labels = raw9259Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9259 raw9259Labels permutation619 permutation5
    mixedMoment B raw9259step0 raw9259step0Labels = mixedMoment B raw9259step1 raw9259step1Labels := by
      have ha : raw9259step1 = raw9259step0 := by apply Matrix.ext; unfold raw9259step1 raw9259step0; decide +kernel
      have hl : raw9259step0Labels = labelEmbedding8 ∘ raw9259step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9259step0 raw9259step0Labels raw9259step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5057 node5057Labels := by rfl

def raw9260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9260step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9260step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9260step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9260 raw9260Labels = mixedMoment B node5097 node5097Labels := by
  calc
    mixedMoment B raw9260 raw9260Labels = mixedMoment B raw9260step0 raw9260step0Labels := by
      have ha : raw9260step0 = (fun i j => raw9260 (permutation609 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9260step0 raw9260; decide +kernel
      have hl : raw9260step0Labels = raw9260Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9260 raw9260Labels permutation609 permutation5
    mixedMoment B raw9260step0 raw9260step0Labels = mixedMoment B raw9260step1 raw9260step1Labels := by
      have ha : raw9260step1 = raw9260step0 := by apply Matrix.ext; unfold raw9260step1 raw9260step0; decide +kernel
      have hl : raw9260step0Labels = labelEmbedding8 ∘ raw9260step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9260step0 raw9260step0Labels raw9260step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5097 node5097Labels := by rfl

def raw9261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9261step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw9261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9261 raw9261Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw9261 raw9261Labels = mixedMoment B raw9261step0 raw9261step0Labels := by
      have ha : raw9261step0 = (fun i j => raw9261 (permutation186 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9261step0 raw9261; decide +kernel
      have hl : raw9261step0Labels = raw9261Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9261 raw9261Labels permutation186 permutation2
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw9262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9262step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9262step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9262step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9262step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9262 raw9262Labels = mixedMoment B node4600 node4600Labels := by
  calc
    mixedMoment B raw9262 raw9262Labels = mixedMoment B raw9262step0 raw9262step0Labels := by
      have hz : ∀ j, raw9262 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9262step0 = (fun i j => raw9262 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9262step0 raw9262; decide +kernel
      have hl : raw9262step0Labels = raw9262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9262 raw9262Labels permutation265 hz
    mixedMoment B raw9262step0 raw9262step0Labels = mixedMoment B raw9262step1 raw9262step1Labels := by
      have ha : raw9262step1 = (fun i j => raw9262step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9262step1 raw9262step0; decide +kernel
      have hl : raw9262step1Labels = raw9262step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9262step0 raw9262step0Labels permutation38 permutation3
    mixedMoment B raw9262step1 raw9262step1Labels = mixedMoment B raw9262step2 raw9262step2Labels := by
      have ha : raw9262step2 = raw9262step1 := by apply Matrix.ext; unfold raw9262step2 raw9262step1; decide +kernel
      have hl : raw9262step1Labels = labelEmbedding6 ∘ raw9262step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9262step1 raw9262step1Labels raw9262step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4600 node4600Labels := by rfl

def raw9263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9263step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9263 raw9263Labels = mixedMoment B node5150 node5150Labels := by
  calc
    mixedMoment B raw9263 raw9263Labels = mixedMoment B raw9263step0 raw9263step0Labels := by
      have ha : raw9263step0 = (fun i j => raw9263 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9263step0 raw9263; decide +kernel
      have hl : raw9263step0Labels = raw9263Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9263 raw9263Labels permutation158 permutation2
    _ = mixedMoment B node5150 node5150Labels := by rfl

def raw9264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9264step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9264 raw9264Labels = mixedMoment B node5205 node5205Labels := by
  calc
    mixedMoment B raw9264 raw9264Labels = mixedMoment B raw9264step0 raw9264step0Labels := by
      have hz : ∀ j, raw9264 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9264step0 = (fun i j => raw9264 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9264step0 raw9264; decide +kernel
      have hl : raw9264step0Labels = raw9264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9264 raw9264Labels permutation265 hz
    mixedMoment B raw9264step0 raw9264step0Labels = mixedMoment B raw9264step1 raw9264step1Labels := by
      have ha : raw9264step1 = (fun i j => raw9264step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9264step1 raw9264step0; decide +kernel
      have hl : raw9264step1Labels = raw9264step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9264step0 raw9264step0Labels permutation38 permutation2
    _ = mixedMoment B node5205 node5205Labels := by rfl

def raw9265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9265step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9265step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9265step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9265step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9265 raw9265Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw9265 raw9265Labels = mixedMoment B raw9265step0 raw9265step0Labels := by
      have hz : ∀ j, raw9265 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9265step0 = (fun i j => raw9265 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9265step0 raw9265; decide +kernel
      have hl : raw9265step0Labels = raw9265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9265 raw9265Labels permutation265 hz
    mixedMoment B raw9265step0 raw9265step0Labels = mixedMoment B raw9265step1 raw9265step1Labels := by
      have ha : raw9265step1 = (fun i j => raw9265step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9265step1 raw9265step0; decide +kernel
      have hl : raw9265step1Labels = raw9265step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9265step0 raw9265step0Labels permutation137 permutation5
    mixedMoment B raw9265step1 raw9265step1Labels = mixedMoment B raw9265step2 raw9265step2Labels := by
      have ha : raw9265step2 = raw9265step1 := by apply Matrix.ext; unfold raw9265step2 raw9265step1; decide +kernel
      have hl : raw9265step1Labels = labelEmbedding8 ∘ raw9265step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9265step1 raw9265step1Labels raw9265step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw9266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9266step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9266step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9266 raw9266Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw9266 raw9266Labels = mixedMoment B raw9266step0 raw9266step0Labels := by
      have hz : ∀ j, raw9266 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9266step0 = (fun i j => raw9266 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9266step0 raw9266; decide +kernel
      have hl : raw9266step0Labels = raw9266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9266 raw9266Labels permutation265 hz
    mixedMoment B raw9266step0 raw9266step0Labels = mixedMoment B raw9266step1 raw9266step1Labels := by
      have ha : raw9266step1 = (fun i j => raw9266step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9266step1 raw9266step0; decide +kernel
      have hl : raw9266step1Labels = raw9266step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9266step0 raw9266step0Labels permutation42 permutation2
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw9267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9267step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9267step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9267 raw9267Labels = mixedMoment B node4600 node4600Labels := by
  calc
    mixedMoment B raw9267 raw9267Labels = mixedMoment B raw9267step0 raw9267step0Labels := by
      have hz : ∀ j, raw9267 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9267step0 = (fun i j => raw9267 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9267step0 raw9267; decide +kernel
      have hl : raw9267step0Labels = raw9267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9267 raw9267Labels permutation265 hz
    mixedMoment B raw9267step0 raw9267step0Labels = mixedMoment B raw9267step1 raw9267step1Labels := by
      have ha : raw9267step1 = (fun i j => raw9267step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9267step1 raw9267step0; decide +kernel
      have hl : raw9267step1Labels = raw9267step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9267step0 raw9267step0Labels permutation32 permutation3
    mixedMoment B raw9267step1 raw9267step1Labels = mixedMoment B raw9267step2 raw9267step2Labels := by
      have ha : raw9267step2 = raw9267step1 := by apply Matrix.ext; unfold raw9267step2 raw9267step1; decide +kernel
      have hl : raw9267step1Labels = labelEmbedding6 ∘ raw9267step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9267step1 raw9267step1Labels raw9267step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4600 node4600Labels := by rfl

def raw9268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9268 raw9268Labels = mixedMoment B node5150 node5150Labels := by
  calc
    _ = mixedMoment B node5150 node5150Labels := by rfl

def raw9269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9269 raw9269Labels = mixedMoment B node5205 node5205Labels := by
  calc
    mixedMoment B raw9269 raw9269Labels = mixedMoment B raw9269step0 raw9269step0Labels := by
      have hz : ∀ j, raw9269 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9269step0 = (fun i j => raw9269 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9269step0 raw9269; decide +kernel
      have hl : raw9269step0Labels = raw9269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9269 raw9269Labels permutation265 hz
    _ = mixedMoment B node5205 node5205Labels := by rfl

def raw9270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9270step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9270step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9270step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9270step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9270 raw9270Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw9270 raw9270Labels = mixedMoment B raw9270step0 raw9270step0Labels := by
      have hz : ∀ j, raw9270 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9270step0 = (fun i j => raw9270 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9270step0 raw9270; decide +kernel
      have hl : raw9270step0Labels = raw9270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9270 raw9270Labels permutation265 hz
    mixedMoment B raw9270step0 raw9270step0Labels = mixedMoment B raw9270step1 raw9270step1Labels := by
      have ha : raw9270step1 = (fun i j => raw9270step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9270step1 raw9270step0; decide +kernel
      have hl : raw9270step1Labels = raw9270step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9270step0 raw9270step0Labels permutation143 permutation5
    mixedMoment B raw9270step1 raw9270step1Labels = mixedMoment B raw9270step2 raw9270step2Labels := by
      have ha : raw9270step2 = raw9270step1 := by apply Matrix.ext; unfold raw9270step2 raw9270step1; decide +kernel
      have hl : raw9270step1Labels = labelEmbedding8 ∘ raw9270step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9270step1 raw9270step1Labels raw9270step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw9271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9271step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9271step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9271 raw9271Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw9271 raw9271Labels = mixedMoment B raw9271step0 raw9271step0Labels := by
      have hz : ∀ j, raw9271 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9271step0 = (fun i j => raw9271 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9271step0 raw9271; decide +kernel
      have hl : raw9271step0Labels = raw9271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9271 raw9271Labels permutation265 hz
    mixedMoment B raw9271step0 raw9271step0Labels = mixedMoment B raw9271step1 raw9271step1Labels := by
      have ha : raw9271step1 = (fun i j => raw9271step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9271step1 raw9271step0; decide +kernel
      have hl : raw9271step1Labels = raw9271step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9271step0 raw9271step0Labels permutation36 permutation2
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw9272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw9272step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw9272step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9272 raw9272Labels = mixedMoment B node4585 node4585Labels := by
  calc
    mixedMoment B raw9272 raw9272Labels = mixedMoment B raw9272step0 raw9272step0Labels := by
      have hz : ∀ j, raw9272 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9272step0 = (fun i j => raw9272 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9272step0 raw9272; decide +kernel
      have hl : raw9272step0Labels = raw9272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9272 raw9272Labels permutation265 hz
    mixedMoment B raw9272step0 raw9272step0Labels = mixedMoment B raw9272step1 raw9272step1Labels := by
      have ha : raw9272step1 = (fun i j => raw9272step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9272step1 raw9272step0; decide +kernel
      have hl : raw9272step1Labels = raw9272step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9272step0 raw9272step0Labels permutation32 permutation3
    mixedMoment B raw9272step1 raw9272step1Labels = mixedMoment B raw9272step2 raw9272step2Labels := by
      have ha : raw9272step2 = raw9272step1 := by apply Matrix.ext; unfold raw9272step2 raw9272step1; decide +kernel
      have hl : raw9272step1Labels = labelEmbedding6 ∘ raw9272step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9272step1 raw9272step1Labels raw9272step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4585 node4585Labels := by rfl

def raw9273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9273step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9273step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9273step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9273step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9273 raw9273Labels = mixedMoment B node5011 node5011Labels := by
  calc
    mixedMoment B raw9273 raw9273Labels = mixedMoment B raw9273step0 raw9273step0Labels := by
      have ha : raw9273step0 = (fun i j => raw9273 (permutation682 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9273step0 raw9273; decide +kernel
      have hl : raw9273step0Labels = raw9273Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9273 raw9273Labels permutation682 permutation5
    mixedMoment B raw9273step0 raw9273step0Labels = mixedMoment B raw9273step1 raw9273step1Labels := by
      have ha : raw9273step1 = raw9273step0 := by apply Matrix.ext; unfold raw9273step1 raw9273step0; decide +kernel
      have hl : raw9273step0Labels = labelEmbedding8 ∘ raw9273step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9273step0 raw9273step0Labels raw9273step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5011 node5011Labels := by rfl

def raw9274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9274step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9274step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9274step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9274step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9274 raw9274Labels = mixedMoment B node5016 node5016Labels := by
  calc
    mixedMoment B raw9274 raw9274Labels = mixedMoment B raw9274step0 raw9274step0Labels := by
      have hz : ∀ j, raw9274 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9274step0 = (fun i j => raw9274 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9274step0 raw9274; decide +kernel
      have hl : raw9274step0Labels = raw9274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9274 raw9274Labels permutation265 hz
    mixedMoment B raw9274step0 raw9274step0Labels = mixedMoment B raw9274step1 raw9274step1Labels := by
      have ha : raw9274step1 = (fun i j => raw9274step0 (permutation150 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9274step1 raw9274step0; decide +kernel
      have hl : raw9274step1Labels = raw9274step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9274step0 raw9274step0Labels permutation150 permutation5
    mixedMoment B raw9274step1 raw9274step1Labels = mixedMoment B raw9274step2 raw9274step2Labels := by
      have ha : raw9274step2 = raw9274step1 := by apply Matrix.ext; unfold raw9274step2 raw9274step1; decide +kernel
      have hl : raw9274step1Labels = labelEmbedding8 ∘ raw9274step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9274step1 raw9274step1Labels raw9274step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5016 node5016Labels := by rfl

def raw9275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9275step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9275step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9275step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9275 raw9275Labels = mixedMoment B node5016 node5016Labels := by
  calc
    mixedMoment B raw9275 raw9275Labels = mixedMoment B raw9275step0 raw9275step0Labels := by
      have hz : ∀ j, raw9275 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9275step0 = (fun i j => raw9275 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9275step0 raw9275; decide +kernel
      have hl : raw9275step0Labels = raw9275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9275 raw9275Labels permutation265 hz
    mixedMoment B raw9275step0 raw9275step0Labels = mixedMoment B raw9275step1 raw9275step1Labels := by
      have ha : raw9275step1 = (fun i j => raw9275step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9275step1 raw9275step0; decide +kernel
      have hl : raw9275step1Labels = raw9275step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9275step0 raw9275step0Labels permutation148 permutation5
    mixedMoment B raw9275step1 raw9275step1Labels = mixedMoment B raw9275step2 raw9275step2Labels := by
      have ha : raw9275step2 = raw9275step1 := by apply Matrix.ext; unfold raw9275step2 raw9275step1; decide +kernel
      have hl : raw9275step1Labels = labelEmbedding8 ∘ raw9275step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9275step1 raw9275step1Labels raw9275step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5016 node5016Labels := by rfl

def raw9276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw9276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw9276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw9276step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9276 raw9276Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw9276 raw9276Labels = mixedMoment B raw9276step0 raw9276step0Labels := by
      have hz : ∀ j, raw9276 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9276step0 = (fun i j => raw9276 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9276step0 raw9276; decide +kernel
      have hl : raw9276step0Labels = raw9276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9276 raw9276Labels permutation265 hz
    mixedMoment B raw9276step0 raw9276step0Labels = mixedMoment B raw9276step1 raw9276step1Labels := by
      have ha : raw9276step1 = (fun i j => raw9276step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9276step1 raw9276step0; decide +kernel
      have hl : raw9276step1Labels = raw9276step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9276step0 raw9276step0Labels permutation33 permutation2
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw9277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw9277step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9277step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw9277step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9277 raw9277Labels = mixedMoment B node4416 node4416Labels := by
  calc
    mixedMoment B raw9277 raw9277Labels = mixedMoment B raw9277step0 raw9277step0Labels := by
      have hz : ∀ j, raw9277 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9277step0 = (fun i j => raw9277 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9277step0 raw9277; decide +kernel
      have hl : raw9277step0Labels = raw9277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9277 raw9277Labels permutation265 hz
    mixedMoment B raw9277step0 raw9277step0Labels = mixedMoment B raw9277step1 raw9277step1Labels := by
      have ha : raw9277step1 = (fun i j => raw9277step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9277step1 raw9277step0; decide +kernel
      have hl : raw9277step1Labels = raw9277step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9277step0 raw9277step0Labels permutation149 permutation5
    mixedMoment B raw9277step1 raw9277step1Labels = mixedMoment B raw9277step2 raw9277step2Labels := by
      have ha : raw9277step2 = raw9277step1 := by apply Matrix.ext; unfold raw9277step2 raw9277step1; decide +kernel
      have hl : raw9277step1Labels = labelEmbedding8 ∘ raw9277step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9277step1 raw9277step1Labels raw9277step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4416 node4416Labels := by rfl

def raw9278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9278step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9278step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9278step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9278 raw9278Labels = mixedMoment B node4414 node4414Labels := by
  calc
    mixedMoment B raw9278 raw9278Labels = mixedMoment B raw9278step0 raw9278step0Labels := by
      have ha : raw9278step0 = (fun i j => raw9278 (permutation682 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9278step0 raw9278; decide +kernel
      have hl : raw9278step0Labels = raw9278Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9278 raw9278Labels permutation682 permutation5
    mixedMoment B raw9278step0 raw9278step0Labels = mixedMoment B raw9278step1 raw9278step1Labels := by
      have ha : raw9278step1 = raw9278step0 := by apply Matrix.ext; unfold raw9278step1 raw9278step0; decide +kernel
      have hl : raw9278step0Labels = labelEmbedding8 ∘ raw9278step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9278step0 raw9278step0Labels raw9278step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4414 node4414Labels := by rfl

def raw9279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9279step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9279step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9279step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9279step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9279 raw9279Labels = mixedMoment B node4420 node4420Labels := by
  calc
    mixedMoment B raw9279 raw9279Labels = mixedMoment B raw9279step0 raw9279step0Labels := by
      have hz : ∀ j, raw9279 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9279step0 = (fun i j => raw9279 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9279step0 raw9279; decide +kernel
      have hl : raw9279step0Labels = raw9279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9279 raw9279Labels permutation265 hz
    mixedMoment B raw9279step0 raw9279step0Labels = mixedMoment B raw9279step1 raw9279step1Labels := by
      have ha : raw9279step1 = (fun i j => raw9279step0 (permutation150 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9279step1 raw9279step0; decide +kernel
      have hl : raw9279step1Labels = raw9279step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9279step0 raw9279step0Labels permutation150 permutation5
    mixedMoment B raw9279step1 raw9279step1Labels = mixedMoment B raw9279step2 raw9279step2Labels := by
      have ha : raw9279step2 = raw9279step1 := by apply Matrix.ext; unfold raw9279step2 raw9279step1; decide +kernel
      have hl : raw9279step1Labels = labelEmbedding8 ∘ raw9279step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9279step1 raw9279step1Labels raw9279step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4420 node4420Labels := by rfl

def raw9280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9280step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9280step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9280 raw9280Labels = mixedMoment B node4420 node4420Labels := by
  calc
    mixedMoment B raw9280 raw9280Labels = mixedMoment B raw9280step0 raw9280step0Labels := by
      have hz : ∀ j, raw9280 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9280step0 = (fun i j => raw9280 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9280step0 raw9280; decide +kernel
      have hl : raw9280step0Labels = raw9280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9280 raw9280Labels permutation265 hz
    mixedMoment B raw9280step0 raw9280step0Labels = mixedMoment B raw9280step1 raw9280step1Labels := by
      have ha : raw9280step1 = (fun i j => raw9280step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9280step1 raw9280step0; decide +kernel
      have hl : raw9280step1Labels = raw9280step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9280step0 raw9280step0Labels permutation148 permutation5
    mixedMoment B raw9280step1 raw9280step1Labels = mixedMoment B raw9280step2 raw9280step2Labels := by
      have ha : raw9280step2 = raw9280step1 := by apply Matrix.ext; unfold raw9280step2 raw9280step1; decide +kernel
      have hl : raw9280step1Labels = labelEmbedding8 ∘ raw9280step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9280step1 raw9280step1Labels raw9280step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4420 node4420Labels := by rfl

def raw9281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -4, 1]]
def raw9281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -4, 1]]
def raw9281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9281step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw9281step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9281step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9281 raw9281Labels = mixedMoment B node4494 node4494Labels := by
  calc
    mixedMoment B raw9281 raw9281Labels = mixedMoment B raw9281step0 raw9281step0Labels := by
      have hz : ∀ j, raw9281 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9281step0 = (fun i j => raw9281 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9281step0 raw9281; decide +kernel
      have hl : raw9281step0Labels = raw9281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9281 raw9281Labels permutation265 hz
    mixedMoment B raw9281step0 raw9281step0Labels = mixedMoment B raw9281step1 raw9281step1Labels := by
      have ha : raw9281step1 = (fun i j => raw9281step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9281step1 raw9281step0; decide +kernel
      have hl : raw9281step1Labels = raw9281step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9281step0 raw9281step0Labels permutation137 permutation5
    mixedMoment B raw9281step1 raw9281step1Labels = mixedMoment B raw9281step2 raw9281step2Labels := by
      have ha : raw9281step2 = raw9281step1 := by apply Matrix.ext; unfold raw9281step2 raw9281step1; decide +kernel
      have hl : raw9281step1Labels = labelEmbedding8 ∘ raw9281step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9281step1 raw9281step1Labels raw9281step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4494 node4494Labels := by rfl

def raw9282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9282Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw9282step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9282step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9282step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9282 raw9282Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw9282 raw9282Labels = mixedMoment B raw9282step0 raw9282step0Labels := by
      have ha : raw9282step0 = (fun i j => raw9282 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9282step0 raw9282; decide +kernel
      have hl : raw9282step0Labels = raw9282Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9282 raw9282Labels permutation682 permutation3
    mixedMoment B raw9282step0 raw9282step0Labels = mixedMoment B raw9282step1 raw9282step1Labels := by
      have ha : raw9282step1 = -raw9282step0 := by apply Matrix.ext; change ∀ i j, raw9282step1 i j = -(raw9282step0 i j); unfold raw9282step1 raw9282step0; decide +kernel
      have hl : raw9282step1Labels = raw9282step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw9283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9283Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9283step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw9283step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9283step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9283step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9283 raw9283Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw9283 raw9283Labels = mixedMoment B raw9283step0 raw9283step0Labels := by
      have hz : ∀ j, raw9283 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9283step0 = (fun i j => raw9283 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9283step0 raw9283; decide +kernel
      have hl : raw9283step0Labels = raw9283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9283 raw9283Labels permutation265 hz
    mixedMoment B raw9283step0 raw9283step0Labels = mixedMoment B raw9283step1 raw9283step1Labels := by
      have ha : raw9283step1 = (fun i j => raw9283step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9283step1 raw9283step0; decide +kernel
      have hl : raw9283step1Labels = raw9283step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9283step0 raw9283step0Labels permutation151 permutation3
    mixedMoment B raw9283step1 raw9283step1Labels = mixedMoment B raw9283step2 raw9283step2Labels := by
      have ha : raw9283step2 = -raw9283step1 := by apply Matrix.ext; change ∀ i j, raw9283step2 i j = -(raw9283step1 i j); unfold raw9283step2 raw9283step1; decide +kernel
      have hl : raw9283step2Labels = raw9283step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw9284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9284Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9284step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9284step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw9284step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9284step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9284step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9284 raw9284Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw9284 raw9284Labels = mixedMoment B raw9284step0 raw9284step0Labels := by
      have hz : ∀ j, raw9284 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9284step0 = (fun i j => raw9284 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9284step0 raw9284; decide +kernel
      have hl : raw9284step0Labels = raw9284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9284 raw9284Labels permutation265 hz
    mixedMoment B raw9284step0 raw9284step0Labels = mixedMoment B raw9284step1 raw9284step1Labels := by
      have ha : raw9284step1 = (fun i j => raw9284step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9284step1 raw9284step0; decide +kernel
      have hl : raw9284step1Labels = raw9284step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9284step0 raw9284step0Labels permutation149 permutation3
    mixedMoment B raw9284step1 raw9284step1Labels = mixedMoment B raw9284step2 raw9284step2Labels := by
      have ha : raw9284step2 = -raw9284step1 := by apply Matrix.ext; change ∀ i j, raw9284step2 i j = -(raw9284step1 i j); unfold raw9284step2 raw9284step1; decide +kernel
      have hl : raw9284step2Labels = raw9284step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw9285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9285Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9285step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw9285step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9285step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw9285step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9285 raw9285Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw9285 raw9285Labels = mixedMoment B raw9285step0 raw9285step0Labels := by
      have hz : ∀ j, raw9285 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9285step0 = (fun i j => raw9285 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9285step0 raw9285; decide +kernel
      have hl : raw9285step0Labels = raw9285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9285 raw9285Labels permutation265 hz
    mixedMoment B raw9285step0 raw9285step0Labels = mixedMoment B raw9285step1 raw9285step1Labels := by
      have ha : raw9285step1 = (fun i j => raw9285step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9285step1 raw9285step0; decide +kernel
      have hl : raw9285step1Labels = raw9285step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9285step0 raw9285step0Labels permutation137 permutation3
    mixedMoment B raw9285step1 raw9285step1Labels = mixedMoment B raw9285step2 raw9285step2Labels := by
      have ha : raw9285step2 = -raw9285step1 := by apply Matrix.ext; change ∀ i j, raw9285step2 i j = -(raw9285step1 i j); unfold raw9285step2 raw9285step1; decide +kernel
      have hl : raw9285step2Labels = raw9285step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3619 node3619Labels := by rfl

def raw9286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9286Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9286step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9286step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw9286step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9286step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9286step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9286 raw9286Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw9286 raw9286Labels = mixedMoment B raw9286step0 raw9286step0Labels := by
      have hz : ∀ j, raw9286 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9286step0 = (fun i j => raw9286 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9286step0 raw9286; decide +kernel
      have hl : raw9286step0Labels = raw9286Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9286 raw9286Labels permutation265 hz
    mixedMoment B raw9286step0 raw9286step0Labels = mixedMoment B raw9286step1 raw9286step1Labels := by
      have ha : raw9286step1 = (fun i j => raw9286step0 (permutation54 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9286step1 raw9286step0; decide +kernel
      have hl : raw9286step1Labels = raw9286step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9286step0 raw9286step0Labels permutation54 permutation6
    mixedMoment B raw9286step1 raw9286step1Labels = mixedMoment B raw9286step2 raw9286step2Labels := by
      have ha : raw9286step2 = -raw9286step1 := by apply Matrix.ext; change ∀ i j, raw9286step2 i j = -(raw9286step1 i j); unfold raw9286step2 raw9286step1; decide +kernel
      have hl : raw9286step2Labels = raw9286step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw9287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9287Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9287step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw9287step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9287 raw9287Labels = mixedMoment B node1197 node1197Labels := by
  calc
    mixedMoment B raw9287 raw9287Labels = mixedMoment B raw9287step0 raw9287step0Labels := by
      have ha : raw9287step0 = (fun i j => raw9287 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9287step0 raw9287; decide +kernel
      have hl : raw9287step0Labels = raw9287Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9287 raw9287Labels permutation184 permutation3
    _ = mixedMoment B node1197 node1197Labels := by rfl

def raw9288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9288Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw9288step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9288 raw9288Labels = mixedMoment B node2851 node2851Labels := by
  calc
    mixedMoment B raw9288 raw9288Labels = mixedMoment B raw9288step0 raw9288step0Labels := by
      have ha : raw9288step0 = (fun i j => raw9288 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9288step0 raw9288; decide +kernel
      have hl : raw9288step0Labels = raw9288Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9288 raw9288Labels permutation184 permutation3
    _ = mixedMoment B node2851 node2851Labels := by rfl

def raw9289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9289Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw9289step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9289 raw9289Labels = mixedMoment B node2851 node2851Labels := by
  calc
    mixedMoment B raw9289 raw9289Labels = mixedMoment B raw9289step0 raw9289step0Labels := by
      have ha : raw9289step0 = (fun i j => raw9289 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9289step0 raw9289; decide +kernel
      have hl : raw9289step0Labels = raw9289Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9289 raw9289Labels permutation208 permutation3
    _ = mixedMoment B node2851 node2851Labels := by rfl

def raw9290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9290Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw9290step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9290 raw9290Labels = mixedMoment B node3058 node3058Labels := by
  calc
    mixedMoment B raw9290 raw9290Labels = mixedMoment B raw9290step0 raw9290step0Labels := by
      have ha : raw9290step0 = (fun i j => raw9290 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9290step0 raw9290; decide +kernel
      have hl : raw9290step0Labels = raw9290Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9290 raw9290Labels permutation184 permutation3
    _ = mixedMoment B node3058 node3058Labels := by rfl

def raw9291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9291Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9291step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9291 raw9291Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw9291 raw9291Labels = mixedMoment B raw9291step0 raw9291step0Labels := by
      have ha : raw9291step0 = (fun i j => raw9291 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9291step0 raw9291; decide +kernel
      have hl : raw9291step0Labels = raw9291Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9291 raw9291Labels permutation184 permutation3
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw9292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9292Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9292step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9292step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9292 raw9292Labels = mixedMoment B node1234 node1234Labels := by
  calc
    mixedMoment B raw9292 raw9292Labels = mixedMoment B raw9292step0 raw9292step0Labels := by
      have hz : ∀ j, raw9292 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9292step0 = (fun i j => raw9292 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9292step0 raw9292; decide +kernel
      have hl : raw9292step0Labels = raw9292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9292 raw9292Labels permutation265 hz
    mixedMoment B raw9292step0 raw9292step0Labels = mixedMoment B raw9292step1 raw9292step1Labels := by
      have ha : raw9292step1 = (fun i j => raw9292step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9292step1 raw9292step0; decide +kernel
      have hl : raw9292step1Labels = raw9292step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9292step0 raw9292step0Labels permutation38 permutation3
    _ = mixedMoment B node1234 node1234Labels := by rfl

def raw9293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9293Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9293step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9293step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9293 raw9293Labels = mixedMoment B node2923 node2923Labels := by
  calc
    mixedMoment B raw9293 raw9293Labels = mixedMoment B raw9293step0 raw9293step0Labels := by
      have ha : raw9293step0 = (fun i j => raw9293 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9293step0 raw9293; decide +kernel
      have hl : raw9293step0Labels = raw9293Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9293 raw9293Labels permutation158 permutation3
    _ = mixedMoment B node2923 node2923Labels := by rfl

def raw9294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9294Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9294step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9294step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9294 raw9294Labels = mixedMoment B node2879 node2879Labels := by
  calc
    mixedMoment B raw9294 raw9294Labels = mixedMoment B raw9294step0 raw9294step0Labels := by
      have hz : ∀ j, raw9294 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9294step0 = (fun i j => raw9294 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9294step0 raw9294; decide +kernel
      have hl : raw9294step0Labels = raw9294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9294 raw9294Labels permutation265 hz
    mixedMoment B raw9294step0 raw9294step0Labels = mixedMoment B raw9294step1 raw9294step1Labels := by
      have ha : raw9294step1 = (fun i j => raw9294step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9294step1 raw9294step0; decide +kernel
      have hl : raw9294step1Labels = raw9294step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9294step0 raw9294step0Labels permutation38 permutation3
    _ = mixedMoment B node2879 node2879Labels := by rfl

def raw9295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9295Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9295step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9295step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9295 raw9295Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw9295 raw9295Labels = mixedMoment B raw9295step0 raw9295step0Labels := by
      have hz : ∀ j, raw9295 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9295step0 = (fun i j => raw9295 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9295step0 raw9295; decide +kernel
      have hl : raw9295step0Labels = raw9295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9295 raw9295Labels permutation265 hz
    mixedMoment B raw9295step0 raw9295step0Labels = mixedMoment B raw9295step1 raw9295step1Labels := by
      have ha : raw9295step1 = (fun i j => raw9295step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9295step1 raw9295step0; decide +kernel
      have hl : raw9295step1Labels = raw9295step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9295step0 raw9295step0Labels permutation40 permutation3
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw9296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9296Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9296step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9296 raw9296Labels = mixedMoment B node3099 node3099Labels := by
  calc
    mixedMoment B raw9296 raw9296Labels = mixedMoment B raw9296step0 raw9296step0Labels := by
      have hz : ∀ j, raw9296 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9296step0 = (fun i j => raw9296 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9296step0 raw9296; decide +kernel
      have hl : raw9296step0Labels = raw9296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9296 raw9296Labels permutation265 hz
    mixedMoment B raw9296step0 raw9296step0Labels = mixedMoment B raw9296step1 raw9296step1Labels := by
      have ha : raw9296step1 = (fun i j => raw9296step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9296step1 raw9296step0; decide +kernel
      have hl : raw9296step1Labels = raw9296step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9296step0 raw9296step0Labels permutation38 permutation3
    _ = mixedMoment B node3099 node3099Labels := by rfl

def raw9297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9297Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9297step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9297step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9297step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9297 raw9297Labels = mixedMoment B node1234 node1234Labels := by
  calc
    mixedMoment B raw9297 raw9297Labels = mixedMoment B raw9297step0 raw9297step0Labels := by
      have hz : ∀ j, raw9297 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9297step0 = (fun i j => raw9297 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9297step0 raw9297; decide +kernel
      have hl : raw9297step0Labels = raw9297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9297 raw9297Labels permutation265 hz
    mixedMoment B raw9297step0 raw9297step0Labels = mixedMoment B raw9297step1 raw9297step1Labels := by
      have ha : raw9297step1 = (fun i j => raw9297step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9297step1 raw9297step0; decide +kernel
      have hl : raw9297step1Labels = raw9297step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9297step0 raw9297step0Labels permutation32 permutation3
    _ = mixedMoment B node1234 node1234Labels := by rfl

def raw9298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9298Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9298step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9298step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9298 raw9298Labels = mixedMoment B node2923 node2923Labels := by
  calc
    mixedMoment B raw9298 raw9298Labels = mixedMoment B raw9298step0 raw9298step0Labels := by
      have ha : raw9298step0 = (fun i j => raw9298 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9298step0 raw9298; decide +kernel
      have hl : raw9298step0Labels = raw9298Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9298 raw9298Labels permutation152 permutation3
    _ = mixedMoment B node2923 node2923Labels := by rfl

def raw9299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9299Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9299step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw9299step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9299 raw9299Labels = mixedMoment B node2879 node2879Labels := by
  calc
    mixedMoment B raw9299 raw9299Labels = mixedMoment B raw9299step0 raw9299step0Labels := by
      have hz : ∀ j, raw9299 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9299step0 = (fun i j => raw9299 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9299step0 raw9299; decide +kernel
      have hl : raw9299step0Labels = raw9299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9299 raw9299Labels permutation265 hz
    mixedMoment B raw9299step0 raw9299step0Labels = mixedMoment B raw9299step1 raw9299step1Labels := by
      have ha : raw9299step1 = (fun i j => raw9299step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9299step1 raw9299step0; decide +kernel
      have hl : raw9299step1Labels = raw9299step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9299step0 raw9299step0Labels permutation32 permutation3
    _ = mixedMoment B node2879 node2879Labels := by rfl

def raw9300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9300Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9300step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw9300step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9300 raw9300Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw9300 raw9300Labels = mixedMoment B raw9300step0 raw9300step0Labels := by
      have hz : ∀ j, raw9300 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9300step0 = (fun i j => raw9300 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9300step0 raw9300; decide +kernel
      have hl : raw9300step0Labels = raw9300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9300 raw9300Labels permutation265 hz
    mixedMoment B raw9300step0 raw9300step0Labels = mixedMoment B raw9300step1 raw9300step1Labels := by
      have ha : raw9300step1 = (fun i j => raw9300step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9300step1 raw9300step0; decide +kernel
      have hl : raw9300step1Labels = raw9300step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9300step0 raw9300step0Labels permutation34 permutation3
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw9301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9301step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9301 raw9301Labels = mixedMoment B node3099 node3099Labels := by
  calc
    mixedMoment B raw9301 raw9301Labels = mixedMoment B raw9301step0 raw9301step0Labels := by
      have hz : ∀ j, raw9301 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9301step0 = (fun i j => raw9301 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9301step0 raw9301; decide +kernel
      have hl : raw9301step0Labels = raw9301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9301 raw9301Labels permutation265 hz
    mixedMoment B raw9301step0 raw9301step0Labels = mixedMoment B raw9301step1 raw9301step1Labels := by
      have ha : raw9301step1 = (fun i j => raw9301step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9301step1 raw9301step0; decide +kernel
      have hl : raw9301step1Labels = raw9301step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9301step0 raw9301step0Labels permutation32 permutation3
    _ = mixedMoment B node3099 node3099Labels := by rfl

def raw9302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9302Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9302step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw9302step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9302 raw9302Labels = mixedMoment B node1204 node1204Labels := by
  calc
    mixedMoment B raw9302 raw9302Labels = mixedMoment B raw9302step0 raw9302step0Labels := by
      have hz : ∀ j, raw9302 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9302step0 = (fun i j => raw9302 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9302step0 raw9302; decide +kernel
      have hl : raw9302step0Labels = raw9302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9302 raw9302Labels permutation265 hz
    mixedMoment B raw9302step0 raw9302step0Labels = mixedMoment B raw9302step1 raw9302step1Labels := by
      have ha : raw9302step1 = (fun i j => raw9302step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9302step1 raw9302step0; decide +kernel
      have hl : raw9302step1Labels = raw9302step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9302step0 raw9302step0Labels permutation32 permutation3
    _ = mixedMoment B node1204 node1204Labels := by rfl

def raw9303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9303Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw9303step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9303 raw9303Labels = mixedMoment B node2912 node2912Labels := by
  calc
    mixedMoment B raw9303 raw9303Labels = mixedMoment B raw9303step0 raw9303step0Labels := by
      have ha : raw9303step0 = (fun i j => raw9303 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9303step0 raw9303; decide +kernel
      have hl : raw9303step0Labels = raw9303Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9303 raw9303Labels permutation152 permutation3
    _ = mixedMoment B node2912 node2912Labels := by rfl

def raw9304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9304Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9304step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9304step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw9304step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9304 raw9304Labels = mixedMoment B node2855 node2855Labels := by
  calc
    mixedMoment B raw9304 raw9304Labels = mixedMoment B raw9304step0 raw9304step0Labels := by
      have hz : ∀ j, raw9304 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9304step0 = (fun i j => raw9304 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9304step0 raw9304; decide +kernel
      have hl : raw9304step0Labels = raw9304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9304 raw9304Labels permutation265 hz
    mixedMoment B raw9304step0 raw9304step0Labels = mixedMoment B raw9304step1 raw9304step1Labels := by
      have ha : raw9304step1 = (fun i j => raw9304step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9304step1 raw9304step0; decide +kernel
      have hl : raw9304step1Labels = raw9304step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9304step0 raw9304step0Labels permutation32 permutation3
    _ = mixedMoment B node2855 node2855Labels := by rfl

def raw9305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9305Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9305step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9305step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw9305step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9305 raw9305Labels = mixedMoment B node2855 node2855Labels := by
  calc
    mixedMoment B raw9305 raw9305Labels = mixedMoment B raw9305step0 raw9305step0Labels := by
      have hz : ∀ j, raw9305 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9305step0 = (fun i j => raw9305 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9305step0 raw9305; decide +kernel
      have hl : raw9305step0Labels = raw9305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9305 raw9305Labels permutation265 hz
    mixedMoment B raw9305step0 raw9305step0Labels = mixedMoment B raw9305step1 raw9305step1Labels := by
      have ha : raw9305step1 = (fun i j => raw9305step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9305step1 raw9305step0; decide +kernel
      have hl : raw9305step1Labels = raw9305step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9305step0 raw9305step0Labels permutation38 permutation3
    _ = mixedMoment B node2855 node2855Labels := by rfl

def raw9306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw9306Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw9306step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw9306step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9306 raw9306Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw9306 raw9306Labels = mixedMoment B raw9306step0 raw9306step0Labels := by
      have hz : ∀ j, raw9306 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9306step0 = (fun i j => raw9306 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9306step0 raw9306; decide +kernel
      have hl : raw9306step0Labels = raw9306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9306 raw9306Labels permutation265 hz
    mixedMoment B raw9306step0 raw9306step0Labels = mixedMoment B raw9306step1 raw9306step1Labels := by
      have ha : raw9306step1 = (fun i j => raw9306step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9306step1 raw9306step0; decide +kernel
      have hl : raw9306step1Labels = raw9306step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9306step0 raw9306step0Labels permutation33 permutation3
    _ = mixedMoment B node3078 node3078Labels := by rfl

def raw9307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9307Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9307step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw9307step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9307 raw9307Labels = mixedMoment B node1199 node1199Labels := by
  calc
    mixedMoment B raw9307 raw9307Labels = mixedMoment B raw9307step0 raw9307step0Labels := by
      have hz : ∀ j, raw9307 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9307step0 = (fun i j => raw9307 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9307step0 raw9307; decide +kernel
      have hl : raw9307step0Labels = raw9307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9307 raw9307Labels permutation265 hz
    mixedMoment B raw9307step0 raw9307step0Labels = mixedMoment B raw9307step1 raw9307step1Labels := by
      have ha : raw9307step1 = (fun i j => raw9307step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9307step1 raw9307step0; decide +kernel
      have hl : raw9307step1Labels = raw9307step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9307step0 raw9307step0Labels permutation32 permutation3
    _ = mixedMoment B node1199 node1199Labels := by rfl

def raw9308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9308Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw9308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9308step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9308step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9308 raw9308Labels = mixedMoment B node1593 node1593Labels := by
  calc
    mixedMoment B raw9308 raw9308Labels = mixedMoment B raw9308step0 raw9308step0Labels := by
      have ha : raw9308step0 = (fun i j => raw9308 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9308step0 raw9308; decide +kernel
      have hl : raw9308step0Labels = raw9308Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9308 raw9308Labels permutation682 permutation3
    mixedMoment B raw9308step0 raw9308step0Labels = mixedMoment B raw9308step1 raw9308step1Labels := by
      have ha : raw9308step1 = -raw9308step0 := by apply Matrix.ext; change ∀ i j, raw9308step1 i j = -(raw9308step0 i j); unfold raw9308step1 raw9308step0; decide +kernel
      have hl : raw9308step1Labels = raw9308step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1593 node1593Labels := by rfl

def raw9309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9309Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9309step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw9309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9309step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw9309step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9309 raw9309Labels = mixedMoment B node1603 node1603Labels := by
  calc
    mixedMoment B raw9309 raw9309Labels = mixedMoment B raw9309step0 raw9309step0Labels := by
      have hz : ∀ j, raw9309 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9309step0 = (fun i j => raw9309 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9309step0 raw9309; decide +kernel
      have hl : raw9309step0Labels = raw9309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9309 raw9309Labels permutation265 hz
    mixedMoment B raw9309step0 raw9309step0Labels = mixedMoment B raw9309step1 raw9309step1Labels := by
      have ha : raw9309step1 = (fun i j => raw9309step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9309step1 raw9309step0; decide +kernel
      have hl : raw9309step1Labels = raw9309step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9309step0 raw9309step0Labels permutation151 permutation3
    mixedMoment B raw9309step1 raw9309step1Labels = mixedMoment B raw9309step2 raw9309step2Labels := by
      have ha : raw9309step2 = -raw9309step1 := by apply Matrix.ext; change ∀ i j, raw9309step2 i j = -(raw9309step1 i j); unfold raw9309step2 raw9309step1; decide +kernel
      have hl : raw9309step2Labels = raw9309step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1603 node1603Labels := by rfl

def raw9310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9310Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9310step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw9310step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9310step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw9310step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9310 raw9310Labels = mixedMoment B node1603 node1603Labels := by
  calc
    mixedMoment B raw9310 raw9310Labels = mixedMoment B raw9310step0 raw9310step0Labels := by
      have hz : ∀ j, raw9310 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9310step0 = (fun i j => raw9310 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9310step0 raw9310; decide +kernel
      have hl : raw9310step0Labels = raw9310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9310 raw9310Labels permutation265 hz
    mixedMoment B raw9310step0 raw9310step0Labels = mixedMoment B raw9310step1 raw9310step1Labels := by
      have ha : raw9310step1 = (fun i j => raw9310step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9310step1 raw9310step0; decide +kernel
      have hl : raw9310step1Labels = raw9310step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9310step0 raw9310step0Labels permutation149 permutation3
    mixedMoment B raw9310step1 raw9310step1Labels = mixedMoment B raw9310step2 raw9310step2Labels := by
      have ha : raw9310step2 = -raw9310step1 := by apply Matrix.ext; change ∀ i j, raw9310step2 i j = -(raw9310step1 i j); unfold raw9310step2 raw9310step1; decide +kernel
      have hl : raw9310step2Labels = raw9310step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1603 node1603Labels := by rfl

def raw9311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -4, 1]]
def raw9311Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -4, 1]]
def raw9311step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw9311step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9311step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw9311step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9311 raw9311Labels = mixedMoment B node1700 node1700Labels := by
  calc
    mixedMoment B raw9311 raw9311Labels = mixedMoment B raw9311step0 raw9311step0Labels := by
      have hz : ∀ j, raw9311 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9311step0 = (fun i j => raw9311 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9311step0 raw9311; decide +kernel
      have hl : raw9311step0Labels = raw9311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9311 raw9311Labels permutation265 hz
    mixedMoment B raw9311step0 raw9311step0Labels = mixedMoment B raw9311step1 raw9311step1Labels := by
      have ha : raw9311step1 = (fun i j => raw9311step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9311step1 raw9311step0; decide +kernel
      have hl : raw9311step1Labels = raw9311step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9311step0 raw9311step0Labels permutation137 permutation3
    mixedMoment B raw9311step1 raw9311step1Labels = mixedMoment B raw9311step2 raw9311step2Labels := by
      have ha : raw9311step2 = -raw9311step1 := by apply Matrix.ext; change ∀ i j, raw9311step2 i j = -(raw9311step1 i j); unfold raw9311step2 raw9311step1; decide +kernel
      have hl : raw9311step2Labels = raw9311step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1700 node1700Labels := by rfl

def raw9312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9312Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9312step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9312step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9312 raw9312Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw9312 raw9312Labels = mixedMoment B raw9312step0 raw9312step0Labels := by
      have ha : raw9312step0 = (fun i j => raw9312 (permutation668 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9312step0 raw9312; decide +kernel
      have hl : raw9312step0Labels = raw9312Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9312 raw9312Labels permutation668 permutation5
    mixedMoment B raw9312step0 raw9312step0Labels = mixedMoment B raw9312step1 raw9312step1Labels := by
      have ha : raw9312step1 = raw9312step0 := by apply Matrix.ext; unfold raw9312step1 raw9312step0; decide +kernel
      have hl : raw9312step0Labels = labelEmbedding1 ∘ raw9312step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9312step0 raw9312step0Labels raw9312step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2730 node2730Labels := by rfl

def raw9313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9313Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9313step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9313step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9313step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9313 raw9313Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw9313 raw9313Labels = mixedMoment B raw9313step0 raw9313step0Labels := by
      have hz : ∀ j, raw9313 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9313step0 = (fun i j => raw9313 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9313step0 raw9313; decide +kernel
      have hl : raw9313step0Labels = raw9313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9313 raw9313Labels permutation265 hz
    mixedMoment B raw9313step0 raw9313step0Labels = mixedMoment B raw9313step1 raw9313step1Labels := by
      have ha : raw9313step1 = (fun i j => raw9313step0 (permutation147 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9313step1 raw9313step0; decide +kernel
      have hl : raw9313step1Labels = raw9313step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9313step0 raw9313step0Labels permutation147 permutation5
    mixedMoment B raw9313step1 raw9313step1Labels = mixedMoment B raw9313step2 raw9313step2Labels := by
      have ha : raw9313step2 = raw9313step1 := by apply Matrix.ext; unfold raw9313step2 raw9313step1; decide +kernel
      have hl : raw9313step1Labels = labelEmbedding1 ∘ raw9313step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9313step1 raw9313step1Labels raw9313step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2731 node2731Labels := by rfl

def raw9314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9314Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9314step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9314step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9314step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9314 raw9314Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw9314 raw9314Labels = mixedMoment B raw9314step0 raw9314step0Labels := by
      have hz : ∀ j, raw9314 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9314step0 = (fun i j => raw9314 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9314step0 raw9314; decide +kernel
      have hl : raw9314step0Labels = raw9314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9314 raw9314Labels permutation265 hz
    mixedMoment B raw9314step0 raw9314step0Labels = mixedMoment B raw9314step1 raw9314step1Labels := by
      have ha : raw9314step1 = (fun i j => raw9314step0 (permutation146 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9314step1 raw9314step0; decide +kernel
      have hl : raw9314step1Labels = raw9314step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9314step0 raw9314step0Labels permutation146 permutation5
    mixedMoment B raw9314step1 raw9314step1Labels = mixedMoment B raw9314step2 raw9314step2Labels := by
      have ha : raw9314step2 = raw9314step1 := by apply Matrix.ext; unfold raw9314step2 raw9314step1; decide +kernel
      have hl : raw9314step1Labels = labelEmbedding1 ∘ raw9314step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9314step1 raw9314step1Labels raw9314step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2731 node2731Labels := by rfl

def raw9315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9315Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9315step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw9315step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9315step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw9315step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9315 raw9315Labels = mixedMoment B node2775 node2775Labels := by
  calc
    mixedMoment B raw9315 raw9315Labels = mixedMoment B raw9315step0 raw9315step0Labels := by
      have hz : ∀ j, raw9315 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9315step0 = (fun i j => raw9315 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9315step0 raw9315; decide +kernel
      have hl : raw9315step0Labels = raw9315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9315 raw9315Labels permutation265 hz
    mixedMoment B raw9315step0 raw9315step0Labels = mixedMoment B raw9315step1 raw9315step1Labels := by
      have ha : raw9315step1 = (fun i j => raw9315step0 (permutation128 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9315step1 raw9315step0; decide +kernel
      have hl : raw9315step1Labels = raw9315step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9315step0 raw9315step0Labels permutation128 permutation5
    mixedMoment B raw9315step1 raw9315step1Labels = mixedMoment B raw9315step2 raw9315step2Labels := by
      have ha : raw9315step2 = raw9315step1 := by apply Matrix.ext; unfold raw9315step2 raw9315step1; decide +kernel
      have hl : raw9315step1Labels = labelEmbedding1 ∘ raw9315step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9315step1 raw9315step1Labels raw9315step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2775 node2775Labels := by rfl

def raw9316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9316Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9316step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw9316step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9316step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9316step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9316step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9316step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9316 raw9316Labels = mixedMoment B node3887 node3887Labels := by
  calc
    mixedMoment B raw9316 raw9316Labels = mixedMoment B raw9316step0 raw9316step0Labels := by
      have hz : ∀ j, raw9316 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9316step0 = (fun i j => raw9316 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9316step0 raw9316; decide +kernel
      have hl : raw9316step0Labels = raw9316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9316 raw9316Labels permutation265 hz
    mixedMoment B raw9316step0 raw9316step0Labels = mixedMoment B raw9316step1 raw9316step1Labels := by
      have ha : raw9316step1 = (fun i j => raw9316step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9316step1 raw9316step0; decide +kernel
      have hl : raw9316step1Labels = raw9316step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9316step0 raw9316step0Labels permutation50 permutation7
    mixedMoment B raw9316step1 raw9316step1Labels = mixedMoment B raw9316step2 raw9316step2Labels := by
      have ha : raw9316step2 = -raw9316step1 := by apply Matrix.ext; change ∀ i j, raw9316step2 i j = -(raw9316step1 i j); unfold raw9316step2 raw9316step1; decide +kernel
      have hl : raw9316step2Labels = raw9316step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9316step2 raw9316step2Labels = mixedMoment B raw9316step3 raw9316step3Labels := by
      have ha : raw9316step3 = raw9316step2 := by apply Matrix.ext; unfold raw9316step3 raw9316step2; decide +kernel
      have hl : raw9316step2Labels = labelEmbedding1 ∘ raw9316step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9316step2 raw9316step2Labels raw9316step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3887 node3887Labels := by rfl

def raw9317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9317Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw9317step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9317step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw9317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9317 raw9317Labels = mixedMoment B node2457 node2457Labels := by
  calc
    mixedMoment B raw9317 raw9317Labels = mixedMoment B raw9317step0 raw9317step0Labels := by
      have ha : raw9317step0 = (fun i j => raw9317 (permutation620 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9317step0 raw9317; decide +kernel
      have hl : raw9317step0Labels = raw9317Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9317 raw9317Labels permutation620 permutation5
    mixedMoment B raw9317step0 raw9317step0Labels = mixedMoment B raw9317step1 raw9317step1Labels := by
      have ha : raw9317step1 = raw9317step0 := by apply Matrix.ext; unfold raw9317step1 raw9317step0; decide +kernel
      have hl : raw9317step0Labels = labelEmbedding1 ∘ raw9317step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9317step0 raw9317step0Labels raw9317step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2457 node2457Labels := by rfl

def raw9318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9318Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9318step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9318step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9318step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9318 raw9318Labels = mixedMoment B node2460 node2460Labels := by
  calc
    mixedMoment B raw9318 raw9318Labels = mixedMoment B raw9318step0 raw9318step0Labels := by
      have ha : raw9318step0 = (fun i j => raw9318 (permutation621 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9318step0 raw9318; decide +kernel
      have hl : raw9318step0Labels = raw9318Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9318 raw9318Labels permutation621 permutation5
    mixedMoment B raw9318step0 raw9318step0Labels = mixedMoment B raw9318step1 raw9318step1Labels := by
      have ha : raw9318step1 = raw9318step0 := by apply Matrix.ext; unfold raw9318step1 raw9318step0; decide +kernel
      have hl : raw9318step0Labels = labelEmbedding1 ∘ raw9318step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9318step0 raw9318step0Labels raw9318step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2460 node2460Labels := by rfl

def raw9319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9319Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9319step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9319step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9319step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9319step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9319 raw9319Labels = mixedMoment B node2460 node2460Labels := by
  calc
    mixedMoment B raw9319 raw9319Labels = mixedMoment B raw9319step0 raw9319step0Labels := by
      have ha : raw9319step0 = (fun i j => raw9319 (permutation619 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9319step0 raw9319; decide +kernel
      have hl : raw9319step0Labels = raw9319Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9319 raw9319Labels permutation619 permutation5
    mixedMoment B raw9319step0 raw9319step0Labels = mixedMoment B raw9319step1 raw9319step1Labels := by
      have ha : raw9319step1 = raw9319step0 := by apply Matrix.ext; unfold raw9319step1 raw9319step0; decide +kernel
      have hl : raw9319step0Labels = labelEmbedding1 ∘ raw9319step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9319step0 raw9319step0Labels raw9319step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2460 node2460Labels := by rfl

def raw9320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9320Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9320step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9320step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9320 raw9320Labels = mixedMoment B node2507 node2507Labels := by
  calc
    mixedMoment B raw9320 raw9320Labels = mixedMoment B raw9320step0 raw9320step0Labels := by
      have ha : raw9320step0 = (fun i j => raw9320 (permutation609 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9320step0 raw9320; decide +kernel
      have hl : raw9320step0Labels = raw9320Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9320 raw9320Labels permutation609 permutation5
    mixedMoment B raw9320step0 raw9320step0Labels = mixedMoment B raw9320step1 raw9320step1Labels := by
      have ha : raw9320step1 = raw9320step0 := by apply Matrix.ext; unfold raw9320step1 raw9320step0; decide +kernel
      have hl : raw9320step0Labels = labelEmbedding1 ∘ raw9320step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9320step0 raw9320step0Labels raw9320step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2507 node2507Labels := by rfl

def raw9321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9321Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw9321step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9321step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9321step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9321step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9321step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9321 raw9321Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw9321 raw9321Labels = mixedMoment B raw9321step0 raw9321step0Labels := by
      have ha : raw9321step0 = (fun i j => raw9321 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9321step0 raw9321; decide +kernel
      have hl : raw9321step0Labels = raw9321Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9321 raw9321Labels permutation246 permutation7
    mixedMoment B raw9321step0 raw9321step0Labels = mixedMoment B raw9321step1 raw9321step1Labels := by
      have ha : raw9321step1 = -raw9321step0 := by apply Matrix.ext; change ∀ i j, raw9321step1 i j = -(raw9321step0 i j); unfold raw9321step1 raw9321step0; decide +kernel
      have hl : raw9321step1Labels = raw9321step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9321step1 raw9321step1Labels = mixedMoment B raw9321step2 raw9321step2Labels := by
      have ha : raw9321step2 = raw9321step1 := by apply Matrix.ext; unfold raw9321step2 raw9321step1; decide +kernel
      have hl : raw9321step1Labels = labelEmbedding1 ∘ raw9321step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9321step1 raw9321step1Labels raw9321step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3571 node3571Labels := by rfl

def raw9322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9322Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9322step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9322step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw9322step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9322step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw9322step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9322 raw9322Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw9322 raw9322Labels = mixedMoment B raw9322step0 raw9322step0Labels := by
      have hz : ∀ j, raw9322 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9322step0 = (fun i j => raw9322 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9322step0 raw9322; decide +kernel
      have hl : raw9322step0Labels = raw9322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9322 raw9322Labels permutation265 hz
    mixedMoment B raw9322step0 raw9322step0Labels = mixedMoment B raw9322step1 raw9322step1Labels := by
      have ha : raw9322step1 = (fun i j => raw9322step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9322step1 raw9322step0; decide +kernel
      have hl : raw9322step1Labels = raw9322step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9322step0 raw9322step0Labels permutation139 permutation5
    mixedMoment B raw9322step1 raw9322step1Labels = mixedMoment B raw9322step2 raw9322step2Labels := by
      have ha : raw9322step2 = raw9322step1 := by apply Matrix.ext; unfold raw9322step2 raw9322step1; decide +kernel
      have hl : raw9322step1Labels = labelEmbedding1 ∘ raw9322step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9322step1 raw9322step1Labels raw9322step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2702 node2702Labels := by rfl

def raw9323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9323Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9323step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9323step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9323step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9323 raw9323Labels = mixedMoment B node2700 node2700Labels := by
  calc
    mixedMoment B raw9323 raw9323Labels = mixedMoment B raw9323step0 raw9323step0Labels := by
      have ha : raw9323step0 = (fun i j => raw9323 (permutation646 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9323step0 raw9323; decide +kernel
      have hl : raw9323step0Labels = raw9323Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9323 raw9323Labels permutation646 permutation5
    mixedMoment B raw9323step0 raw9323step0Labels = mixedMoment B raw9323step1 raw9323step1Labels := by
      have ha : raw9323step1 = raw9323step0 := by apply Matrix.ext; unfold raw9323step1 raw9323step0; decide +kernel
      have hl : raw9323step0Labels = labelEmbedding1 ∘ raw9323step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9323step0 raw9323step0Labels raw9323step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2700 node2700Labels := by rfl

def raw9324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9324Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9324step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw9324step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw9324step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9324 raw9324Labels = mixedMoment B node2706 node2706Labels := by
  calc
    mixedMoment B raw9324 raw9324Labels = mixedMoment B raw9324step0 raw9324step0Labels := by
      have hz : ∀ j, raw9324 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9324step0 = (fun i j => raw9324 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9324step0 raw9324; decide +kernel
      have hl : raw9324step0Labels = raw9324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9324 raw9324Labels permutation265 hz
    mixedMoment B raw9324step0 raw9324step0Labels = mixedMoment B raw9324step1 raw9324step1Labels := by
      have ha : raw9324step1 = (fun i j => raw9324step0 (permutation138 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9324step1 raw9324step0; decide +kernel
      have hl : raw9324step1Labels = raw9324step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9324step0 raw9324step0Labels permutation138 permutation5
    mixedMoment B raw9324step1 raw9324step1Labels = mixedMoment B raw9324step2 raw9324step2Labels := by
      have ha : raw9324step2 = raw9324step1 := by apply Matrix.ext; unfold raw9324step2 raw9324step1; decide +kernel
      have hl : raw9324step1Labels = labelEmbedding1 ∘ raw9324step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9324step1 raw9324step1Labels raw9324step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2706 node2706Labels := by rfl

def raw9325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9325Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9325step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9325step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9325step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9325step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9325 raw9325Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw9325 raw9325Labels = mixedMoment B raw9325step0 raw9325step0Labels := by
      have hz : ∀ j, raw9325 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9325step0 = (fun i j => raw9325 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9325step0 raw9325; decide +kernel
      have hl : raw9325step0Labels = raw9325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9325 raw9325Labels permutation265 hz
    mixedMoment B raw9325step0 raw9325step0Labels = mixedMoment B raw9325step1 raw9325step1Labels := by
      have ha : raw9325step1 = (fun i j => raw9325step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9325step1 raw9325step0; decide +kernel
      have hl : raw9325step1Labels = raw9325step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9325step0 raw9325step0Labels permutation137 permutation5
    mixedMoment B raw9325step1 raw9325step1Labels = mixedMoment B raw9325step2 raw9325step2Labels := by
      have ha : raw9325step2 = raw9325step1 := by apply Matrix.ext; unfold raw9325step2 raw9325step1; decide +kernel
      have hl : raw9325step1Labels = labelEmbedding1 ∘ raw9325step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9325step1 raw9325step1Labels raw9325step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2738 node2738Labels := by rfl

def raw9326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9326Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9326step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw9326step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9326step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9326step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9326step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9326step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9326 raw9326Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw9326 raw9326Labels = mixedMoment B raw9326step0 raw9326step0Labels := by
      have hz : ∀ j, raw9326 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9326step0 = (fun i j => raw9326 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9326step0 raw9326; decide +kernel
      have hl : raw9326step0Labels = raw9326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9326 raw9326Labels permutation265 hz
    mixedMoment B raw9326step0 raw9326step0Labels = mixedMoment B raw9326step1 raw9326step1Labels := by
      have ha : raw9326step1 = (fun i j => raw9326step0 (permutation52 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9326step1 raw9326step0; decide +kernel
      have hl : raw9326step1Labels = raw9326step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9326step0 raw9326step0Labels permutation52 permutation7
    mixedMoment B raw9326step1 raw9326step1Labels = mixedMoment B raw9326step2 raw9326step2Labels := by
      have ha : raw9326step2 = -raw9326step1 := by apply Matrix.ext; change ∀ i j, raw9326step2 i j = -(raw9326step1 i j); unfold raw9326step2 raw9326step1; decide +kernel
      have hl : raw9326step2Labels = raw9326step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9326step2 raw9326step2Labels = mixedMoment B raw9326step3 raw9326step3Labels := by
      have ha : raw9326step3 = raw9326step2 := by apply Matrix.ext; unfold raw9326step3 raw9326step2; decide +kernel
      have hl : raw9326step2Labels = labelEmbedding1 ∘ raw9326step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9326step2 raw9326step2Labels raw9326step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

def raw9327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9327Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9327step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw9327step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw9327step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9327 raw9327Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw9327 raw9327Labels = mixedMoment B raw9327step0 raw9327step0Labels := by
      have hz : ∀ j, raw9327 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9327step0 = (fun i j => raw9327 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9327step0 raw9327; decide +kernel
      have hl : raw9327step0Labels = raw9327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9327 raw9327Labels permutation265 hz
    mixedMoment B raw9327step0 raw9327step0Labels = mixedMoment B raw9327step1 raw9327step1Labels := by
      have ha : raw9327step1 = (fun i j => raw9327step0 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9327step1 raw9327step0; decide +kernel
      have hl : raw9327step1Labels = raw9327step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9327step0 raw9327step0Labels permutation145 permutation5
    mixedMoment B raw9327step1 raw9327step1Labels = mixedMoment B raw9327step2 raw9327step2Labels := by
      have ha : raw9327step2 = raw9327step1 := by apply Matrix.ext; unfold raw9327step2 raw9327step1; decide +kernel
      have hl : raw9327step1Labels = labelEmbedding1 ∘ raw9327step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9327step1 raw9327step1Labels raw9327step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2702 node2702Labels := by rfl

def raw9328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9328Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9328step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9328 raw9328Labels = mixedMoment B node2700 node2700Labels := by
  calc
    mixedMoment B raw9328 raw9328Labels = mixedMoment B raw9328step0 raw9328step0Labels := by
      have ha : raw9328step0 = (fun i j => raw9328 (permutation664 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9328step0 raw9328; decide +kernel
      have hl : raw9328step0Labels = raw9328Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9328 raw9328Labels permutation664 permutation5
    mixedMoment B raw9328step0 raw9328step0Labels = mixedMoment B raw9328step1 raw9328step1Labels := by
      have ha : raw9328step1 = raw9328step0 := by apply Matrix.ext; unfold raw9328step1 raw9328step0; decide +kernel
      have hl : raw9328step0Labels = labelEmbedding1 ∘ raw9328step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9328step0 raw9328step0Labels raw9328step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2700 node2700Labels := by rfl

def raw9329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9329Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9329step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw9329step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw9329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9329 raw9329Labels = mixedMoment B node2706 node2706Labels := by
  calc
    mixedMoment B raw9329 raw9329Labels = mixedMoment B raw9329step0 raw9329step0Labels := by
      have hz : ∀ j, raw9329 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9329step0 = (fun i j => raw9329 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9329step0 raw9329; decide +kernel
      have hl : raw9329step0Labels = raw9329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9329 raw9329Labels permutation265 hz
    mixedMoment B raw9329step0 raw9329step0Labels = mixedMoment B raw9329step1 raw9329step1Labels := by
      have ha : raw9329step1 = (fun i j => raw9329step0 (permutation144 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9329step1 raw9329step0; decide +kernel
      have hl : raw9329step1Labels = raw9329step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9329step0 raw9329step0Labels permutation144 permutation5
    mixedMoment B raw9329step1 raw9329step1Labels = mixedMoment B raw9329step2 raw9329step2Labels := by
      have ha : raw9329step2 = raw9329step1 := by apply Matrix.ext; unfold raw9329step2 raw9329step1; decide +kernel
      have hl : raw9329step1Labels = labelEmbedding1 ∘ raw9329step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9329step1 raw9329step1Labels raw9329step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2706 node2706Labels := by rfl

def raw9330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9330Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw9330step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9330step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9330 raw9330Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw9330 raw9330Labels = mixedMoment B raw9330step0 raw9330step0Labels := by
      have hz : ∀ j, raw9330 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9330step0 = (fun i j => raw9330 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9330step0 raw9330; decide +kernel
      have hl : raw9330step0Labels = raw9330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9330 raw9330Labels permutation265 hz
    mixedMoment B raw9330step0 raw9330step0Labels = mixedMoment B raw9330step1 raw9330step1Labels := by
      have ha : raw9330step1 = (fun i j => raw9330step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9330step1 raw9330step0; decide +kernel
      have hl : raw9330step1Labels = raw9330step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9330step0 raw9330step0Labels permutation143 permutation5
    mixedMoment B raw9330step1 raw9330step1Labels = mixedMoment B raw9330step2 raw9330step2Labels := by
      have ha : raw9330step2 = raw9330step1 := by apply Matrix.ext; unfold raw9330step2 raw9330step1; decide +kernel
      have hl : raw9330step1Labels = labelEmbedding1 ∘ raw9330step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9330step1 raw9330step1Labels raw9330step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2738 node2738Labels := by rfl

def raw9331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9331Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw9331step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw9331step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9331step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9331step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw9331step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9331 raw9331Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw9331 raw9331Labels = mixedMoment B raw9331step0 raw9331step0Labels := by
      have hz : ∀ j, raw9331 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9331step0 = (fun i j => raw9331 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9331step0 raw9331; decide +kernel
      have hl : raw9331step0Labels = raw9331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9331 raw9331Labels permutation265 hz
    mixedMoment B raw9331step0 raw9331step0Labels = mixedMoment B raw9331step1 raw9331step1Labels := by
      have ha : raw9331step1 = (fun i j => raw9331step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9331step1 raw9331step0; decide +kernel
      have hl : raw9331step1Labels = raw9331step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9331step0 raw9331step0Labels permutation50 permutation7
    mixedMoment B raw9331step1 raw9331step1Labels = mixedMoment B raw9331step2 raw9331step2Labels := by
      have ha : raw9331step2 = -raw9331step1 := by apply Matrix.ext; change ∀ i j, raw9331step2 i j = -(raw9331step1 i j); unfold raw9331step2 raw9331step1; decide +kernel
      have hl : raw9331step2Labels = raw9331step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9331step2 raw9331step2Labels = mixedMoment B raw9331step3 raw9331step3Labels := by
      have ha : raw9331step3 = raw9331step2 := by apply Matrix.ext; unfold raw9331step3 raw9331step2; decide +kernel
      have hl : raw9331step2Labels = labelEmbedding1 ∘ raw9331step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9331step2 raw9331step2Labels raw9331step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

def raw9332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9332Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9332step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9332step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw9332step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9332step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw9332step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9332 raw9332Labels = mixedMoment B node2397 node2397Labels := by
  calc
    mixedMoment B raw9332 raw9332Labels = mixedMoment B raw9332step0 raw9332step0Labels := by
      have hz : ∀ j, raw9332 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9332step0 = (fun i j => raw9332 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9332step0 raw9332; decide +kernel
      have hl : raw9332step0Labels = raw9332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9332 raw9332Labels permutation265 hz
    mixedMoment B raw9332step0 raw9332step0Labels = mixedMoment B raw9332step1 raw9332step1Labels := by
      have ha : raw9332step1 = (fun i j => raw9332step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9332step1 raw9332step0; decide +kernel
      have hl : raw9332step1Labels = raw9332step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9332step0 raw9332step0Labels permutation149 permutation5
    mixedMoment B raw9332step1 raw9332step1Labels = mixedMoment B raw9332step2 raw9332step2Labels := by
      have ha : raw9332step2 = raw9332step1 := by apply Matrix.ext; unfold raw9332step2 raw9332step1; decide +kernel
      have hl : raw9332step1Labels = labelEmbedding1 ∘ raw9332step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9332step1 raw9332step1Labels raw9332step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2397 node2397Labels := by rfl

def raw9333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9333Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9333step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9333step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9333step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9333step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9333 raw9333Labels = mixedMoment B node2396 node2396Labels := by
  calc
    mixedMoment B raw9333 raw9333Labels = mixedMoment B raw9333step0 raw9333step0Labels := by
      have ha : raw9333step0 = (fun i j => raw9333 (permutation682 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9333step0 raw9333; decide +kernel
      have hl : raw9333step0Labels = raw9333Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9333 raw9333Labels permutation682 permutation5
    mixedMoment B raw9333step0 raw9333step0Labels = mixedMoment B raw9333step1 raw9333step1Labels := by
      have ha : raw9333step1 = raw9333step0 := by apply Matrix.ext; unfold raw9333step1 raw9333step0; decide +kernel
      have hl : raw9333step0Labels = labelEmbedding1 ∘ raw9333step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9333step0 raw9333step0Labels raw9333step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2396 node2396Labels := by rfl

def raw9334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9334Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9334step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9334step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9334step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9334step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9334step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9334 raw9334Labels = mixedMoment B node2401 node2401Labels := by
  calc
    mixedMoment B raw9334 raw9334Labels = mixedMoment B raw9334step0 raw9334step0Labels := by
      have hz : ∀ j, raw9334 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9334step0 = (fun i j => raw9334 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9334step0 raw9334; decide +kernel
      have hl : raw9334step0Labels = raw9334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9334 raw9334Labels permutation265 hz
    mixedMoment B raw9334step0 raw9334step0Labels = mixedMoment B raw9334step1 raw9334step1Labels := by
      have ha : raw9334step1 = (fun i j => raw9334step0 (permutation150 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9334step1 raw9334step0; decide +kernel
      have hl : raw9334step1Labels = raw9334step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9334step0 raw9334step0Labels permutation150 permutation5
    mixedMoment B raw9334step1 raw9334step1Labels = mixedMoment B raw9334step2 raw9334step2Labels := by
      have ha : raw9334step2 = raw9334step1 := by apply Matrix.ext; unfold raw9334step2 raw9334step1; decide +kernel
      have hl : raw9334step1Labels = labelEmbedding1 ∘ raw9334step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9334step1 raw9334step1Labels raw9334step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2401 node2401Labels := by rfl

def raw9335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9335Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -1, -1], ![2, -3, 1]]
def raw9335step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9335step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9335step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9335step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9335 raw9335Labels = mixedMoment B node2401 node2401Labels := by
  calc
    mixedMoment B raw9335 raw9335Labels = mixedMoment B raw9335step0 raw9335step0Labels := by
      have hz : ∀ j, raw9335 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9335step0 = (fun i j => raw9335 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9335step0 raw9335; decide +kernel
      have hl : raw9335step0Labels = raw9335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9335 raw9335Labels permutation265 hz
    mixedMoment B raw9335step0 raw9335step0Labels = mixedMoment B raw9335step1 raw9335step1Labels := by
      have ha : raw9335step1 = (fun i j => raw9335step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9335step1 raw9335step0; decide +kernel
      have hl : raw9335step1Labels = raw9335step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9335step0 raw9335step0Labels permutation148 permutation5
    mixedMoment B raw9335step1 raw9335step1Labels = mixedMoment B raw9335step2 raw9335step2Labels := by
      have ha : raw9335step2 = raw9335step1 := by apply Matrix.ext; unfold raw9335step2 raw9335step1; decide +kernel
      have hl : raw9335step1Labels = labelEmbedding1 ∘ raw9335step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9335step1 raw9335step1Labels raw9335step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2401 node2401Labels := by rfl

def raw9336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw9336Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw9336step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw9336step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9336step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9336step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9336step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9336step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9336 raw9336Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw9336 raw9336Labels = mixedMoment B raw9336step0 raw9336step0Labels := by
      have hz : ∀ j, raw9336 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9336step0 = (fun i j => raw9336 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9336step0 raw9336; decide +kernel
      have hl : raw9336step0Labels = raw9336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9336 raw9336Labels permutation265 hz
    mixedMoment B raw9336step0 raw9336step0Labels = mixedMoment B raw9336step1 raw9336step1Labels := by
      have ha : raw9336step1 = (fun i j => raw9336step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9336step1 raw9336step0; decide +kernel
      have hl : raw9336step1Labels = raw9336step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9336step0 raw9336step0Labels permutation50 permutation7
    mixedMoment B raw9336step1 raw9336step1Labels = mixedMoment B raw9336step2 raw9336step2Labels := by
      have ha : raw9336step2 = -raw9336step1 := by apply Matrix.ext; change ∀ i j, raw9336step2 i j = -(raw9336step1 i j); unfold raw9336step2 raw9336step1; decide +kernel
      have hl : raw9336step2Labels = raw9336step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9336step2 raw9336step2Labels = mixedMoment B raw9336step3 raw9336step3Labels := by
      have ha : raw9336step3 = raw9336step2 := by apply Matrix.ext; unfold raw9336step3 raw9336step2; decide +kernel
      have hl : raw9336step2Labels = labelEmbedding1 ∘ raw9336step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9336step2 raw9336step2Labels raw9336step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3580 node3580Labels := by rfl

def raw9337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9337Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9337step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9337step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw9337step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9337step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw9337step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9337 raw9337Labels = mixedMoment B node997 node997Labels := by
  calc
    mixedMoment B raw9337 raw9337Labels = mixedMoment B raw9337step0 raw9337step0Labels := by
      have hz : ∀ j, raw9337 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9337step0 = (fun i j => raw9337 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9337step0 raw9337; decide +kernel
      have hl : raw9337step0Labels = raw9337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9337 raw9337Labels permutation265 hz
    mixedMoment B raw9337step0 raw9337step0Labels = mixedMoment B raw9337step1 raw9337step1Labels := by
      have ha : raw9337step1 = (fun i j => raw9337step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9337step1 raw9337step0; decide +kernel
      have hl : raw9337step1Labels = raw9337step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9337step0 raw9337step0Labels permutation149 permutation5
    mixedMoment B raw9337step1 raw9337step1Labels = mixedMoment B raw9337step2 raw9337step2Labels := by
      have ha : raw9337step2 = raw9337step1 := by apply Matrix.ext; unfold raw9337step2 raw9337step1; decide +kernel
      have hl : raw9337step1Labels = labelEmbedding1 ∘ raw9337step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9337step1 raw9337step1Labels raw9337step2Labels labelEmbedding1 hl
    _ = mixedMoment B node997 node997Labels := by rfl

def raw9338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9338Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9338step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9338 raw9338Labels = mixedMoment B node995 node995Labels := by
  calc
    mixedMoment B raw9338 raw9338Labels = mixedMoment B raw9338step0 raw9338step0Labels := by
      have ha : raw9338step0 = (fun i j => raw9338 (permutation682 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9338step0 raw9338; decide +kernel
      have hl : raw9338step0Labels = raw9338Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9338 raw9338Labels permutation682 permutation5
    mixedMoment B raw9338step0 raw9338step0Labels = mixedMoment B raw9338step1 raw9338step1Labels := by
      have ha : raw9338step1 = raw9338step0 := by apply Matrix.ext; unfold raw9338step1 raw9338step0; decide +kernel
      have hl : raw9338step0Labels = labelEmbedding1 ∘ raw9338step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9338step0 raw9338step0Labels raw9338step1Labels labelEmbedding1 hl
    _ = mixedMoment B node995 node995Labels := by rfl

def raw9339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9339Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9339step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9339step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9339step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9339step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9339 raw9339Labels = mixedMoment B node1001 node1001Labels := by
  calc
    mixedMoment B raw9339 raw9339Labels = mixedMoment B raw9339step0 raw9339step0Labels := by
      have hz : ∀ j, raw9339 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9339step0 = (fun i j => raw9339 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9339step0 raw9339; decide +kernel
      have hl : raw9339step0Labels = raw9339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9339 raw9339Labels permutation265 hz
    mixedMoment B raw9339step0 raw9339step0Labels = mixedMoment B raw9339step1 raw9339step1Labels := by
      have ha : raw9339step1 = (fun i j => raw9339step0 (permutation150 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9339step1 raw9339step0; decide +kernel
      have hl : raw9339step1Labels = raw9339step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9339step0 raw9339step0Labels permutation150 permutation5
    mixedMoment B raw9339step1 raw9339step1Labels = mixedMoment B raw9339step2 raw9339step2Labels := by
      have ha : raw9339step2 = raw9339step1 := by apply Matrix.ext; unfold raw9339step2 raw9339step1; decide +kernel
      have hl : raw9339step1Labels = labelEmbedding1 ∘ raw9339step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9339step1 raw9339step1Labels raw9339step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1001 node1001Labels := by rfl

def raw9340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9340Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -4, 1]]
def raw9340step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9340step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9340step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw9340step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9340 raw9340Labels = mixedMoment B node1001 node1001Labels := by
  calc
    mixedMoment B raw9340 raw9340Labels = mixedMoment B raw9340step0 raw9340step0Labels := by
      have hz : ∀ j, raw9340 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9340step0 = (fun i j => raw9340 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9340step0 raw9340; decide +kernel
      have hl : raw9340step0Labels = raw9340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9340 raw9340Labels permutation265 hz
    mixedMoment B raw9340step0 raw9340step0Labels = mixedMoment B raw9340step1 raw9340step1Labels := by
      have ha : raw9340step1 = (fun i j => raw9340step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9340step1 raw9340step0; decide +kernel
      have hl : raw9340step1Labels = raw9340step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9340step0 raw9340step0Labels permutation148 permutation5
    mixedMoment B raw9340step1 raw9340step1Labels = mixedMoment B raw9340step2 raw9340step2Labels := by
      have ha : raw9340step2 = raw9340step1 := by apply Matrix.ext; unfold raw9340step2 raw9340step1; decide +kernel
      have hl : raw9340step1Labels = labelEmbedding1 ∘ raw9340step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9340step1 raw9340step1Labels raw9340step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1001 node1001Labels := by rfl

def raw9341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -4, 1]]
def raw9341Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -4, 1]]
def raw9341step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9341step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9341step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9341step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9341 raw9341Labels = mixedMoment B node1078 node1078Labels := by
  calc
    mixedMoment B raw9341 raw9341Labels = mixedMoment B raw9341step0 raw9341step0Labels := by
      have hz : ∀ j, raw9341 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9341step0 = (fun i j => raw9341 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9341step0 raw9341; decide +kernel
      have hl : raw9341step0Labels = raw9341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9341 raw9341Labels permutation265 hz
    mixedMoment B raw9341step0 raw9341step0Labels = mixedMoment B raw9341step1 raw9341step1Labels := by
      have ha : raw9341step1 = (fun i j => raw9341step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9341step1 raw9341step0; decide +kernel
      have hl : raw9341step1Labels = raw9341step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9341step0 raw9341step0Labels permutation137 permutation5
    mixedMoment B raw9341step1 raw9341step1Labels = mixedMoment B raw9341step2 raw9341step2Labels := by
      have ha : raw9341step2 = raw9341step1 := by apply Matrix.ext; unfold raw9341step2 raw9341step1; decide +kernel
      have hl : raw9341step1Labels = labelEmbedding1 ∘ raw9341step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9341step1 raw9341step1Labels raw9341step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1078 node1078Labels := by rfl

def raw9342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9342Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9342step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9342 raw9342Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw9342 raw9342Labels = mixedMoment B raw9342step0 raw9342step0Labels := by
      have hz : ∀ j, raw9342 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9342step0 = (fun i j => raw9342 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9342step0 raw9342; decide +kernel
      have hl : raw9342step0Labels = raw9342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9342 raw9342Labels permutation265 hz
    _ = mixedMoment B node2754 node2754Labels := by rfl

def raw9343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw9343Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9343step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw9343step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9343 raw9343Labels = mixedMoment B node1250 node1250Labels := by
  calc
    mixedMoment B raw9343 raw9343Labels = mixedMoment B raw9343step0 raw9343step0Labels := by
      have ha : raw9343step0 = (fun i j => raw9343 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9343step0 raw9343; decide +kernel
      have hl : raw9343step0Labels = raw9343Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9343 raw9343Labels permutation182 permutation2
    _ = mixedMoment B node1250 node1250Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
