import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw34048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw34048Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34048step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw34048step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34048step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw34048step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34048 raw34048Labels = mixedMoment B node2941 node2941Labels := by
  calc
    mixedMoment B raw34048 raw34048Labels = mixedMoment B raw34048step0 raw34048step0Labels := by
      have hz : ∀ j, raw34048 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34048step0 = (fun i j => raw34048 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34048step0 raw34048; decide +kernel
      have hl : raw34048step0Labels = raw34048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34048 raw34048Labels permutation520 hz
    mixedMoment B raw34048step0 raw34048step0Labels = mixedMoment B raw34048step1 raw34048step1Labels := by
      have ha : raw34048step1 = (fun i j => raw34048step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34048step1 raw34048step0; decide +kernel
      have hl : raw34048step1Labels = raw34048step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34048step0 raw34048step0Labels permutation151 permutation3
    mixedMoment B raw34048step1 raw34048step1Labels = mixedMoment B raw34048step2 raw34048step2Labels := by
      have ha : raw34048step2 = -raw34048step1 := by apply Matrix.ext; change ∀ i j, raw34048step2 i j = -(raw34048step1 i j); unfold raw34048step2 raw34048step1; decide +kernel
      have hl : raw34048step2Labels = raw34048step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2941 node2941Labels := by rfl

def raw34049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34049Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34049step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34049step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34049step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34049step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34049step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34049 raw34049Labels = mixedMoment B node2661 node2661Labels := by
  calc
    mixedMoment B raw34049 raw34049Labels = mixedMoment B raw34049step0 raw34049step0Labels := by
      have ha : raw34049step0 = (fun i j => raw34049 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34049step0 raw34049; decide +kernel
      have hl : raw34049step0Labels = raw34049Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34049 raw34049Labels permutation160 permutation7
    mixedMoment B raw34049step0 raw34049step0Labels = mixedMoment B raw34049step1 raw34049step1Labels := by
      have ha : raw34049step1 = -raw34049step0 := by apply Matrix.ext; change ∀ i j, raw34049step1 i j = -(raw34049step0 i j); unfold raw34049step1 raw34049step0; decide +kernel
      have hl : raw34049step1Labels = raw34049step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34049step1 raw34049step1Labels = mixedMoment B raw34049step2 raw34049step2Labels := by
      have ha : raw34049step2 = raw34049step1 := by apply Matrix.ext; unfold raw34049step2 raw34049step1; decide +kernel
      have hl : raw34049step1Labels = labelEmbedding1 ∘ raw34049step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34049step1 raw34049step1Labels raw34049step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2661 node2661Labels := by rfl

def raw34050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34050Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw34050step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw34050step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34050step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw34050step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34050 raw34050Labels = mixedMoment B node2708 node2708Labels := by
  calc
    mixedMoment B raw34050 raw34050Labels = mixedMoment B raw34050step0 raw34050step0Labels := by
      have ha : raw34050step0 = (fun i j => raw34050 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34050step0 raw34050; decide +kernel
      have hl : raw34050step0Labels = raw34050Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34050 raw34050Labels permutation160 permutation7
    mixedMoment B raw34050step0 raw34050step0Labels = mixedMoment B raw34050step1 raw34050step1Labels := by
      have ha : raw34050step1 = -raw34050step0 := by apply Matrix.ext; change ∀ i j, raw34050step1 i j = -(raw34050step0 i j); unfold raw34050step1 raw34050step0; decide +kernel
      have hl : raw34050step1Labels = raw34050step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34050step1 raw34050step1Labels = mixedMoment B raw34050step2 raw34050step2Labels := by
      have ha : raw34050step2 = raw34050step1 := by apply Matrix.ext; unfold raw34050step2 raw34050step1; decide +kernel
      have hl : raw34050step1Labels = labelEmbedding1 ∘ raw34050step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34050step1 raw34050step1Labels raw34050step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2708 node2708Labels := by rfl

def raw34051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34051Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34051step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34051step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34051step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34051step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34051step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34051step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34051 raw34051Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw34051 raw34051Labels = mixedMoment B raw34051step0 raw34051step0Labels := by
      have hz : ∀ j, raw34051 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34051step0 = (fun i j => raw34051 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34051step0 raw34051; decide +kernel
      have hl : raw34051step0Labels = raw34051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34051 raw34051Labels permutation434 hz
    mixedMoment B raw34051step0 raw34051step0Labels = mixedMoment B raw34051step1 raw34051step1Labels := by
      have ha : raw34051step1 = (fun i j => raw34051step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34051step1 raw34051step0; decide +kernel
      have hl : raw34051step1Labels = raw34051step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34051step0 raw34051step0Labels permutation34 permutation7
    mixedMoment B raw34051step1 raw34051step1Labels = mixedMoment B raw34051step2 raw34051step2Labels := by
      have ha : raw34051step2 = -raw34051step1 := by apply Matrix.ext; change ∀ i j, raw34051step2 i j = -(raw34051step1 i j); unfold raw34051step2 raw34051step1; decide +kernel
      have hl : raw34051step2Labels = raw34051step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34051step2 raw34051step2Labels = mixedMoment B raw34051step3 raw34051step3Labels := by
      have ha : raw34051step3 = raw34051step2 := by apply Matrix.ext; unfold raw34051step3 raw34051step2; decide +kernel
      have hl : raw34051step2Labels = labelEmbedding1 ∘ raw34051step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34051step2 raw34051step2Labels raw34051step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw34052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34052Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34052step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34052step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34052step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34052step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34052step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34052 raw34052Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw34052 raw34052Labels = mixedMoment B raw34052step0 raw34052step0Labels := by
      have hz : ∀ j, raw34052 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34052step0 = (fun i j => raw34052 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34052step0 raw34052; decide +kernel
      have hl : raw34052step0Labels = raw34052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34052 raw34052Labels permutation520 hz
    mixedMoment B raw34052step0 raw34052step0Labels = mixedMoment B raw34052step1 raw34052step1Labels := by
      have ha : raw34052step1 = (fun i j => raw34052step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34052step1 raw34052step0; decide +kernel
      have hl : raw34052step1Labels = raw34052step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34052step0 raw34052step0Labels permutation34 permutation7
    mixedMoment B raw34052step1 raw34052step1Labels = mixedMoment B raw34052step2 raw34052step2Labels := by
      have ha : raw34052step2 = -raw34052step1 := by apply Matrix.ext; change ∀ i j, raw34052step2 i j = -(raw34052step1 i j); unfold raw34052step2 raw34052step1; decide +kernel
      have hl : raw34052step2Labels = raw34052step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34052step2 raw34052step2Labels = mixedMoment B raw34052step3 raw34052step3Labels := by
      have ha : raw34052step3 = raw34052step2 := by apply Matrix.ext; unfold raw34052step3 raw34052step2; decide +kernel
      have hl : raw34052step2Labels = labelEmbedding1 ∘ raw34052step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34052step2 raw34052step2Labels raw34052step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw34053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34053Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw34053step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34053step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34053step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34053step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34053step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34053 raw34053Labels = mixedMoment B node2709 node2709Labels := by
  calc
    mixedMoment B raw34053 raw34053Labels = mixedMoment B raw34053step0 raw34053step0Labels := by
      have ha : raw34053step0 = (fun i j => raw34053 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34053step0 raw34053; decide +kernel
      have hl : raw34053step0Labels = raw34053Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34053 raw34053Labels permutation160 permutation7
    mixedMoment B raw34053step0 raw34053step0Labels = mixedMoment B raw34053step1 raw34053step1Labels := by
      have ha : raw34053step1 = -raw34053step0 := by apply Matrix.ext; change ∀ i j, raw34053step1 i j = -(raw34053step0 i j); unfold raw34053step1 raw34053step0; decide +kernel
      have hl : raw34053step1Labels = raw34053step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34053step1 raw34053step1Labels = mixedMoment B raw34053step2 raw34053step2Labels := by
      have ha : raw34053step2 = raw34053step1 := by apply Matrix.ext; unfold raw34053step2 raw34053step1; decide +kernel
      have hl : raw34053step1Labels = labelEmbedding1 ∘ raw34053step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34053step1 raw34053step1Labels raw34053step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2709 node2709Labels := by rfl

def raw34054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34054Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34054step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34054step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34054step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34054step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34054step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34054step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34054 raw34054Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw34054 raw34054Labels = mixedMoment B raw34054step0 raw34054step0Labels := by
      have hz : ∀ j, raw34054 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw34054step0 = (fun i j => raw34054 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw34054step0 raw34054; decide +kernel
      have hl : raw34054step0Labels = raw34054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34054 raw34054Labels permutation265 hz
    mixedMoment B raw34054step0 raw34054step0Labels = mixedMoment B raw34054step1 raw34054step1Labels := by
      have ha : raw34054step1 = (fun i j => raw34054step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34054step1 raw34054step0; decide +kernel
      have hl : raw34054step1Labels = raw34054step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34054step0 raw34054step0Labels permutation40 permutation7
    mixedMoment B raw34054step1 raw34054step1Labels = mixedMoment B raw34054step2 raw34054step2Labels := by
      have ha : raw34054step2 = -raw34054step1 := by apply Matrix.ext; change ∀ i j, raw34054step2 i j = -(raw34054step1 i j); unfold raw34054step2 raw34054step1; decide +kernel
      have hl : raw34054step2Labels = raw34054step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34054step2 raw34054step2Labels = mixedMoment B raw34054step3 raw34054step3Labels := by
      have ha : raw34054step3 = raw34054step2 := by apply Matrix.ext; unfold raw34054step3 raw34054step2; decide +kernel
      have hl : raw34054step2Labels = labelEmbedding1 ∘ raw34054step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34054step2 raw34054step2Labels raw34054step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1707 node1707Labels := by rfl

def raw34055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34055Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34055step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw34055step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34055step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw34055step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34055step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw34055step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34055 raw34055Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw34055 raw34055Labels = mixedMoment B raw34055step0 raw34055step0Labels := by
      have hz : ∀ j, raw34055 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw34055step0 = (fun i j => raw34055 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw34055step0 raw34055; decide +kernel
      have hl : raw34055step0Labels = raw34055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34055 raw34055Labels permutation265 hz
    mixedMoment B raw34055step0 raw34055step0Labels = mixedMoment B raw34055step1 raw34055step1Labels := by
      have ha : raw34055step1 = (fun i j => raw34055step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34055step1 raw34055step0; decide +kernel
      have hl : raw34055step1Labels = raw34055step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34055step0 raw34055step0Labels permutation40 permutation7
    mixedMoment B raw34055step1 raw34055step1Labels = mixedMoment B raw34055step2 raw34055step2Labels := by
      have ha : raw34055step2 = -raw34055step1 := by apply Matrix.ext; change ∀ i j, raw34055step2 i j = -(raw34055step1 i j); unfold raw34055step2 raw34055step1; decide +kernel
      have hl : raw34055step2Labels = raw34055step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34055step2 raw34055step2Labels = mixedMoment B raw34055step3 raw34055step3Labels := by
      have ha : raw34055step3 = raw34055step2 := by apply Matrix.ext; unfold raw34055step3 raw34055step2; decide +kernel
      have hl : raw34055step2Labels = labelEmbedding1 ∘ raw34055step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34055step2 raw34055step2Labels raw34055step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2242 node2242Labels := by rfl

def raw34056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34056Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34056step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34056step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34056step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34056step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34056step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34056step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34056step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34056step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34056step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34056 raw34056Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw34056 raw34056Labels = mixedMoment B raw34056step0 raw34056step0Labels := by
      have hz : ∀ j, raw34056 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34056step0 = (fun i j => raw34056 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34056step0 raw34056; decide +kernel
      have hl : raw34056step0Labels = raw34056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34056 raw34056Labels permutation434 hz
    mixedMoment B raw34056step0 raw34056step0Labels = mixedMoment B raw34056step1 raw34056step1Labels := by
      have hz : ∀ j, raw34056step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw34056step1 = (fun i j => raw34056step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw34056step1 raw34056step0; decide +kernel
      have hl : raw34056step1Labels = raw34056step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34056step0 raw34056step0Labels permutation56 hz
    mixedMoment B raw34056step1 raw34056step1Labels = mixedMoment B raw34056step2 raw34056step2Labels := by
      have ha : raw34056step2 = (fun i j => raw34056step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34056step2 raw34056step1; decide +kernel
      have hl : raw34056step2Labels = raw34056step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34056step1 raw34056step1Labels permutation10 permutation7
    mixedMoment B raw34056step2 raw34056step2Labels = mixedMoment B raw34056step3 raw34056step3Labels := by
      have ha : raw34056step3 = -raw34056step2 := by apply Matrix.ext; change ∀ i j, raw34056step3 i j = -(raw34056step2 i j); unfold raw34056step3 raw34056step2; decide +kernel
      have hl : raw34056step3Labels = raw34056step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34056step3 raw34056step3Labels = mixedMoment B raw34056step4 raw34056step4Labels := by
      have ha : raw34056step4 = raw34056step3 := by apply Matrix.ext; unfold raw34056step4 raw34056step3; decide +kernel
      have hl : raw34056step3Labels = labelEmbedding1 ∘ raw34056step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34056step3 raw34056step3Labels raw34056step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2264 node2264Labels := by rfl

def raw34057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34057Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34057step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34057step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34057step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34057step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34057step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34057step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34057step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34057step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34057step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34057 raw34057Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw34057 raw34057Labels = mixedMoment B raw34057step0 raw34057step0Labels := by
      have hz : ∀ j, raw34057 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34057step0 = (fun i j => raw34057 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34057step0 raw34057; decide +kernel
      have hl : raw34057step0Labels = raw34057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34057 raw34057Labels permutation520 hz
    mixedMoment B raw34057step0 raw34057step0Labels = mixedMoment B raw34057step1 raw34057step1Labels := by
      have hz : ∀ j, raw34057step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw34057step1 = (fun i j => raw34057step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw34057step1 raw34057step0; decide +kernel
      have hl : raw34057step1Labels = raw34057step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34057step0 raw34057step0Labels permutation56 hz
    mixedMoment B raw34057step1 raw34057step1Labels = mixedMoment B raw34057step2 raw34057step2Labels := by
      have ha : raw34057step2 = (fun i j => raw34057step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34057step2 raw34057step1; decide +kernel
      have hl : raw34057step2Labels = raw34057step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34057step1 raw34057step1Labels permutation10 permutation7
    mixedMoment B raw34057step2 raw34057step2Labels = mixedMoment B raw34057step3 raw34057step3Labels := by
      have ha : raw34057step3 = -raw34057step2 := by apply Matrix.ext; change ∀ i j, raw34057step3 i j = -(raw34057step2 i j); unfold raw34057step3 raw34057step2; decide +kernel
      have hl : raw34057step3Labels = raw34057step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34057step3 raw34057step3Labels = mixedMoment B raw34057step4 raw34057step4Labels := by
      have ha : raw34057step4 = raw34057step3 := by apply Matrix.ext; unfold raw34057step4 raw34057step3; decide +kernel
      have hl : raw34057step3Labels = labelEmbedding1 ∘ raw34057step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34057step3 raw34057step3Labels raw34057step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2264 node2264Labels := by rfl

def raw34058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34058Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34058step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw34058step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34058step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34058step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34058step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34058step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34058 raw34058Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw34058 raw34058Labels = mixedMoment B raw34058step0 raw34058step0Labels := by
      have hz : ∀ j, raw34058 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw34058step0 = (fun i j => raw34058 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw34058step0 raw34058; decide +kernel
      have hl : raw34058step0Labels = raw34058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34058 raw34058Labels permutation265 hz
    mixedMoment B raw34058step0 raw34058step0Labels = mixedMoment B raw34058step1 raw34058step1Labels := by
      have ha : raw34058step1 = (fun i j => raw34058step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34058step1 raw34058step0; decide +kernel
      have hl : raw34058step1Labels = raw34058step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34058step0 raw34058step0Labels permutation40 permutation7
    mixedMoment B raw34058step1 raw34058step1Labels = mixedMoment B raw34058step2 raw34058step2Labels := by
      have ha : raw34058step2 = -raw34058step1 := by apply Matrix.ext; change ∀ i j, raw34058step2 i j = -(raw34058step1 i j); unfold raw34058step2 raw34058step1; decide +kernel
      have hl : raw34058step2Labels = raw34058step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34058step2 raw34058step2Labels = mixedMoment B raw34058step3 raw34058step3Labels := by
      have ha : raw34058step3 = raw34058step2 := by apply Matrix.ext; unfold raw34058step3 raw34058step2; decide +kernel
      have hl : raw34058step2Labels = labelEmbedding1 ∘ raw34058step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34058step2 raw34058step2Labels raw34058step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2244 node2244Labels := by rfl

def raw34059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34059Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34059step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34059step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34059step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34059step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34059step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34059 raw34059Labels = mixedMoment B node1664 node1664Labels := by
  calc
    mixedMoment B raw34059 raw34059Labels = mixedMoment B raw34059step0 raw34059step0Labels := by
      have ha : raw34059step0 = (fun i j => raw34059 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34059step0 raw34059; decide +kernel
      have hl : raw34059step0Labels = raw34059Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34059 raw34059Labels permutation160 permutation7
    mixedMoment B raw34059step0 raw34059step0Labels = mixedMoment B raw34059step1 raw34059step1Labels := by
      have ha : raw34059step1 = -raw34059step0 := by apply Matrix.ext; change ∀ i j, raw34059step1 i j = -(raw34059step0 i j); unfold raw34059step1 raw34059step0; decide +kernel
      have hl : raw34059step1Labels = raw34059step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34059step1 raw34059step1Labels = mixedMoment B raw34059step2 raw34059step2Labels := by
      have ha : raw34059step2 = raw34059step1 := by apply Matrix.ext; unfold raw34059step2 raw34059step1; decide +kernel
      have hl : raw34059step1Labels = labelEmbedding1 ∘ raw34059step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34059step1 raw34059step1Labels raw34059step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1664 node1664Labels := by rfl

def raw34060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34060Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34060step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34060step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34060step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34060step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34060step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34060 raw34060Labels = mixedMoment B node2141 node2141Labels := by
  calc
    mixedMoment B raw34060 raw34060Labels = mixedMoment B raw34060step0 raw34060step0Labels := by
      have ha : raw34060step0 = (fun i j => raw34060 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34060step0 raw34060; decide +kernel
      have hl : raw34060step0Labels = raw34060Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34060 raw34060Labels permutation160 permutation7
    mixedMoment B raw34060step0 raw34060step0Labels = mixedMoment B raw34060step1 raw34060step1Labels := by
      have ha : raw34060step1 = -raw34060step0 := by apply Matrix.ext; change ∀ i j, raw34060step1 i j = -(raw34060step0 i j); unfold raw34060step1 raw34060step0; decide +kernel
      have hl : raw34060step1Labels = raw34060step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34060step1 raw34060step1Labels = mixedMoment B raw34060step2 raw34060step2Labels := by
      have ha : raw34060step2 = raw34060step1 := by apply Matrix.ext; unfold raw34060step2 raw34060step1; decide +kernel
      have hl : raw34060step1Labels = labelEmbedding1 ∘ raw34060step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34060step1 raw34060step1Labels raw34060step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2141 node2141Labels := by rfl

def raw34061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34061Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34061step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34061step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34061step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34061step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34061step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34061step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34061 raw34061Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw34061 raw34061Labels = mixedMoment B raw34061step0 raw34061step0Labels := by
      have hz : ∀ j, raw34061 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34061step0 = (fun i j => raw34061 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34061step0 raw34061; decide +kernel
      have hl : raw34061step0Labels = raw34061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34061 raw34061Labels permutation434 hz
    mixedMoment B raw34061step0 raw34061step0Labels = mixedMoment B raw34061step1 raw34061step1Labels := by
      have ha : raw34061step1 = (fun i j => raw34061step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34061step1 raw34061step0; decide +kernel
      have hl : raw34061step1Labels = raw34061step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34061step0 raw34061step0Labels permutation34 permutation7
    mixedMoment B raw34061step1 raw34061step1Labels = mixedMoment B raw34061step2 raw34061step2Labels := by
      have ha : raw34061step2 = -raw34061step1 := by apply Matrix.ext; change ∀ i j, raw34061step2 i j = -(raw34061step1 i j); unfold raw34061step2 raw34061step1; decide +kernel
      have hl : raw34061step2Labels = raw34061step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34061step2 raw34061step2Labels = mixedMoment B raw34061step3 raw34061step3Labels := by
      have ha : raw34061step3 = raw34061step2 := by apply Matrix.ext; unfold raw34061step3 raw34061step2; decide +kernel
      have hl : raw34061step2Labels = labelEmbedding1 ∘ raw34061step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34061step2 raw34061step2Labels raw34061step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

def raw34062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34062Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34062step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34062step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34062step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34062step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34062step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34062step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34062 raw34062Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw34062 raw34062Labels = mixedMoment B raw34062step0 raw34062step0Labels := by
      have hz : ∀ j, raw34062 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34062step0 = (fun i j => raw34062 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34062step0 raw34062; decide +kernel
      have hl : raw34062step0Labels = raw34062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34062 raw34062Labels permutation520 hz
    mixedMoment B raw34062step0 raw34062step0Labels = mixedMoment B raw34062step1 raw34062step1Labels := by
      have ha : raw34062step1 = (fun i j => raw34062step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34062step1 raw34062step0; decide +kernel
      have hl : raw34062step1Labels = raw34062step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34062step0 raw34062step0Labels permutation34 permutation7
    mixedMoment B raw34062step1 raw34062step1Labels = mixedMoment B raw34062step2 raw34062step2Labels := by
      have ha : raw34062step2 = -raw34062step1 := by apply Matrix.ext; change ∀ i j, raw34062step2 i j = -(raw34062step1 i j); unfold raw34062step2 raw34062step1; decide +kernel
      have hl : raw34062step2Labels = raw34062step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34062step2 raw34062step2Labels = mixedMoment B raw34062step3 raw34062step3Labels := by
      have ha : raw34062step3 = raw34062step2 := by apply Matrix.ext; unfold raw34062step3 raw34062step2; decide +kernel
      have hl : raw34062step2Labels = labelEmbedding1 ∘ raw34062step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34062step2 raw34062step2Labels raw34062step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

def raw34063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34063Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34063step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34063step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34063step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34063step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34063step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34063step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34063 raw34063Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw34063 raw34063Labels = mixedMoment B raw34063step0 raw34063step0Labels := by
      have ha : raw34063step0 = (fun i j => raw34063 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34063step0 raw34063; decide +kernel
      have hl : raw34063step0Labels = raw34063Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34063 raw34063Labels permutation160 permutation7
    mixedMoment B raw34063step0 raw34063step0Labels = mixedMoment B raw34063step1 raw34063step1Labels := by
      have ha : raw34063step1 = -raw34063step0 := by apply Matrix.ext; change ∀ i j, raw34063step1 i j = -(raw34063step0 i j); unfold raw34063step1 raw34063step0; decide +kernel
      have hl : raw34063step1Labels = raw34063step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34063step1 raw34063step1Labels = mixedMoment B raw34063step2 raw34063step2Labels := by
      have ha : raw34063step2 = raw34063step1 := by apply Matrix.ext; unfold raw34063step2 raw34063step1; decide +kernel
      have hl : raw34063step1Labels = labelEmbedding1 ∘ raw34063step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34063step1 raw34063step1Labels raw34063step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2191 node2191Labels := by rfl

def raw34064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34064Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34064step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34064step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34064step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34064step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34064step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34064 raw34064Labels = mixedMoment B node1667 node1667Labels := by
  calc
    mixedMoment B raw34064 raw34064Labels = mixedMoment B raw34064step0 raw34064step0Labels := by
      have ha : raw34064step0 = (fun i j => raw34064 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34064step0 raw34064; decide +kernel
      have hl : raw34064step0Labels = raw34064Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34064 raw34064Labels permutation166 permutation7
    mixedMoment B raw34064step0 raw34064step0Labels = mixedMoment B raw34064step1 raw34064step1Labels := by
      have ha : raw34064step1 = -raw34064step0 := by apply Matrix.ext; change ∀ i j, raw34064step1 i j = -(raw34064step0 i j); unfold raw34064step1 raw34064step0; decide +kernel
      have hl : raw34064step1Labels = raw34064step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34064step1 raw34064step1Labels = mixedMoment B raw34064step2 raw34064step2Labels := by
      have ha : raw34064step2 = raw34064step1 := by apply Matrix.ext; unfold raw34064step2 raw34064step1; decide +kernel
      have hl : raw34064step1Labels = labelEmbedding1 ∘ raw34064step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34064step1 raw34064step1Labels raw34064step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1667 node1667Labels := by rfl

def raw34065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34065Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34065step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34065step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34065step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34065step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34065step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34065 raw34065Labels = mixedMoment B node2144 node2144Labels := by
  calc
    mixedMoment B raw34065 raw34065Labels = mixedMoment B raw34065step0 raw34065step0Labels := by
      have ha : raw34065step0 = (fun i j => raw34065 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34065step0 raw34065; decide +kernel
      have hl : raw34065step0Labels = raw34065Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34065 raw34065Labels permutation166 permutation7
    mixedMoment B raw34065step0 raw34065step0Labels = mixedMoment B raw34065step1 raw34065step1Labels := by
      have ha : raw34065step1 = -raw34065step0 := by apply Matrix.ext; change ∀ i j, raw34065step1 i j = -(raw34065step0 i j); unfold raw34065step1 raw34065step0; decide +kernel
      have hl : raw34065step1Labels = raw34065step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34065step1 raw34065step1Labels = mixedMoment B raw34065step2 raw34065step2Labels := by
      have ha : raw34065step2 = raw34065step1 := by apply Matrix.ext; unfold raw34065step2 raw34065step1; decide +kernel
      have hl : raw34065step1Labels = labelEmbedding1 ∘ raw34065step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34065step1 raw34065step1Labels raw34065step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2144 node2144Labels := by rfl

def raw34066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34066Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw34066step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34066step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw34066step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34066step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw34066step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34066 raw34066Labels = mixedMoment B node2194 node2194Labels := by
  calc
    mixedMoment B raw34066 raw34066Labels = mixedMoment B raw34066step0 raw34066step0Labels := by
      have ha : raw34066step0 = (fun i j => raw34066 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34066step0 raw34066; decide +kernel
      have hl : raw34066step0Labels = raw34066Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34066 raw34066Labels permutation166 permutation7
    mixedMoment B raw34066step0 raw34066step0Labels = mixedMoment B raw34066step1 raw34066step1Labels := by
      have ha : raw34066step1 = -raw34066step0 := by apply Matrix.ext; change ∀ i j, raw34066step1 i j = -(raw34066step0 i j); unfold raw34066step1 raw34066step0; decide +kernel
      have hl : raw34066step1Labels = raw34066step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34066step1 raw34066step1Labels = mixedMoment B raw34066step2 raw34066step2Labels := by
      have ha : raw34066step2 = raw34066step1 := by apply Matrix.ext; unfold raw34066step2 raw34066step1; decide +kernel
      have hl : raw34066step1Labels = labelEmbedding1 ∘ raw34066step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34066step1 raw34066step1Labels raw34066step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2194 node2194Labels := by rfl

def raw34067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw34067Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34067step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34067step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34067step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34067step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34067step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34067step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34067step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34067 raw34067Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw34067 raw34067Labels = mixedMoment B raw34067step0 raw34067step0Labels := by
      have hz : ∀ j, raw34067 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34067step0 = (fun i j => raw34067 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34067step0 raw34067; decide +kernel
      have hl : raw34067step0Labels = raw34067Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34067 raw34067Labels permutation520 hz
    mixedMoment B raw34067step0 raw34067step0Labels = mixedMoment B raw34067step1 raw34067step1Labels := by
      have ha : raw34067step1 = (fun i j => raw34067step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34067step1 raw34067step0; decide +kernel
      have hl : raw34067step1Labels = raw34067step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34067step0 raw34067step0Labels permutation34 permutation7
    mixedMoment B raw34067step1 raw34067step1Labels = mixedMoment B raw34067step2 raw34067step2Labels := by
      have ha : raw34067step2 = -raw34067step1 := by apply Matrix.ext; change ∀ i j, raw34067step2 i j = -(raw34067step1 i j); unfold raw34067step2 raw34067step1; decide +kernel
      have hl : raw34067step2Labels = raw34067step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34067step2 raw34067step2Labels = mixedMoment B raw34067step3 raw34067step3Labels := by
      have ha : raw34067step3 = raw34067step2 := by apply Matrix.ext; unfold raw34067step3 raw34067step2; decide +kernel
      have hl : raw34067step2Labels = labelEmbedding1 ∘ raw34067step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34067step2 raw34067step2Labels raw34067step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2215 node2215Labels := by rfl

def raw34068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34068Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw34068step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34068step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34068step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34068step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34068 raw34068Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw34068 raw34068Labels = mixedMoment B raw34068step0 raw34068step0Labels := by
      have ha : raw34068step0 = (fun i j => raw34068 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34068step0 raw34068; decide +kernel
      have hl : raw34068step0Labels = raw34068Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34068 raw34068Labels permutation166 permutation7
    mixedMoment B raw34068step0 raw34068step0Labels = mixedMoment B raw34068step1 raw34068step1Labels := by
      have ha : raw34068step1 = -raw34068step0 := by apply Matrix.ext; change ∀ i j, raw34068step1 i j = -(raw34068step0 i j); unfold raw34068step1 raw34068step0; decide +kernel
      have hl : raw34068step1Labels = raw34068step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34068step1 raw34068step1Labels = mixedMoment B raw34068step2 raw34068step2Labels := by
      have ha : raw34068step2 = raw34068step1 := by apply Matrix.ext; unfold raw34068step2 raw34068step1; decide +kernel
      have hl : raw34068step1Labels = labelEmbedding1 ∘ raw34068step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34068step1 raw34068step1Labels raw34068step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw34069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34069Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34069step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34069step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34069step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34069step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34069step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34069 raw34069Labels = mixedMoment B node1667 node1667Labels := by
  calc
    mixedMoment B raw34069 raw34069Labels = mixedMoment B raw34069step0 raw34069step0Labels := by
      have ha : raw34069step0 = (fun i j => raw34069 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34069step0 raw34069; decide +kernel
      have hl : raw34069step0Labels = raw34069Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34069 raw34069Labels permutation160 permutation7
    mixedMoment B raw34069step0 raw34069step0Labels = mixedMoment B raw34069step1 raw34069step1Labels := by
      have ha : raw34069step1 = -raw34069step0 := by apply Matrix.ext; change ∀ i j, raw34069step1 i j = -(raw34069step0 i j); unfold raw34069step1 raw34069step0; decide +kernel
      have hl : raw34069step1Labels = raw34069step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34069step1 raw34069step1Labels = mixedMoment B raw34069step2 raw34069step2Labels := by
      have ha : raw34069step2 = raw34069step1 := by apply Matrix.ext; unfold raw34069step2 raw34069step1; decide +kernel
      have hl : raw34069step1Labels = labelEmbedding1 ∘ raw34069step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34069step1 raw34069step1Labels raw34069step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1667 node1667Labels := by rfl

def raw34070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34070Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34070step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34070step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34070step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34070step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34070 raw34070Labels = mixedMoment B node2144 node2144Labels := by
  calc
    mixedMoment B raw34070 raw34070Labels = mixedMoment B raw34070step0 raw34070step0Labels := by
      have ha : raw34070step0 = (fun i j => raw34070 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34070step0 raw34070; decide +kernel
      have hl : raw34070step0Labels = raw34070Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34070 raw34070Labels permutation160 permutation7
    mixedMoment B raw34070step0 raw34070step0Labels = mixedMoment B raw34070step1 raw34070step1Labels := by
      have ha : raw34070step1 = -raw34070step0 := by apply Matrix.ext; change ∀ i j, raw34070step1 i j = -(raw34070step0 i j); unfold raw34070step1 raw34070step0; decide +kernel
      have hl : raw34070step1Labels = raw34070step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34070step1 raw34070step1Labels = mixedMoment B raw34070step2 raw34070step2Labels := by
      have ha : raw34070step2 = raw34070step1 := by apply Matrix.ext; unfold raw34070step2 raw34070step1; decide +kernel
      have hl : raw34070step1Labels = labelEmbedding1 ∘ raw34070step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34070step1 raw34070step1Labels raw34070step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2144 node2144Labels := by rfl

def raw34071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34071Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw34071step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw34071step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34071step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw34071step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34071 raw34071Labels = mixedMoment B node2194 node2194Labels := by
  calc
    mixedMoment B raw34071 raw34071Labels = mixedMoment B raw34071step0 raw34071step0Labels := by
      have ha : raw34071step0 = (fun i j => raw34071 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34071step0 raw34071; decide +kernel
      have hl : raw34071step0Labels = raw34071Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34071 raw34071Labels permutation160 permutation7
    mixedMoment B raw34071step0 raw34071step0Labels = mixedMoment B raw34071step1 raw34071step1Labels := by
      have ha : raw34071step1 = -raw34071step0 := by apply Matrix.ext; change ∀ i j, raw34071step1 i j = -(raw34071step0 i j); unfold raw34071step1 raw34071step0; decide +kernel
      have hl : raw34071step1Labels = raw34071step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34071step1 raw34071step1Labels = mixedMoment B raw34071step2 raw34071step2Labels := by
      have ha : raw34071step2 = raw34071step1 := by apply Matrix.ext; unfold raw34071step2 raw34071step1; decide +kernel
      have hl : raw34071step1Labels = labelEmbedding1 ∘ raw34071step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34071step1 raw34071step1Labels raw34071step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2194 node2194Labels := by rfl

def raw34072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34072Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34072step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34072step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34072step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34072step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34072step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34072step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34072step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34072 raw34072Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw34072 raw34072Labels = mixedMoment B raw34072step0 raw34072step0Labels := by
      have hz : ∀ j, raw34072 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34072step0 = (fun i j => raw34072 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34072step0 raw34072; decide +kernel
      have hl : raw34072step0Labels = raw34072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34072 raw34072Labels permutation434 hz
    mixedMoment B raw34072step0 raw34072step0Labels = mixedMoment B raw34072step1 raw34072step1Labels := by
      have ha : raw34072step1 = (fun i j => raw34072step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34072step1 raw34072step0; decide +kernel
      have hl : raw34072step1Labels = raw34072step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34072step0 raw34072step0Labels permutation34 permutation7
    mixedMoment B raw34072step1 raw34072step1Labels = mixedMoment B raw34072step2 raw34072step2Labels := by
      have ha : raw34072step2 = -raw34072step1 := by apply Matrix.ext; change ∀ i j, raw34072step2 i j = -(raw34072step1 i j); unfold raw34072step2 raw34072step1; decide +kernel
      have hl : raw34072step2Labels = raw34072step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34072step2 raw34072step2Labels = mixedMoment B raw34072step3 raw34072step3Labels := by
      have ha : raw34072step3 = raw34072step2 := by apply Matrix.ext; unfold raw34072step3 raw34072step2; decide +kernel
      have hl : raw34072step2Labels = labelEmbedding1 ∘ raw34072step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34072step2 raw34072step2Labels raw34072step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2215 node2215Labels := by rfl

def raw34073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34073Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw34073step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34073step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34073step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34073step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34073step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34073 raw34073Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw34073 raw34073Labels = mixedMoment B raw34073step0 raw34073step0Labels := by
      have ha : raw34073step0 = (fun i j => raw34073 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34073step0 raw34073; decide +kernel
      have hl : raw34073step0Labels = raw34073Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34073 raw34073Labels permutation160 permutation7
    mixedMoment B raw34073step0 raw34073step0Labels = mixedMoment B raw34073step1 raw34073step1Labels := by
      have ha : raw34073step1 = -raw34073step0 := by apply Matrix.ext; change ∀ i j, raw34073step1 i j = -(raw34073step0 i j); unfold raw34073step1 raw34073step0; decide +kernel
      have hl : raw34073step1Labels = raw34073step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34073step1 raw34073step1Labels = mixedMoment B raw34073step2 raw34073step2Labels := by
      have ha : raw34073step2 = raw34073step1 := by apply Matrix.ext; unfold raw34073step2 raw34073step1; decide +kernel
      have hl : raw34073step1Labels = labelEmbedding1 ∘ raw34073step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34073step1 raw34073step1Labels raw34073step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw34074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34074Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw34074step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34074step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw34074step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34074step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw34074step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34074 raw34074Labels = mixedMoment B node1663 node1663Labels := by
  calc
    mixedMoment B raw34074 raw34074Labels = mixedMoment B raw34074step0 raw34074step0Labels := by
      have ha : raw34074step0 = (fun i j => raw34074 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34074step0 raw34074; decide +kernel
      have hl : raw34074step0Labels = raw34074Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34074 raw34074Labels permutation160 permutation7
    mixedMoment B raw34074step0 raw34074step0Labels = mixedMoment B raw34074step1 raw34074step1Labels := by
      have ha : raw34074step1 = -raw34074step0 := by apply Matrix.ext; change ∀ i j, raw34074step1 i j = -(raw34074step0 i j); unfold raw34074step1 raw34074step0; decide +kernel
      have hl : raw34074step1Labels = raw34074step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34074step1 raw34074step1Labels = mixedMoment B raw34074step2 raw34074step2Labels := by
      have ha : raw34074step2 = raw34074step1 := by apply Matrix.ext; unfold raw34074step2 raw34074step1; decide +kernel
      have hl : raw34074step1Labels = labelEmbedding1 ∘ raw34074step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34074step1 raw34074step1Labels raw34074step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1663 node1663Labels := by rfl

def raw34075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34075Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw34075step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34075step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw34075step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34075step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw34075step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34075 raw34075Labels = mixedMoment B node2140 node2140Labels := by
  calc
    mixedMoment B raw34075 raw34075Labels = mixedMoment B raw34075step0 raw34075step0Labels := by
      have ha : raw34075step0 = (fun i j => raw34075 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34075step0 raw34075; decide +kernel
      have hl : raw34075step0Labels = raw34075Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34075 raw34075Labels permutation160 permutation7
    mixedMoment B raw34075step0 raw34075step0Labels = mixedMoment B raw34075step1 raw34075step1Labels := by
      have ha : raw34075step1 = -raw34075step0 := by apply Matrix.ext; change ∀ i j, raw34075step1 i j = -(raw34075step0 i j); unfold raw34075step1 raw34075step0; decide +kernel
      have hl : raw34075step1Labels = raw34075step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34075step1 raw34075step1Labels = mixedMoment B raw34075step2 raw34075step2Labels := by
      have ha : raw34075step2 = raw34075step1 := by apply Matrix.ext; unfold raw34075step2 raw34075step1; decide +kernel
      have hl : raw34075step1Labels = labelEmbedding1 ∘ raw34075step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34075step1 raw34075step1Labels raw34075step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2140 node2140Labels := by rfl

def raw34076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34076Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw34076step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34076step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw34076step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34076step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw34076step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34076 raw34076Labels = mixedMoment B node2189 node2189Labels := by
  calc
    mixedMoment B raw34076 raw34076Labels = mixedMoment B raw34076step0 raw34076step0Labels := by
      have ha : raw34076step0 = (fun i j => raw34076 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34076step0 raw34076; decide +kernel
      have hl : raw34076step0Labels = raw34076Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34076 raw34076Labels permutation160 permutation7
    mixedMoment B raw34076step0 raw34076step0Labels = mixedMoment B raw34076step1 raw34076step1Labels := by
      have ha : raw34076step1 = -raw34076step0 := by apply Matrix.ext; change ∀ i j, raw34076step1 i j = -(raw34076step0 i j); unfold raw34076step1 raw34076step0; decide +kernel
      have hl : raw34076step1Labels = raw34076step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34076step1 raw34076step1Labels = mixedMoment B raw34076step2 raw34076step2Labels := by
      have ha : raw34076step2 = raw34076step1 := by apply Matrix.ext; unfold raw34076step2 raw34076step1; decide +kernel
      have hl : raw34076step1Labels = labelEmbedding1 ∘ raw34076step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34076step1 raw34076step1Labels raw34076step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2189 node2189Labels := by rfl

def raw34077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw34077Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34077step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw34077step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34077step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw34077step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34077step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw34077step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34077 raw34077Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw34077 raw34077Labels = mixedMoment B raw34077step0 raw34077step0Labels := by
      have hz : ∀ j, raw34077 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34077step0 = (fun i j => raw34077 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34077step0 raw34077; decide +kernel
      have hl : raw34077step0Labels = raw34077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34077 raw34077Labels permutation434 hz
    mixedMoment B raw34077step0 raw34077step0Labels = mixedMoment B raw34077step1 raw34077step1Labels := by
      have ha : raw34077step1 = (fun i j => raw34077step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34077step1 raw34077step0; decide +kernel
      have hl : raw34077step1Labels = raw34077step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34077step0 raw34077step0Labels permutation34 permutation7
    mixedMoment B raw34077step1 raw34077step1Labels = mixedMoment B raw34077step2 raw34077step2Labels := by
      have ha : raw34077step2 = -raw34077step1 := by apply Matrix.ext; change ∀ i j, raw34077step2 i j = -(raw34077step1 i j); unfold raw34077step2 raw34077step1; decide +kernel
      have hl : raw34077step2Labels = raw34077step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34077step2 raw34077step2Labels = mixedMoment B raw34077step3 raw34077step3Labels := by
      have ha : raw34077step3 = raw34077step2 := by apply Matrix.ext; unfold raw34077step3 raw34077step2; decide +kernel
      have hl : raw34077step2Labels = labelEmbedding1 ∘ raw34077step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34077step2 raw34077step2Labels raw34077step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw34078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw34078Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34078step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw34078step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw34078step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34078step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw34078step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34078 raw34078Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw34078 raw34078Labels = mixedMoment B raw34078step0 raw34078step0Labels := by
      have hz : ∀ j, raw34078 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34078step0 = (fun i j => raw34078 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34078step0 raw34078; decide +kernel
      have hl : raw34078step0Labels = raw34078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34078 raw34078Labels permutation520 hz
    mixedMoment B raw34078step0 raw34078step0Labels = mixedMoment B raw34078step1 raw34078step1Labels := by
      have ha : raw34078step1 = (fun i j => raw34078step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34078step1 raw34078step0; decide +kernel
      have hl : raw34078step1Labels = raw34078step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34078step0 raw34078step0Labels permutation34 permutation7
    mixedMoment B raw34078step1 raw34078step1Labels = mixedMoment B raw34078step2 raw34078step2Labels := by
      have ha : raw34078step2 = -raw34078step1 := by apply Matrix.ext; change ∀ i j, raw34078step2 i j = -(raw34078step1 i j); unfold raw34078step2 raw34078step1; decide +kernel
      have hl : raw34078step2Labels = raw34078step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34078step2 raw34078step2Labels = mixedMoment B raw34078step3 raw34078step3Labels := by
      have ha : raw34078step3 = raw34078step2 := by apply Matrix.ext; unfold raw34078step3 raw34078step2; decide +kernel
      have hl : raw34078step2Labels = labelEmbedding1 ∘ raw34078step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34078step2 raw34078step2Labels raw34078step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw34079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34079step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34079 raw34079Labels = mixedMoment B node4248 node4248Labels := by
  calc
    mixedMoment B raw34079 raw34079Labels = mixedMoment B raw34079step0 raw34079step0Labels := by
      have ha : raw34079step0 = (fun i j => raw34079 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34079step0 raw34079; decide +kernel
      have hl : raw34079step0Labels = raw34079Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34079 raw34079Labels permutation152 permutation3
    mixedMoment B raw34079step0 raw34079step0Labels = mixedMoment B raw34079step1 raw34079step1Labels := by
      have ha : raw34079step1 = raw34079step0 := by apply Matrix.ext; unfold raw34079step1 raw34079step0; decide +kernel
      have hl : raw34079step0Labels = labelEmbedding6 ∘ raw34079step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34079step0 raw34079step0Labels raw34079step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4248 node4248Labels := by rfl

def raw34080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34080step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34080step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34080step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34080 raw34080Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw34080 raw34080Labels = mixedMoment B raw34080step0 raw34080step0Labels := by
      have ha : raw34080step0 = (fun i j => raw34080 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34080step0 raw34080; decide +kernel
      have hl : raw34080step0Labels = raw34080Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34080 raw34080Labels permutation176 permutation3
    mixedMoment B raw34080step0 raw34080step0Labels = mixedMoment B raw34080step1 raw34080step1Labels := by
      have ha : raw34080step1 = raw34080step0 := by apply Matrix.ext; unfold raw34080step1 raw34080step0; decide +kernel
      have hl : raw34080step0Labels = labelEmbedding6 ∘ raw34080step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34080step0 raw34080step0Labels raw34080step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

def raw34081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw34081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw34081step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34081step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34081step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34081step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34081step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34081 raw34081Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw34081 raw34081Labels = mixedMoment B raw34081step0 raw34081step0Labels := by
      have ha : raw34081step0 = (fun i j => raw34081 (permutation234 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34081step0 raw34081; decide +kernel
      have hl : raw34081step0Labels = raw34081Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34081 raw34081Labels permutation234 permutation5
    mixedMoment B raw34081step0 raw34081step0Labels = mixedMoment B raw34081step1 raw34081step1Labels := by
      have ha : raw34081step1 = -raw34081step0 := by apply Matrix.ext; change ∀ i j, raw34081step1 i j = -(raw34081step0 i j); unfold raw34081step1 raw34081step0; decide +kernel
      have hl : raw34081step1Labels = raw34081step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34081step1 raw34081step1Labels = mixedMoment B raw34081step2 raw34081step2Labels := by
      have ha : raw34081step2 = raw34081step1 := by apply Matrix.ext; unfold raw34081step2 raw34081step1; decide +kernel
      have hl : raw34081step1Labels = labelEmbedding8 ∘ raw34081step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34081step1 raw34081step1Labels raw34081step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

def raw34082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw34082step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34082step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw34082step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34082 raw34082Labels = mixedMoment B node4207 node4207Labels := by
  calc
    mixedMoment B raw34082 raw34082Labels = mixedMoment B raw34082step0 raw34082step0Labels := by
      have ha : raw34082step0 = (fun i j => raw34082 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34082step0 raw34082; decide +kernel
      have hl : raw34082step0Labels = raw34082Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34082 raw34082Labels permutation160 permutation3
    mixedMoment B raw34082step0 raw34082step0Labels = mixedMoment B raw34082step1 raw34082step1Labels := by
      have ha : raw34082step1 = raw34082step0 := by apply Matrix.ext; unfold raw34082step1 raw34082step0; decide +kernel
      have hl : raw34082step0Labels = labelEmbedding6 ∘ raw34082step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34082step0 raw34082step0Labels raw34082step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4207 node4207Labels := by rfl

def raw34083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34083step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw34083step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34083step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw34083step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34083 raw34083Labels = mixedMoment B node4640 node4640Labels := by
  calc
    mixedMoment B raw34083 raw34083Labels = mixedMoment B raw34083step0 raw34083step0Labels := by
      have ha : raw34083step0 = (fun i j => raw34083 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34083step0 raw34083; decide +kernel
      have hl : raw34083step0Labels = raw34083Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34083 raw34083Labels permutation160 permutation3
    mixedMoment B raw34083step0 raw34083step0Labels = mixedMoment B raw34083step1 raw34083step1Labels := by
      have ha : raw34083step1 = raw34083step0 := by apply Matrix.ext; unfold raw34083step1 raw34083step0; decide +kernel
      have hl : raw34083step0Labels = labelEmbedding6 ∘ raw34083step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34083step0 raw34083step0Labels raw34083step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4640 node4640Labels := by rfl

def raw34084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw34084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw34084step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34084step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34084step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34084step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34084step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34084 raw34084Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw34084 raw34084Labels = mixedMoment B raw34084step0 raw34084step0Labels := by
      have ha : raw34084step0 = (fun i j => raw34084 (permutation226 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34084step0 raw34084; decide +kernel
      have hl : raw34084step0Labels = raw34084Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34084 raw34084Labels permutation226 permutation5
    mixedMoment B raw34084step0 raw34084step0Labels = mixedMoment B raw34084step1 raw34084step1Labels := by
      have ha : raw34084step1 = -raw34084step0 := by apply Matrix.ext; change ∀ i j, raw34084step1 i j = -(raw34084step0 i j); unfold raw34084step1 raw34084step0; decide +kernel
      have hl : raw34084step1Labels = raw34084step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34084step1 raw34084step1Labels = mixedMoment B raw34084step2 raw34084step2Labels := by
      have ha : raw34084step2 = raw34084step1 := by apply Matrix.ext; unfold raw34084step2 raw34084step1; decide +kernel
      have hl : raw34084step1Labels = labelEmbedding8 ∘ raw34084step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34084step1 raw34084step1Labels raw34084step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4782 node4782Labels := by rfl

def raw34085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34085step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34085 raw34085Labels = mixedMoment B node4197 node4197Labels := by
  calc
    mixedMoment B raw34085 raw34085Labels = mixedMoment B raw34085step0 raw34085step0Labels := by
      have ha : raw34085step0 = (fun i j => raw34085 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34085step0 raw34085; decide +kernel
      have hl : raw34085step0Labels = raw34085Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34085 raw34085Labels permutation154 permutation3
    mixedMoment B raw34085step0 raw34085step0Labels = mixedMoment B raw34085step1 raw34085step1Labels := by
      have ha : raw34085step1 = raw34085step0 := by apply Matrix.ext; unfold raw34085step1 raw34085step0; decide +kernel
      have hl : raw34085step0Labels = labelEmbedding6 ∘ raw34085step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34085step0 raw34085step0Labels raw34085step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4197 node4197Labels := by rfl

def raw34086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34086step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34086 raw34086Labels = mixedMoment B node4632 node4632Labels := by
  calc
    mixedMoment B raw34086 raw34086Labels = mixedMoment B raw34086step0 raw34086step0Labels := by
      have ha : raw34086step0 = (fun i j => raw34086 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34086step0 raw34086; decide +kernel
      have hl : raw34086step0Labels = raw34086Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34086 raw34086Labels permutation154 permutation3
    mixedMoment B raw34086step0 raw34086step0Labels = mixedMoment B raw34086step1 raw34086step1Labels := by
      have ha : raw34086step1 = raw34086step0 := by apply Matrix.ext; unfold raw34086step1 raw34086step0; decide +kernel
      have hl : raw34086step0Labels = labelEmbedding6 ∘ raw34086step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34086step0 raw34086step0Labels raw34086step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4632 node4632Labels := by rfl

def raw34087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34087step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34087step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34087 raw34087Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw34087 raw34087Labels = mixedMoment B raw34087step0 raw34087step0Labels := by
      have ha : raw34087step0 = (fun i j => raw34087 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34087step0 raw34087; decide +kernel
      have hl : raw34087step0Labels = raw34087Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34087 raw34087Labels permutation154 permutation3
    mixedMoment B raw34087step0 raw34087step0Labels = mixedMoment B raw34087step1 raw34087step1Labels := by
      have ha : raw34087step1 = raw34087step0 := by apply Matrix.ext; unfold raw34087step1 raw34087step0; decide +kernel
      have hl : raw34087step0Labels = labelEmbedding6 ∘ raw34087step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34087step0 raw34087step0Labels raw34087step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4763 node4763Labels := by rfl

def raw34088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw34088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34088step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34088step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34088step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34088 raw34088Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw34088 raw34088Labels = mixedMoment B raw34088step0 raw34088step0Labels := by
      have ha : raw34088step0 = (fun i j => raw34088 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34088step0 raw34088; decide +kernel
      have hl : raw34088step0Labels = raw34088Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34088 raw34088Labels permutation164 permutation3
    mixedMoment B raw34088step0 raw34088step0Labels = mixedMoment B raw34088step1 raw34088step1Labels := by
      have ha : raw34088step1 = raw34088step0 := by apply Matrix.ext; unfold raw34088step1 raw34088step0; decide +kernel
      have hl : raw34088step0Labels = labelEmbedding6 ∘ raw34088step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34088step0 raw34088step0Labels raw34088step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4782 node4782Labels := by rfl

def raw34089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw34089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34089step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34089step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34089step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34089 raw34089Labels = mixedMoment B node4197 node4197Labels := by
  calc
    mixedMoment B raw34089 raw34089Labels = mixedMoment B raw34089step0 raw34089step0Labels := by
      have ha : raw34089step0 = (fun i j => raw34089 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34089step0 raw34089; decide +kernel
      have hl : raw34089step0Labels = raw34089Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34089 raw34089Labels permutation152 permutation3
    mixedMoment B raw34089step0 raw34089step0Labels = mixedMoment B raw34089step1 raw34089step1Labels := by
      have ha : raw34089step1 = raw34089step0 := by apply Matrix.ext; unfold raw34089step1 raw34089step0; decide +kernel
      have hl : raw34089step0Labels = labelEmbedding6 ∘ raw34089step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34089step0 raw34089step0Labels raw34089step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4197 node4197Labels := by rfl

def raw34090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw34090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34090step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34090step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34090 raw34090Labels = mixedMoment B node4632 node4632Labels := by
  calc
    mixedMoment B raw34090 raw34090Labels = mixedMoment B raw34090step0 raw34090step0Labels := by
      have ha : raw34090step0 = (fun i j => raw34090 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34090step0 raw34090; decide +kernel
      have hl : raw34090step0Labels = raw34090Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34090 raw34090Labels permutation152 permutation3
    mixedMoment B raw34090step0 raw34090step0Labels = mixedMoment B raw34090step1 raw34090step1Labels := by
      have ha : raw34090step1 = raw34090step0 := by apply Matrix.ext; unfold raw34090step1 raw34090step0; decide +kernel
      have hl : raw34090step0Labels = labelEmbedding6 ∘ raw34090step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34090step0 raw34090step0Labels raw34090step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4632 node4632Labels := by rfl

def raw34091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw34091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34091step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34091step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34091 raw34091Labels = mixedMoment B node4763 node4763Labels := by
  calc
    mixedMoment B raw34091 raw34091Labels = mixedMoment B raw34091step0 raw34091step0Labels := by
      have ha : raw34091step0 = (fun i j => raw34091 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34091step0 raw34091; decide +kernel
      have hl : raw34091step0Labels = raw34091Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34091 raw34091Labels permutation152 permutation3
    mixedMoment B raw34091step0 raw34091step0Labels = mixedMoment B raw34091step1 raw34091step1Labels := by
      have ha : raw34091step1 = raw34091step0 := by apply Matrix.ext; unfold raw34091step1 raw34091step0; decide +kernel
      have hl : raw34091step0Labels = labelEmbedding6 ∘ raw34091step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34091step0 raw34091step0Labels raw34091step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4763 node4763Labels := by rfl

def raw34092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw34092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34092step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34092step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34092step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34092 raw34092Labels = mixedMoment B node4195 node4195Labels := by
  calc
    mixedMoment B raw34092 raw34092Labels = mixedMoment B raw34092step0 raw34092step0Labels := by
      have ha : raw34092step0 = (fun i j => raw34092 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34092step0 raw34092; decide +kernel
      have hl : raw34092step0Labels = raw34092Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34092 raw34092Labels permutation152 permutation3
    mixedMoment B raw34092step0 raw34092step0Labels = mixedMoment B raw34092step1 raw34092step1Labels := by
      have ha : raw34092step1 = raw34092step0 := by apply Matrix.ext; unfold raw34092step1 raw34092step0; decide +kernel
      have hl : raw34092step0Labels = labelEmbedding6 ∘ raw34092step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34092step0 raw34092step0Labels raw34092step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4195 node4195Labels := by rfl

def raw34093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw34093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34093step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34093step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34093step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34093step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34093 raw34093Labels = mixedMoment B node4630 node4630Labels := by
  calc
    mixedMoment B raw34093 raw34093Labels = mixedMoment B raw34093step0 raw34093step0Labels := by
      have ha : raw34093step0 = (fun i j => raw34093 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34093step0 raw34093; decide +kernel
      have hl : raw34093step0Labels = raw34093Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34093 raw34093Labels permutation152 permutation3
    mixedMoment B raw34093step0 raw34093step0Labels = mixedMoment B raw34093step1 raw34093step1Labels := by
      have ha : raw34093step1 = raw34093step0 := by apply Matrix.ext; unfold raw34093step1 raw34093step0; decide +kernel
      have hl : raw34093step0Labels = labelEmbedding6 ∘ raw34093step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34093step0 raw34093step0Labels raw34093step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4630 node4630Labels := by rfl

def raw34094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw34094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34094step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34094step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw34094step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34094 raw34094Labels = mixedMoment B node4759 node4759Labels := by
  calc
    mixedMoment B raw34094 raw34094Labels = mixedMoment B raw34094step0 raw34094step0Labels := by
      have ha : raw34094step0 = (fun i j => raw34094 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34094step0 raw34094; decide +kernel
      have hl : raw34094step0Labels = raw34094Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34094 raw34094Labels permutation152 permutation3
    mixedMoment B raw34094step0 raw34094step0Labels = mixedMoment B raw34094step1 raw34094step1Labels := by
      have ha : raw34094step1 = raw34094step0 := by apply Matrix.ext; unfold raw34094step1 raw34094step0; decide +kernel
      have hl : raw34094step0Labels = labelEmbedding6 ∘ raw34094step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34094step0 raw34094step0Labels raw34094step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4759 node4759Labels := by rfl

def raw34095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw34095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw34095step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34095step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw34095step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34095 raw34095Labels = mixedMoment B node4778 node4778Labels := by
  calc
    mixedMoment B raw34095 raw34095Labels = mixedMoment B raw34095step0 raw34095step0Labels := by
      have ha : raw34095step0 = (fun i j => raw34095 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34095step0 raw34095; decide +kernel
      have hl : raw34095step0Labels = raw34095Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34095 raw34095Labels permutation164 permutation3
    mixedMoment B raw34095step0 raw34095step0Labels = mixedMoment B raw34095step1 raw34095step1Labels := by
      have ha : raw34095step1 = raw34095step0 := by apply Matrix.ext; unfold raw34095step1 raw34095step0; decide +kernel
      have hl : raw34095step0Labels = labelEmbedding6 ∘ raw34095step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34095step0 raw34095step0Labels raw34095step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4778 node4778Labels := by rfl

def raw34096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw34096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34096step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34096step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34096step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34096step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34096step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34096 raw34096Labels = mixedMoment B node4392 node4392Labels := by
  calc
    mixedMoment B raw34096 raw34096Labels = mixedMoment B raw34096step0 raw34096step0Labels := by
      have ha : raw34096step0 = (fun i j => raw34096 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34096step0 raw34096; decide +kernel
      have hl : raw34096step0Labels = raw34096Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34096 raw34096Labels permutation160 permutation4
    mixedMoment B raw34096step0 raw34096step0Labels = mixedMoment B raw34096step1 raw34096step1Labels := by
      have ha : raw34096step1 = -raw34096step0 := by apply Matrix.ext; change ∀ i j, raw34096step1 i j = -(raw34096step0 i j); unfold raw34096step1 raw34096step0; decide +kernel
      have hl : raw34096step1Labels = raw34096step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34096step1 raw34096step1Labels = mixedMoment B raw34096step2 raw34096step2Labels := by
      have ha : raw34096step2 = raw34096step1 := by apply Matrix.ext; unfold raw34096step2 raw34096step1; decide +kernel
      have hl : raw34096step1Labels = labelEmbedding7 ∘ raw34096step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34096step1 raw34096step1Labels raw34096step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4392 node4392Labels := by rfl

def raw34097 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw34097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34097step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34097step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34097 raw34097Labels = mixedMoment B node4812 node4812Labels := by
  calc
    mixedMoment B raw34097 raw34097Labels = mixedMoment B raw34097step0 raw34097step0Labels := by
      have ha : raw34097step0 = (fun i j => raw34097 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34097step0 raw34097; decide +kernel
      have hl : raw34097step0Labels = raw34097Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34097 raw34097Labels permutation152 permutation6
    mixedMoment B raw34097step0 raw34097step0Labels = mixedMoment B raw34097step1 raw34097step1Labels := by
      have ha : raw34097step1 = raw34097step0 := by apply Matrix.ext; unfold raw34097step1 raw34097step0; decide +kernel
      have hl : raw34097step0Labels = labelEmbedding9 ∘ raw34097step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34097step0 raw34097step0Labels raw34097step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4812 node4812Labels := by rfl

def raw34098 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw34098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34098step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34098step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34098step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34098 raw34098Labels = mixedMoment B node4812 node4812Labels := by
  calc
    mixedMoment B raw34098 raw34098Labels = mixedMoment B raw34098step0 raw34098step0Labels := by
      have ha : raw34098step0 = (fun i j => raw34098 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34098step0 raw34098; decide +kernel
      have hl : raw34098step0Labels = raw34098Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34098 raw34098Labels permutation154 permutation6
    mixedMoment B raw34098step0 raw34098step0Labels = mixedMoment B raw34098step1 raw34098step1Labels := by
      have ha : raw34098step1 = raw34098step0 := by apply Matrix.ext; unfold raw34098step1 raw34098step0; decide +kernel
      have hl : raw34098step0Labels = labelEmbedding9 ∘ raw34098step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34098step0 raw34098step0Labels raw34098step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4812 node4812Labels := by rfl

def raw34099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw34099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34099step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw34099step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34099step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34099step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34099step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34099step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34099 raw34099Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw34099 raw34099Labels = mixedMoment B raw34099step0 raw34099step0Labels := by
      have ha : raw34099step0 = (fun i j => raw34099 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34099step0 raw34099; decide +kernel
      have hl : raw34099step0Labels = raw34099Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34099 raw34099Labels permutation158 permutation4
    mixedMoment B raw34099step0 raw34099step0Labels = mixedMoment B raw34099step1 raw34099step1Labels := by
      have ha : raw34099step1 = -raw34099step0 := by apply Matrix.ext; change ∀ i j, raw34099step1 i j = -(raw34099step0 i j); unfold raw34099step1 raw34099step0; decide +kernel
      have hl : raw34099step1Labels = raw34099step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34099step1 raw34099step1Labels = mixedMoment B raw34099step2 raw34099step2Labels := by
      have ha : raw34099step2 = raw34099step1 := by apply Matrix.ext; unfold raw34099step2 raw34099step1; decide +kernel
      have hl : raw34099step1Labels = labelEmbedding7 ∘ raw34099step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34099step1 raw34099step1Labels raw34099step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4396 node4396Labels := by rfl

def raw34100 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw34100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34100step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34100step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34100step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34100 raw34100Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw34100 raw34100Labels = mixedMoment B raw34100step0 raw34100step0Labels := by
      have ha : raw34100step0 = (fun i j => raw34100 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34100step0 raw34100; decide +kernel
      have hl : raw34100step0Labels = raw34100Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34100 raw34100Labels permutation152 permutation6
    mixedMoment B raw34100step0 raw34100step0Labels = mixedMoment B raw34100step1 raw34100step1Labels := by
      have ha : raw34100step1 = raw34100step0 := by apply Matrix.ext; unfold raw34100step1 raw34100step0; decide +kernel
      have hl : raw34100step0Labels = labelEmbedding9 ∘ raw34100step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34100step0 raw34100step0Labels raw34100step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

def raw34101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw34101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw34101step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34101step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34101step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34101step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw34101step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34101 raw34101Labels = mixedMoment B node4390 node4390Labels := by
  calc
    mixedMoment B raw34101 raw34101Labels = mixedMoment B raw34101step0 raw34101step0Labels := by
      have ha : raw34101step0 = (fun i j => raw34101 (permutation160 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34101step0 raw34101; decide +kernel
      have hl : raw34101step0Labels = raw34101Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34101 raw34101Labels permutation160 permutation4
    mixedMoment B raw34101step0 raw34101step0Labels = mixedMoment B raw34101step1 raw34101step1Labels := by
      have ha : raw34101step1 = -raw34101step0 := by apply Matrix.ext; change ∀ i j, raw34101step1 i j = -(raw34101step0 i j); unfold raw34101step1 raw34101step0; decide +kernel
      have hl : raw34101step1Labels = raw34101step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34101step1 raw34101step1Labels = mixedMoment B raw34101step2 raw34101step2Labels := by
      have ha : raw34101step2 = raw34101step1 := by apply Matrix.ext; unfold raw34101step2 raw34101step1; decide +kernel
      have hl : raw34101step1Labels = labelEmbedding7 ∘ raw34101step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34101step1 raw34101step1Labels raw34101step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4390 node4390Labels := by rfl

def raw34102 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw34102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw34102step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34102step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw34102step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34102 raw34102Labels = mixedMoment B node4797 node4797Labels := by
  calc
    mixedMoment B raw34102 raw34102Labels = mixedMoment B raw34102step0 raw34102step0Labels := by
      have ha : raw34102step0 = (fun i j => raw34102 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34102step0 raw34102; decide +kernel
      have hl : raw34102step0Labels = raw34102Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34102 raw34102Labels permutation152 permutation6
    mixedMoment B raw34102step0 raw34102step0Labels = mixedMoment B raw34102step1 raw34102step1Labels := by
      have ha : raw34102step1 = raw34102step0 := by apply Matrix.ext; unfold raw34102step1 raw34102step0; decide +kernel
      have hl : raw34102step0Labels = labelEmbedding9 ∘ raw34102step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34102step0 raw34102step0Labels raw34102step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4797 node4797Labels := by rfl

def raw34103 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw34103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34103step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw34103step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34103step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw34103step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34103 raw34103Labels = mixedMoment B node4797 node4797Labels := by
  calc
    mixedMoment B raw34103 raw34103Labels = mixedMoment B raw34103step0 raw34103step0Labels := by
      have ha : raw34103step0 = (fun i j => raw34103 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34103step0 raw34103; decide +kernel
      have hl : raw34103step0Labels = raw34103Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34103 raw34103Labels permutation154 permutation6
    mixedMoment B raw34103step0 raw34103step0Labels = mixedMoment B raw34103step1 raw34103step1Labels := by
      have ha : raw34103step1 = raw34103step0 := by apply Matrix.ext; unfold raw34103step1 raw34103step0; decide +kernel
      have hl : raw34103step0Labels = labelEmbedding9 ∘ raw34103step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34103step0 raw34103step0Labels raw34103step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4797 node4797Labels := by rfl

def raw34104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34104step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34104step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34104step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34104step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34104step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34104step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34104 raw34104Labels = mixedMoment B node5233 node5233Labels := by
  calc
    mixedMoment B raw34104 raw34104Labels = mixedMoment B raw34104step0 raw34104step0Labels := by
      have hz : ∀ j, raw34104 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34104step0 = (fun i j => raw34104 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34104step0 raw34104; decide +kernel
      have hl : raw34104step0Labels = raw34104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34104 raw34104Labels permutation346 hz
    mixedMoment B raw34104step0 raw34104step0Labels = mixedMoment B raw34104step1 raw34104step1Labels := by
      have ha : raw34104step1 = (fun i j => raw34104step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34104step1 raw34104step0; decide +kernel
      have hl : raw34104step1Labels = raw34104step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34104step0 raw34104step0Labels permutation37 permutation7
    mixedMoment B raw34104step1 raw34104step1Labels = mixedMoment B raw34104step2 raw34104step2Labels := by
      have ha : raw34104step2 = -raw34104step1 := by apply Matrix.ext; change ∀ i j, raw34104step2 i j = -(raw34104step1 i j); unfold raw34104step2 raw34104step1; decide +kernel
      have hl : raw34104step2Labels = raw34104step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34104step2 raw34104step2Labels = mixedMoment B raw34104step3 raw34104step3Labels := by
      have ha : raw34104step3 = raw34104step2 := by apply Matrix.ext; unfold raw34104step3 raw34104step2; decide +kernel
      have hl : raw34104step2Labels = labelEmbedding10 ∘ raw34104step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34104step2 raw34104step2Labels raw34104step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5233 node5233Labels := by rfl

def raw34105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34105step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34105step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34105step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34105step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34105step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34105step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34105 raw34105Labels = mixedMoment B node5244 node5244Labels := by
  calc
    mixedMoment B raw34105 raw34105Labels = mixedMoment B raw34105step0 raw34105step0Labels := by
      have ha : raw34105step0 = (fun i j => raw34105 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34105step0 raw34105; decide +kernel
      have hl : raw34105step0Labels = raw34105Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34105 raw34105Labels permutation157 permutation7
    mixedMoment B raw34105step0 raw34105step0Labels = mixedMoment B raw34105step1 raw34105step1Labels := by
      have ha : raw34105step1 = -raw34105step0 := by apply Matrix.ext; change ∀ i j, raw34105step1 i j = -(raw34105step0 i j); unfold raw34105step1 raw34105step0; decide +kernel
      have hl : raw34105step1Labels = raw34105step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34105step1 raw34105step1Labels = mixedMoment B raw34105step2 raw34105step2Labels := by
      have ha : raw34105step2 = raw34105step1 := by apply Matrix.ext; unfold raw34105step2 raw34105step1; decide +kernel
      have hl : raw34105step1Labels = labelEmbedding10 ∘ raw34105step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34105step1 raw34105step1Labels raw34105step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5244 node5244Labels := by rfl

def raw34106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34106step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw34106step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34106step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34106step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34106step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34106step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34106 raw34106Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw34106 raw34106Labels = mixedMoment B raw34106step0 raw34106step0Labels := by
      have hz : ∀ j, raw34106 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34106step0 = (fun i j => raw34106 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34106step0 raw34106; decide +kernel
      have hl : raw34106step0Labels = raw34106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34106 raw34106Labels permutation346 hz
    mixedMoment B raw34106step0 raw34106step0Labels = mixedMoment B raw34106step1 raw34106step1Labels := by
      have ha : raw34106step1 = (fun i j => raw34106step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34106step1 raw34106step0; decide +kernel
      have hl : raw34106step1Labels = raw34106step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34106step0 raw34106step0Labels permutation37 permutation7
    mixedMoment B raw34106step1 raw34106step1Labels = mixedMoment B raw34106step2 raw34106step2Labels := by
      have ha : raw34106step2 = -raw34106step1 := by apply Matrix.ext; change ∀ i j, raw34106step2 i j = -(raw34106step1 i j); unfold raw34106step2 raw34106step1; decide +kernel
      have hl : raw34106step2Labels = raw34106step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34106step2 raw34106step2Labels = mixedMoment B raw34106step3 raw34106step3Labels := by
      have ha : raw34106step3 = raw34106step2 := by apply Matrix.ext; unfold raw34106step3 raw34106step2; decide +kernel
      have hl : raw34106step2Labels = labelEmbedding10 ∘ raw34106step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34106step2 raw34106step2Labels raw34106step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw34107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34107step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw34107step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34107step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34107step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34107step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34107step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34107 raw34107Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw34107 raw34107Labels = mixedMoment B raw34107step0 raw34107step0Labels := by
      have hz : ∀ j, raw34107 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34107step0 = (fun i j => raw34107 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34107step0 raw34107; decide +kernel
      have hl : raw34107step0Labels = raw34107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34107 raw34107Labels permutation346 hz
    mixedMoment B raw34107step0 raw34107step0Labels = mixedMoment B raw34107step1 raw34107step1Labels := by
      have ha : raw34107step1 = (fun i j => raw34107step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34107step1 raw34107step0; decide +kernel
      have hl : raw34107step1Labels = raw34107step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34107step0 raw34107step0Labels permutation37 permutation7
    mixedMoment B raw34107step1 raw34107step1Labels = mixedMoment B raw34107step2 raw34107step2Labels := by
      have ha : raw34107step2 = -raw34107step1 := by apply Matrix.ext; change ∀ i j, raw34107step2 i j = -(raw34107step1 i j); unfold raw34107step2 raw34107step1; decide +kernel
      have hl : raw34107step2Labels = raw34107step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34107step2 raw34107step2Labels = mixedMoment B raw34107step3 raw34107step3Labels := by
      have ha : raw34107step3 = raw34107step2 := by apply Matrix.ext; unfold raw34107step3 raw34107step2; decide +kernel
      have hl : raw34107step2Labels = labelEmbedding10 ∘ raw34107step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34107step2 raw34107step2Labels raw34107step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw34108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34108step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34108step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34108step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34108step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34108step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34108 raw34108Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw34108 raw34108Labels = mixedMoment B raw34108step0 raw34108step0Labels := by
      have hz : ∀ j, raw34108 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34108step0 = (fun i j => raw34108 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34108step0 raw34108; decide +kernel
      have hl : raw34108step0Labels = raw34108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34108 raw34108Labels permutation346 hz
    mixedMoment B raw34108step0 raw34108step0Labels = mixedMoment B raw34108step1 raw34108step1Labels := by
      have ha : raw34108step1 = (fun i j => raw34108step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34108step1 raw34108step0; decide +kernel
      have hl : raw34108step1Labels = raw34108step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34108step0 raw34108step0Labels permutation37 permutation7
    mixedMoment B raw34108step1 raw34108step1Labels = mixedMoment B raw34108step2 raw34108step2Labels := by
      have ha : raw34108step2 = -raw34108step1 := by apply Matrix.ext; change ∀ i j, raw34108step2 i j = -(raw34108step1 i j); unfold raw34108step2 raw34108step1; decide +kernel
      have hl : raw34108step2Labels = raw34108step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34108step2 raw34108step2Labels = mixedMoment B raw34108step3 raw34108step3Labels := by
      have ha : raw34108step3 = raw34108step2 := by apply Matrix.ext; unfold raw34108step3 raw34108step2; decide +kernel
      have hl : raw34108step2Labels = labelEmbedding10 ∘ raw34108step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34108step2 raw34108step2Labels raw34108step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw34109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34109step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34109step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34109step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34109step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34109 raw34109Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw34109 raw34109Labels = mixedMoment B raw34109step0 raw34109step0Labels := by
      have hz : ∀ j, raw34109 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34109step0 = (fun i j => raw34109 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34109step0 raw34109; decide +kernel
      have hl : raw34109step0Labels = raw34109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34109 raw34109Labels permutation346 hz
    mixedMoment B raw34109step0 raw34109step0Labels = mixedMoment B raw34109step1 raw34109step1Labels := by
      have hz : ∀ j, raw34109step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw34109step1 = (fun i j => raw34109step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw34109step1 raw34109step0; decide +kernel
      have hl : raw34109step1Labels = raw34109step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34109step0 raw34109step0Labels permutation56 hz
    mixedMoment B raw34109step1 raw34109step1Labels = mixedMoment B raw34109step2 raw34109step2Labels := by
      have ha : raw34109step2 = (fun i j => raw34109step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34109step2 raw34109step1; decide +kernel
      have hl : raw34109step2Labels = raw34109step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34109step1 raw34109step1Labels permutation10 permutation2
    _ = mixedMoment B node4503 node4503Labels := by rfl

def raw34110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34110step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34110step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34110 raw34110Labels = mixedMoment B node4680 node4680Labels := by
  calc
    mixedMoment B raw34110 raw34110Labels = mixedMoment B raw34110step0 raw34110step0Labels := by
      have ha : raw34110step0 = (fun i j => raw34110 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34110step0 raw34110; decide +kernel
      have hl : raw34110step0Labels = raw34110Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34110 raw34110Labels permutation154 permutation2
    _ = mixedMoment B node4680 node4680Labels := by rfl

def raw34111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34111Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34111step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34111step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34111 raw34111Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw34111 raw34111Labels = mixedMoment B raw34111step0 raw34111step0Labels := by
      have ha : raw34111step0 = (fun i j => raw34111 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34111step0 raw34111; decide +kernel
      have hl : raw34111step0Labels = raw34111Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34111 raw34111Labels permutation158 permutation2
    _ = mixedMoment B node4816 node4816Labels := by rfl

def raw34112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34112step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34112 raw34112Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw34112 raw34112Labels = mixedMoment B raw34112step0 raw34112step0Labels := by
      have ha : raw34112step0 = (fun i j => raw34112 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34112step0 raw34112; decide +kernel
      have hl : raw34112step0Labels = raw34112Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34112 raw34112Labels permutation164 permutation2
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw34113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34113step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34113 raw34113Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw34113 raw34113Labels = mixedMoment B raw34113step0 raw34113step0Labels := by
      have ha : raw34113step0 = (fun i j => raw34113 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34113step0 raw34113; decide +kernel
      have hl : raw34113step0Labels = raw34113Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34113 raw34113Labels permutation157 permutation2
    _ = mixedMoment B node4831 node4831Labels := by rfl

def raw34114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34114Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34114step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34114step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34114 raw34114Labels = mixedMoment B node4688 node4688Labels := by
  calc
    mixedMoment B raw34114 raw34114Labels = mixedMoment B raw34114step0 raw34114step0Labels := by
      have hz : ∀ j, raw34114 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34114step0 = (fun i j => raw34114 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34114step0 raw34114; decide +kernel
      have hl : raw34114step0Labels = raw34114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34114 raw34114Labels permutation346 hz
    mixedMoment B raw34114step0 raw34114step0Labels = mixedMoment B raw34114step1 raw34114step1Labels := by
      have ha : raw34114step1 = (fun i j => raw34114step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34114step1 raw34114step0; decide +kernel
      have hl : raw34114step1Labels = raw34114step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34114step0 raw34114step0Labels permutation35 permutation2
    _ = mixedMoment B node4688 node4688Labels := by rfl

def raw34115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34115step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34115 raw34115Labels = mixedMoment B node4766 node4766Labels := by
  calc
    mixedMoment B raw34115 raw34115Labels = mixedMoment B raw34115step0 raw34115step0Labels := by
      have ha : raw34115step0 = (fun i j => raw34115 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34115step0 raw34115; decide +kernel
      have hl : raw34115step0Labels = raw34115Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34115 raw34115Labels permutation155 permutation2
    _ = mixedMoment B node4766 node4766Labels := by rfl

def raw34116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34116step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34116step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34116 raw34116Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw34116 raw34116Labels = mixedMoment B raw34116step0 raw34116step0Labels := by
      have hz : ∀ j, raw34116 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34116step0 = (fun i j => raw34116 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34116step0 raw34116; decide +kernel
      have hl : raw34116step0Labels = raw34116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34116 raw34116Labels permutation346 hz
    mixedMoment B raw34116step0 raw34116step0Labels = mixedMoment B raw34116step1 raw34116step1Labels := by
      have ha : raw34116step1 = (fun i j => raw34116step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34116step1 raw34116step0; decide +kernel
      have hl : raw34116step1Labels = raw34116step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34116step0 raw34116step0Labels permutation35 permutation2
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw34117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34117Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34117step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34117step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34117 raw34117Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw34117 raw34117Labels = mixedMoment B raw34117step0 raw34117step0Labels := by
      have hz : ∀ j, raw34117 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34117step0 = (fun i j => raw34117 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34117step0 raw34117; decide +kernel
      have hl : raw34117step0Labels = raw34117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34117 raw34117Labels permutation346 hz
    mixedMoment B raw34117step0 raw34117step0Labels = mixedMoment B raw34117step1 raw34117step1Labels := by
      have ha : raw34117step1 = (fun i j => raw34117step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34117step1 raw34117step0; decide +kernel
      have hl : raw34117step1Labels = raw34117step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34117step0 raw34117step0Labels permutation37 permutation2
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw34118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34118step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34118step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34118 raw34118Labels = mixedMoment B node4690 node4690Labels := by
  calc
    mixedMoment B raw34118 raw34118Labels = mixedMoment B raw34118step0 raw34118step0Labels := by
      have hz : ∀ j, raw34118 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34118step0 = (fun i j => raw34118 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34118step0 raw34118; decide +kernel
      have hl : raw34118step0Labels = raw34118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34118 raw34118Labels permutation346 hz
    mixedMoment B raw34118step0 raw34118step0Labels = mixedMoment B raw34118step1 raw34118step1Labels := by
      have ha : raw34118step1 = (fun i j => raw34118step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34118step1 raw34118step0; decide +kernel
      have hl : raw34118step1Labels = raw34118step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34118step0 raw34118step0Labels permutation33 permutation2
    _ = mixedMoment B node4690 node4690Labels := by rfl

def raw34119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34119step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34119step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34119 raw34119Labels = mixedMoment B node4768 node4768Labels := by
  calc
    mixedMoment B raw34119 raw34119Labels = mixedMoment B raw34119step0 raw34119step0Labels := by
      have ha : raw34119step0 = (fun i j => raw34119 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34119step0 raw34119; decide +kernel
      have hl : raw34119step0Labels = raw34119Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34119 raw34119Labels permutation153 permutation2
    _ = mixedMoment B node4768 node4768Labels := by rfl

def raw34120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34120step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34120step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34120 raw34120Labels = mixedMoment B node4821 node4821Labels := by
  calc
    mixedMoment B raw34120 raw34120Labels = mixedMoment B raw34120step0 raw34120step0Labels := by
      have hz : ∀ j, raw34120 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34120step0 = (fun i j => raw34120 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34120step0 raw34120; decide +kernel
      have hl : raw34120step0Labels = raw34120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34120 raw34120Labels permutation346 hz
    mixedMoment B raw34120step0 raw34120step0Labels = mixedMoment B raw34120step1 raw34120step1Labels := by
      have ha : raw34120step1 = (fun i j => raw34120step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34120step1 raw34120step0; decide +kernel
      have hl : raw34120step1Labels = raw34120step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34120step0 raw34120step0Labels permutation33 permutation2
    _ = mixedMoment B node4821 node4821Labels := by rfl

def raw34121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw34121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw34121step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw34121step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34121 raw34121Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw34121 raw34121Labels = mixedMoment B raw34121step0 raw34121step0Labels := by
      have hz : ∀ j, raw34121 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34121step0 = (fun i j => raw34121 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34121step0 raw34121; decide +kernel
      have hl : raw34121step0Labels = raw34121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34121 raw34121Labels permutation346 hz
    mixedMoment B raw34121step0 raw34121step0Labels = mixedMoment B raw34121step1 raw34121step1Labels := by
      have ha : raw34121step1 = (fun i j => raw34121step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34121step1 raw34121step0; decide +kernel
      have hl : raw34121step1Labels = raw34121step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34121step0 raw34121step0Labels permutation36 permutation2
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw34122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw34122step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34122 raw34122Labels = mixedMoment B node4687 node4687Labels := by
  calc
    mixedMoment B raw34122 raw34122Labels = mixedMoment B raw34122step0 raw34122step0Labels := by
      have hz : ∀ j, raw34122 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34122step0 = (fun i j => raw34122 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34122step0 raw34122; decide +kernel
      have hl : raw34122step0Labels = raw34122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34122 raw34122Labels permutation346 hz
    mixedMoment B raw34122step0 raw34122step0Labels = mixedMoment B raw34122step1 raw34122step1Labels := by
      have ha : raw34122step1 = (fun i j => raw34122step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34122step1 raw34122step0; decide +kernel
      have hl : raw34122step1Labels = raw34122step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34122step0 raw34122step0Labels permutation34 permutation2
    _ = mixedMoment B node4687 node4687Labels := by rfl

def raw34123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw34123step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34123 raw34123Labels = mixedMoment B node4765 node4765Labels := by
  calc
    mixedMoment B raw34123 raw34123Labels = mixedMoment B raw34123step0 raw34123step0Labels := by
      have ha : raw34123step0 = (fun i j => raw34123 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34123step0 raw34123; decide +kernel
      have hl : raw34123step0Labels = raw34123Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34123 raw34123Labels permutation154 permutation2
    _ = mixedMoment B node4765 node4765Labels := by rfl

def raw34124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34124step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34124 raw34124Labels = mixedMoment B node4819 node4819Labels := by
  calc
    mixedMoment B raw34124 raw34124Labels = mixedMoment B raw34124step0 raw34124step0Labels := by
      have hz : ∀ j, raw34124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34124step0 = (fun i j => raw34124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34124step0 raw34124; decide +kernel
      have hl : raw34124step0Labels = raw34124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34124 raw34124Labels permutation346 hz
    _ = mixedMoment B node4819 node4819Labels := by rfl

def raw34125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw34125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw34125step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw34125step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34125 raw34125Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw34125 raw34125Labels = mixedMoment B raw34125step0 raw34125step0Labels := by
      have hz : ∀ j, raw34125 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34125step0 = (fun i j => raw34125 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34125step0 raw34125; decide +kernel
      have hl : raw34125step0Labels = raw34125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34125 raw34125Labels permutation346 hz
    mixedMoment B raw34125step0 raw34125step0Labels = mixedMoment B raw34125step1 raw34125step1Labels := by
      have ha : raw34125step1 = (fun i j => raw34125step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34125step1 raw34125step0; decide +kernel
      have hl : raw34125step1Labels = raw34125step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34125step0 raw34125step0Labels permutation34 permutation2
    _ = mixedMoment B node4808 node4808Labels := by rfl

def raw34126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34126Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34126step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34126step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34126step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34126step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34126step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34126 raw34126Labels = mixedMoment B node2678 node2678Labels := by
  calc
    mixedMoment B raw34126 raw34126Labels = mixedMoment B raw34126step0 raw34126step0Labels := by
      have hz : ∀ j, raw34126 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34126step0 = (fun i j => raw34126 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34126step0 raw34126; decide +kernel
      have hl : raw34126step0Labels = raw34126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34126 raw34126Labels permutation346 hz
    mixedMoment B raw34126step0 raw34126step0Labels = mixedMoment B raw34126step1 raw34126step1Labels := by
      have ha : raw34126step1 = (fun i j => raw34126step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34126step1 raw34126step0; decide +kernel
      have hl : raw34126step1Labels = raw34126step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34126step0 raw34126step0Labels permutation37 permutation7
    mixedMoment B raw34126step1 raw34126step1Labels = mixedMoment B raw34126step2 raw34126step2Labels := by
      have ha : raw34126step2 = -raw34126step1 := by apply Matrix.ext; change ∀ i j, raw34126step2 i j = -(raw34126step1 i j); unfold raw34126step2 raw34126step1; decide +kernel
      have hl : raw34126step2Labels = raw34126step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34126step2 raw34126step2Labels = mixedMoment B raw34126step3 raw34126step3Labels := by
      have ha : raw34126step3 = raw34126step2 := by apply Matrix.ext; unfold raw34126step3 raw34126step2; decide +kernel
      have hl : raw34126step2Labels = labelEmbedding1 ∘ raw34126step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34126step2 raw34126step2Labels raw34126step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2678 node2678Labels := by rfl

def raw34127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34127Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34127step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34127step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34127step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34127step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34127step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34127step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34127 raw34127Labels = mixedMoment B node2698 node2698Labels := by
  calc
    mixedMoment B raw34127 raw34127Labels = mixedMoment B raw34127step0 raw34127step0Labels := by
      have ha : raw34127step0 = (fun i j => raw34127 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34127step0 raw34127; decide +kernel
      have hl : raw34127step0Labels = raw34127Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34127 raw34127Labels permutation157 permutation7
    mixedMoment B raw34127step0 raw34127step0Labels = mixedMoment B raw34127step1 raw34127step1Labels := by
      have ha : raw34127step1 = -raw34127step0 := by apply Matrix.ext; change ∀ i j, raw34127step1 i j = -(raw34127step0 i j); unfold raw34127step1 raw34127step0; decide +kernel
      have hl : raw34127step1Labels = raw34127step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34127step1 raw34127step1Labels = mixedMoment B raw34127step2 raw34127step2Labels := by
      have ha : raw34127step2 = raw34127step1 := by apply Matrix.ext; unfold raw34127step2 raw34127step1; decide +kernel
      have hl : raw34127step1Labels = labelEmbedding1 ∘ raw34127step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34127step1 raw34127step1Labels raw34127step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2698 node2698Labels := by rfl

def raw34128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34128Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34128step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw34128step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34128step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34128step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34128step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34128 raw34128Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw34128 raw34128Labels = mixedMoment B raw34128step0 raw34128step0Labels := by
      have hz : ∀ j, raw34128 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34128step0 = (fun i j => raw34128 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34128step0 raw34128; decide +kernel
      have hl : raw34128step0Labels = raw34128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34128 raw34128Labels permutation346 hz
    mixedMoment B raw34128step0 raw34128step0Labels = mixedMoment B raw34128step1 raw34128step1Labels := by
      have ha : raw34128step1 = (fun i j => raw34128step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34128step1 raw34128step0; decide +kernel
      have hl : raw34128step1Labels = raw34128step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34128step0 raw34128step0Labels permutation37 permutation7
    mixedMoment B raw34128step1 raw34128step1Labels = mixedMoment B raw34128step2 raw34128step2Labels := by
      have ha : raw34128step2 = -raw34128step1 := by apply Matrix.ext; change ∀ i j, raw34128step2 i j = -(raw34128step1 i j); unfold raw34128step2 raw34128step1; decide +kernel
      have hl : raw34128step2Labels = raw34128step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34128step2 raw34128step2Labels = mixedMoment B raw34128step3 raw34128step3Labels := by
      have ha : raw34128step3 = raw34128step2 := by apply Matrix.ext; unfold raw34128step3 raw34128step2; decide +kernel
      have hl : raw34128step2Labels = labelEmbedding1 ∘ raw34128step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34128step2 raw34128step2Labels raw34128step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw34129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34129Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34129step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw34129step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34129step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34129step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34129step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34129step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34129 raw34129Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw34129 raw34129Labels = mixedMoment B raw34129step0 raw34129step0Labels := by
      have hz : ∀ j, raw34129 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34129step0 = (fun i j => raw34129 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34129step0 raw34129; decide +kernel
      have hl : raw34129step0Labels = raw34129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34129 raw34129Labels permutation346 hz
    mixedMoment B raw34129step0 raw34129step0Labels = mixedMoment B raw34129step1 raw34129step1Labels := by
      have ha : raw34129step1 = (fun i j => raw34129step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34129step1 raw34129step0; decide +kernel
      have hl : raw34129step1Labels = raw34129step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34129step0 raw34129step0Labels permutation37 permutation7
    mixedMoment B raw34129step1 raw34129step1Labels = mixedMoment B raw34129step2 raw34129step2Labels := by
      have ha : raw34129step2 = -raw34129step1 := by apply Matrix.ext; change ∀ i j, raw34129step2 i j = -(raw34129step1 i j); unfold raw34129step2 raw34129step1; decide +kernel
      have hl : raw34129step2Labels = raw34129step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34129step2 raw34129step2Labels = mixedMoment B raw34129step3 raw34129step3Labels := by
      have ha : raw34129step3 = raw34129step2 := by apply Matrix.ext; unfold raw34129step3 raw34129step2; decide +kernel
      have hl : raw34129step2Labels = labelEmbedding1 ∘ raw34129step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34129step2 raw34129step2Labels raw34129step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2731 node2731Labels := by rfl

def raw34130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34130Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34130step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34130step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34130step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34130step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34130step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34130 raw34130Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw34130 raw34130Labels = mixedMoment B raw34130step0 raw34130step0Labels := by
      have hz : ∀ j, raw34130 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34130step0 = (fun i j => raw34130 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34130step0 raw34130; decide +kernel
      have hl : raw34130step0Labels = raw34130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34130 raw34130Labels permutation346 hz
    mixedMoment B raw34130step0 raw34130step0Labels = mixedMoment B raw34130step1 raw34130step1Labels := by
      have ha : raw34130step1 = (fun i j => raw34130step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34130step1 raw34130step0; decide +kernel
      have hl : raw34130step1Labels = raw34130step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34130step0 raw34130step0Labels permutation37 permutation7
    mixedMoment B raw34130step1 raw34130step1Labels = mixedMoment B raw34130step2 raw34130step2Labels := by
      have ha : raw34130step2 = -raw34130step1 := by apply Matrix.ext; change ∀ i j, raw34130step2 i j = -(raw34130step1 i j); unfold raw34130step2 raw34130step1; decide +kernel
      have hl : raw34130step2Labels = raw34130step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34130step2 raw34130step2Labels = mixedMoment B raw34130step3 raw34130step3Labels := by
      have ha : raw34130step3 = raw34130step2 := by apply Matrix.ext; unfold raw34130step3 raw34130step2; decide +kernel
      have hl : raw34130step2Labels = labelEmbedding1 ∘ raw34130step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34130step2 raw34130step2Labels raw34130step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw34131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34131Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34131step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34131step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34131step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34131step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34131step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34131step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34131step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34131step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34131step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34131 raw34131Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw34131 raw34131Labels = mixedMoment B raw34131step0 raw34131step0Labels := by
      have hz : ∀ j, raw34131 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34131step0 = (fun i j => raw34131 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34131step0 raw34131; decide +kernel
      have hl : raw34131step0Labels = raw34131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34131 raw34131Labels permutation346 hz
    mixedMoment B raw34131step0 raw34131step0Labels = mixedMoment B raw34131step1 raw34131step1Labels := by
      have hz : ∀ j, raw34131step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw34131step1 = (fun i j => raw34131step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw34131step1 raw34131step0; decide +kernel
      have hl : raw34131step1Labels = raw34131step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34131step0 raw34131step0Labels permutation56 hz
    mixedMoment B raw34131step1 raw34131step1Labels = mixedMoment B raw34131step2 raw34131step2Labels := by
      have ha : raw34131step2 = (fun i j => raw34131step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34131step2 raw34131step1; decide +kernel
      have hl : raw34131step2Labels = raw34131step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34131step1 raw34131step1Labels permutation13 permutation7
    mixedMoment B raw34131step2 raw34131step2Labels = mixedMoment B raw34131step3 raw34131step3Labels := by
      have ha : raw34131step3 = -raw34131step2 := by apply Matrix.ext; change ∀ i j, raw34131step3 i j = -(raw34131step2 i j); unfold raw34131step3 raw34131step2; decide +kernel
      have hl : raw34131step3Labels = raw34131step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34131step3 raw34131step3Labels = mixedMoment B raw34131step4 raw34131step4Labels := by
      have ha : raw34131step4 = raw34131step3 := by apply Matrix.ext; unfold raw34131step4 raw34131step3; decide +kernel
      have hl : raw34131step3Labels = labelEmbedding1 ∘ raw34131step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34131step3 raw34131step3Labels raw34131step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1739 node1739Labels := by rfl

def raw34132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34132Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw34132step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34132step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34132step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34132step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw34132step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34132 raw34132Labels = mixedMoment B node2145 node2145Labels := by
  calc
    mixedMoment B raw34132 raw34132Labels = mixedMoment B raw34132step0 raw34132step0Labels := by
      have ha : raw34132step0 = (fun i j => raw34132 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34132step0 raw34132; decide +kernel
      have hl : raw34132step0Labels = raw34132Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34132 raw34132Labels permutation157 permutation7
    mixedMoment B raw34132step0 raw34132step0Labels = mixedMoment B raw34132step1 raw34132step1Labels := by
      have ha : raw34132step1 = -raw34132step0 := by apply Matrix.ext; change ∀ i j, raw34132step1 i j = -(raw34132step0 i j); unfold raw34132step1 raw34132step0; decide +kernel
      have hl : raw34132step1Labels = raw34132step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34132step1 raw34132step1Labels = mixedMoment B raw34132step2 raw34132step2Labels := by
      have ha : raw34132step2 = raw34132step1 := by apply Matrix.ext; unfold raw34132step2 raw34132step1; decide +kernel
      have hl : raw34132step1Labels = labelEmbedding1 ∘ raw34132step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34132step1 raw34132step1Labels raw34132step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2145 node2145Labels := by rfl

def raw34133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34133Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw34133step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34133step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34133step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34133step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34133step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34133 raw34133Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw34133 raw34133Labels = mixedMoment B raw34133step0 raw34133step0Labels := by
      have ha : raw34133step0 = (fun i j => raw34133 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34133step0 raw34133; decide +kernel
      have hl : raw34133step0Labels = raw34133Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34133 raw34133Labels permutation157 permutation7
    mixedMoment B raw34133step0 raw34133step0Labels = mixedMoment B raw34133step1 raw34133step1Labels := by
      have ha : raw34133step1 = -raw34133step0 := by apply Matrix.ext; change ∀ i j, raw34133step1 i j = -(raw34133step0 i j); unfold raw34133step1 raw34133step0; decide +kernel
      have hl : raw34133step1Labels = raw34133step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34133step1 raw34133step1Labels = mixedMoment B raw34133step2 raw34133step2Labels := by
      have ha : raw34133step2 = raw34133step1 := by apply Matrix.ext; unfold raw34133step2 raw34133step1; decide +kernel
      have hl : raw34133step1Labels = labelEmbedding1 ∘ raw34133step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34133step1 raw34133step1Labels raw34133step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2196 node2196Labels := by rfl

def raw34134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34134Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw34134step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34134step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34134step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34134step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw34134step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34134 raw34134Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw34134 raw34134Labels = mixedMoment B raw34134step0 raw34134step0Labels := by
      have ha : raw34134step0 = (fun i j => raw34134 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34134step0 raw34134; decide +kernel
      have hl : raw34134step0Labels = raw34134Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34134 raw34134Labels permutation157 permutation7
    mixedMoment B raw34134step0 raw34134step0Labels = mixedMoment B raw34134step1 raw34134step1Labels := by
      have ha : raw34134step1 = -raw34134step0 := by apply Matrix.ext; change ∀ i j, raw34134step1 i j = -(raw34134step0 i j); unfold raw34134step1 raw34134step0; decide +kernel
      have hl : raw34134step1Labels = raw34134step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34134step1 raw34134step1Labels = mixedMoment B raw34134step2 raw34134step2Labels := by
      have ha : raw34134step2 = raw34134step1 := by apply Matrix.ext; unfold raw34134step2 raw34134step1; decide +kernel
      have hl : raw34134step1Labels = labelEmbedding1 ∘ raw34134step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34134step1 raw34134step1Labels raw34134step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw34135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34135Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34135step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34135step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34135step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34135step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34135step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34135step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34135 raw34135Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw34135 raw34135Labels = mixedMoment B raw34135step0 raw34135step0Labels := by
      have ha : raw34135step0 = (fun i j => raw34135 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34135step0 raw34135; decide +kernel
      have hl : raw34135step0Labels = raw34135Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34135 raw34135Labels permutation157 permutation7
    mixedMoment B raw34135step0 raw34135step0Labels = mixedMoment B raw34135step1 raw34135step1Labels := by
      have ha : raw34135step1 = -raw34135step0 := by apply Matrix.ext; change ∀ i j, raw34135step1 i j = -(raw34135step0 i j); unfold raw34135step1 raw34135step0; decide +kernel
      have hl : raw34135step1Labels = raw34135step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34135step1 raw34135step1Labels = mixedMoment B raw34135step2 raw34135step2Labels := by
      have ha : raw34135step2 = raw34135step1 := by apply Matrix.ext; unfold raw34135step2 raw34135step1; decide +kernel
      have hl : raw34135step1Labels = labelEmbedding1 ∘ raw34135step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34135step1 raw34135step1Labels raw34135step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2191 node2191Labels := by rfl

def raw34136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34136Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34136step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34136step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw34136step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34136step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw34136step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34136step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw34136step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34136 raw34136Labels = mixedMoment B node2157 node2157Labels := by
  calc
    mixedMoment B raw34136 raw34136Labels = mixedMoment B raw34136step0 raw34136step0Labels := by
      have hz : ∀ j, raw34136 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34136step0 = (fun i j => raw34136 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34136step0 raw34136; decide +kernel
      have hl : raw34136step0Labels = raw34136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34136 raw34136Labels permutation346 hz
    mixedMoment B raw34136step0 raw34136step0Labels = mixedMoment B raw34136step1 raw34136step1Labels := by
      have ha : raw34136step1 = (fun i j => raw34136step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34136step1 raw34136step0; decide +kernel
      have hl : raw34136step1Labels = raw34136step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34136step0 raw34136step0Labels permutation37 permutation7
    mixedMoment B raw34136step1 raw34136step1Labels = mixedMoment B raw34136step2 raw34136step2Labels := by
      have ha : raw34136step2 = -raw34136step1 := by apply Matrix.ext; change ∀ i j, raw34136step2 i j = -(raw34136step1 i j); unfold raw34136step2 raw34136step1; decide +kernel
      have hl : raw34136step2Labels = raw34136step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34136step2 raw34136step2Labels = mixedMoment B raw34136step3 raw34136step3Labels := by
      have ha : raw34136step3 = raw34136step2 := by apply Matrix.ext; unfold raw34136step3 raw34136step2; decide +kernel
      have hl : raw34136step2Labels = labelEmbedding1 ∘ raw34136step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34136step2 raw34136step2Labels raw34136step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2157 node2157Labels := by rfl

def raw34137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34137Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw34137step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34137step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw34137step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34137step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw34137step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34137 raw34137Labels = mixedMoment B node2177 node2177Labels := by
  calc
    mixedMoment B raw34137 raw34137Labels = mixedMoment B raw34137step0 raw34137step0Labels := by
      have ha : raw34137step0 = (fun i j => raw34137 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34137step0 raw34137; decide +kernel
      have hl : raw34137step0Labels = raw34137Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34137 raw34137Labels permutation157 permutation7
    mixedMoment B raw34137step0 raw34137step0Labels = mixedMoment B raw34137step1 raw34137step1Labels := by
      have ha : raw34137step1 = -raw34137step0 := by apply Matrix.ext; change ∀ i j, raw34137step1 i j = -(raw34137step0 i j); unfold raw34137step1 raw34137step0; decide +kernel
      have hl : raw34137step1Labels = raw34137step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34137step1 raw34137step1Labels = mixedMoment B raw34137step2 raw34137step2Labels := by
      have ha : raw34137step2 = raw34137step1 := by apply Matrix.ext; unfold raw34137step2 raw34137step1; decide +kernel
      have hl : raw34137step1Labels = labelEmbedding1 ∘ raw34137step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34137step1 raw34137step1Labels raw34137step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2177 node2177Labels := by rfl

def raw34138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34138Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![0, 1, -1], ![2, -2, 0]]
def raw34138step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34138step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34138step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34138step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34138step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34138step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34138 raw34138Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw34138 raw34138Labels = mixedMoment B raw34138step0 raw34138step0Labels := by
      have hz : ∀ j, raw34138 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34138step0 = (fun i j => raw34138 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34138step0 raw34138; decide +kernel
      have hl : raw34138step0Labels = raw34138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34138 raw34138Labels permutation346 hz
    mixedMoment B raw34138step0 raw34138step0Labels = mixedMoment B raw34138step1 raw34138step1Labels := by
      have ha : raw34138step1 = (fun i j => raw34138step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34138step1 raw34138step0; decide +kernel
      have hl : raw34138step1Labels = raw34138step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34138step0 raw34138step0Labels permutation37 permutation7
    mixedMoment B raw34138step1 raw34138step1Labels = mixedMoment B raw34138step2 raw34138step2Labels := by
      have ha : raw34138step2 = -raw34138step1 := by apply Matrix.ext; change ∀ i j, raw34138step2 i j = -(raw34138step1 i j); unfold raw34138step2 raw34138step1; decide +kernel
      have hl : raw34138step2Labels = raw34138step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34138step2 raw34138step2Labels = mixedMoment B raw34138step3 raw34138step3Labels := by
      have ha : raw34138step3 = raw34138step2 := by apply Matrix.ext; unfold raw34138step3 raw34138step2; decide +kernel
      have hl : raw34138step2Labels = labelEmbedding1 ∘ raw34138step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34138step2 raw34138step2Labels raw34138step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2215 node2215Labels := by rfl

def raw34139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34139Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw34139step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34139step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34139step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34139step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34139step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34139step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34139 raw34139Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw34139 raw34139Labels = mixedMoment B raw34139step0 raw34139step0Labels := by
      have hz : ∀ j, raw34139 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34139step0 = (fun i j => raw34139 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34139step0 raw34139; decide +kernel
      have hl : raw34139step0Labels = raw34139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34139 raw34139Labels permutation346 hz
    mixedMoment B raw34139step0 raw34139step0Labels = mixedMoment B raw34139step1 raw34139step1Labels := by
      have ha : raw34139step1 = (fun i j => raw34139step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34139step1 raw34139step0; decide +kernel
      have hl : raw34139step1Labels = raw34139step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34139step0 raw34139step0Labels permutation37 permutation7
    mixedMoment B raw34139step1 raw34139step1Labels = mixedMoment B raw34139step2 raw34139step2Labels := by
      have ha : raw34139step2 = -raw34139step1 := by apply Matrix.ext; change ∀ i j, raw34139step2 i j = -(raw34139step1 i j); unfold raw34139step2 raw34139step1; decide +kernel
      have hl : raw34139step2Labels = raw34139step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34139step2 raw34139step2Labels = mixedMoment B raw34139step3 raw34139step3Labels := by
      have ha : raw34139step3 = raw34139step2 := by apply Matrix.ext; unfold raw34139step3 raw34139step2; decide +kernel
      have hl : raw34139step2Labels = labelEmbedding1 ∘ raw34139step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34139step2 raw34139step2Labels raw34139step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

def raw34140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34140Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34140step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw34140step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34140step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34140step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34140step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34140 raw34140Labels = mixedMoment B node2158 node2158Labels := by
  calc
    mixedMoment B raw34140 raw34140Labels = mixedMoment B raw34140step0 raw34140step0Labels := by
      have hz : ∀ j, raw34140 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34140step0 = (fun i j => raw34140 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34140step0 raw34140; decide +kernel
      have hl : raw34140step0Labels = raw34140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34140 raw34140Labels permutation346 hz
    mixedMoment B raw34140step0 raw34140step0Labels = mixedMoment B raw34140step1 raw34140step1Labels := by
      have ha : raw34140step1 = (fun i j => raw34140step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34140step1 raw34140step0; decide +kernel
      have hl : raw34140step1Labels = raw34140step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34140step0 raw34140step0Labels permutation37 permutation7
    mixedMoment B raw34140step1 raw34140step1Labels = mixedMoment B raw34140step2 raw34140step2Labels := by
      have ha : raw34140step2 = -raw34140step1 := by apply Matrix.ext; change ∀ i j, raw34140step2 i j = -(raw34140step1 i j); unfold raw34140step2 raw34140step1; decide +kernel
      have hl : raw34140step2Labels = raw34140step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34140step2 raw34140step2Labels = mixedMoment B raw34140step3 raw34140step3Labels := by
      have ha : raw34140step3 = raw34140step2 := by apply Matrix.ext; unfold raw34140step3 raw34140step2; decide +kernel
      have hl : raw34140step2Labels = labelEmbedding1 ∘ raw34140step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34140step2 raw34140step2Labels raw34140step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2158 node2158Labels := by rfl

def raw34141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34141Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw34141step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34141step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34141step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34141step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34141 raw34141Labels = mixedMoment B node2178 node2178Labels := by
  calc
    mixedMoment B raw34141 raw34141Labels = mixedMoment B raw34141step0 raw34141step0Labels := by
      have ha : raw34141step0 = (fun i j => raw34141 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34141step0 raw34141; decide +kernel
      have hl : raw34141step0Labels = raw34141Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34141 raw34141Labels permutation157 permutation7
    mixedMoment B raw34141step0 raw34141step0Labels = mixedMoment B raw34141step1 raw34141step1Labels := by
      have ha : raw34141step1 = -raw34141step0 := by apply Matrix.ext; change ∀ i j, raw34141step1 i j = -(raw34141step0 i j); unfold raw34141step1 raw34141step0; decide +kernel
      have hl : raw34141step1Labels = raw34141step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34141step1 raw34141step1Labels = mixedMoment B raw34141step2 raw34141step2Labels := by
      have ha : raw34141step2 = raw34141step1 := by apply Matrix.ext; unfold raw34141step2 raw34141step1; decide +kernel
      have hl : raw34141step1Labels = labelEmbedding1 ∘ raw34141step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34141step1 raw34141step1Labels raw34141step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2178 node2178Labels := by rfl

def raw34142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34142Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34142step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw34142step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw34142step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34142step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw34142step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34142 raw34142Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw34142 raw34142Labels = mixedMoment B raw34142step0 raw34142step0Labels := by
      have hz : ∀ j, raw34142 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34142step0 = (fun i j => raw34142 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34142step0 raw34142; decide +kernel
      have hl : raw34142step0Labels = raw34142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34142 raw34142Labels permutation346 hz
    mixedMoment B raw34142step0 raw34142step0Labels = mixedMoment B raw34142step1 raw34142step1Labels := by
      have ha : raw34142step1 = (fun i j => raw34142step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34142step1 raw34142step0; decide +kernel
      have hl : raw34142step1Labels = raw34142step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34142step0 raw34142step0Labels permutation37 permutation7
    mixedMoment B raw34142step1 raw34142step1Labels = mixedMoment B raw34142step2 raw34142step2Labels := by
      have ha : raw34142step2 = -raw34142step1 := by apply Matrix.ext; change ∀ i j, raw34142step2 i j = -(raw34142step1 i j); unfold raw34142step2 raw34142step1; decide +kernel
      have hl : raw34142step2Labels = raw34142step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34142step2 raw34142step2Labels = mixedMoment B raw34142step3 raw34142step3Labels := by
      have ha : raw34142step3 = raw34142step2 := by apply Matrix.ext; unfold raw34142step3 raw34142step2; decide +kernel
      have hl : raw34142step2Labels = labelEmbedding1 ∘ raw34142step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34142step2 raw34142step2Labels raw34142step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2217 node2217Labels := by rfl

def raw34143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw34143Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw34143step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw34143step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34143step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34143step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw34143step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34143 raw34143Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw34143 raw34143Labels = mixedMoment B raw34143step0 raw34143step0Labels := by
      have hz : ∀ j, raw34143 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34143step0 = (fun i j => raw34143 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34143step0 raw34143; decide +kernel
      have hl : raw34143step0Labels = raw34143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34143 raw34143Labels permutation346 hz
    mixedMoment B raw34143step0 raw34143step0Labels = mixedMoment B raw34143step1 raw34143step1Labels := by
      have ha : raw34143step1 = (fun i j => raw34143step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34143step1 raw34143step0; decide +kernel
      have hl : raw34143step1Labels = raw34143step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34143step0 raw34143step0Labels permutation37 permutation7
    mixedMoment B raw34143step1 raw34143step1Labels = mixedMoment B raw34143step2 raw34143step2Labels := by
      have ha : raw34143step2 = -raw34143step1 := by apply Matrix.ext; change ∀ i j, raw34143step2 i j = -(raw34143step1 i j); unfold raw34143step2 raw34143step1; decide +kernel
      have hl : raw34143step2Labels = raw34143step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34143step2 raw34143step2Labels = mixedMoment B raw34143step3 raw34143step3Labels := by
      have ha : raw34143step3 = raw34143step2 := by apply Matrix.ext; unfold raw34143step3 raw34143step2; decide +kernel
      have hl : raw34143step2Labels = labelEmbedding1 ∘ raw34143step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34143step2 raw34143step2Labels raw34143step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2206 node2206Labels := by rfl

def raw34144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34144Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34144step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw34144step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34144step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw34144step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34144step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw34144step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34144 raw34144Labels = mixedMoment B node2162 node2162Labels := by
  calc
    mixedMoment B raw34144 raw34144Labels = mixedMoment B raw34144step0 raw34144step0Labels := by
      have hz : ∀ j, raw34144 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34144step0 = (fun i j => raw34144 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34144step0 raw34144; decide +kernel
      have hl : raw34144step0Labels = raw34144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34144 raw34144Labels permutation346 hz
    mixedMoment B raw34144step0 raw34144step0Labels = mixedMoment B raw34144step1 raw34144step1Labels := by
      have ha : raw34144step1 = (fun i j => raw34144step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34144step1 raw34144step0; decide +kernel
      have hl : raw34144step1Labels = raw34144step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34144step0 raw34144step0Labels permutation37 permutation7
    mixedMoment B raw34144step1 raw34144step1Labels = mixedMoment B raw34144step2 raw34144step2Labels := by
      have ha : raw34144step2 = -raw34144step1 := by apply Matrix.ext; change ∀ i j, raw34144step2 i j = -(raw34144step1 i j); unfold raw34144step2 raw34144step1; decide +kernel
      have hl : raw34144step2Labels = raw34144step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34144step2 raw34144step2Labels = mixedMoment B raw34144step3 raw34144step3Labels := by
      have ha : raw34144step3 = raw34144step2 := by apply Matrix.ext; unfold raw34144step3 raw34144step2; decide +kernel
      have hl : raw34144step2Labels = labelEmbedding1 ∘ raw34144step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34144step2 raw34144step2Labels raw34144step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2162 node2162Labels := by rfl

def raw34145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34145Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34145step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -3, 3], ![-1, 0, 1], ![-2, 1, 1]]
def raw34145step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34145step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw34145step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34145step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw34145step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34145 raw34145Labels = mixedMoment B node2179 node2179Labels := by
  calc
    mixedMoment B raw34145 raw34145Labels = mixedMoment B raw34145step0 raw34145step0Labels := by
      have ha : raw34145step0 = (fun i j => raw34145 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34145step0 raw34145; decide +kernel
      have hl : raw34145step0Labels = raw34145Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34145 raw34145Labels permutation157 permutation7
    mixedMoment B raw34145step0 raw34145step0Labels = mixedMoment B raw34145step1 raw34145step1Labels := by
      have ha : raw34145step1 = -raw34145step0 := by apply Matrix.ext; change ∀ i j, raw34145step1 i j = -(raw34145step0 i j); unfold raw34145step1 raw34145step0; decide +kernel
      have hl : raw34145step1Labels = raw34145step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34145step1 raw34145step1Labels = mixedMoment B raw34145step2 raw34145step2Labels := by
      have ha : raw34145step2 = raw34145step1 := by apply Matrix.ext; unfold raw34145step2 raw34145step1; decide +kernel
      have hl : raw34145step1Labels = labelEmbedding1 ∘ raw34145step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34145step1 raw34145step1Labels raw34145step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2179 node2179Labels := by rfl

def raw34146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34146Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34146step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw34146step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34146step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw34146step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34146 raw34146Labels = mixedMoment B node2221 node2221Labels := by
  calc
    mixedMoment B raw34146 raw34146Labels = mixedMoment B raw34146step0 raw34146step0Labels := by
      have hz : ∀ j, raw34146 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34146step0 = (fun i j => raw34146 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34146step0 raw34146; decide +kernel
      have hl : raw34146step0Labels = raw34146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34146 raw34146Labels permutation346 hz
    mixedMoment B raw34146step0 raw34146step0Labels = mixedMoment B raw34146step1 raw34146step1Labels := by
      have ha : raw34146step1 = (fun i j => raw34146step0 (permutation146 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34146step1 raw34146step0; decide +kernel
      have hl : raw34146step1Labels = raw34146step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34146step0 raw34146step0Labels permutation146 permutation5
    mixedMoment B raw34146step1 raw34146step1Labels = mixedMoment B raw34146step2 raw34146step2Labels := by
      have ha : raw34146step2 = raw34146step1 := by apply Matrix.ext; unfold raw34146step2 raw34146step1; decide +kernel
      have hl : raw34146step1Labels = labelEmbedding1 ∘ raw34146step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34146step1 raw34146step1Labels raw34146step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2221 node2221Labels := by rfl

def raw34147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw34147Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![0, 1, -1], ![3, -3, 0]]
def raw34147step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw34147step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw34147step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34147step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw34147step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34147 raw34147Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw34147 raw34147Labels = mixedMoment B raw34147step0 raw34147step0Labels := by
      have hz : ∀ j, raw34147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34147step0 = (fun i j => raw34147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34147step0 raw34147; decide +kernel
      have hl : raw34147step0Labels = raw34147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34147 raw34147Labels permutation346 hz
    mixedMoment B raw34147step0 raw34147step0Labels = mixedMoment B raw34147step1 raw34147step1Labels := by
      have ha : raw34147step1 = (fun i j => raw34147step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34147step1 raw34147step0; decide +kernel
      have hl : raw34147step1Labels = raw34147step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34147step0 raw34147step0Labels permutation37 permutation7
    mixedMoment B raw34147step1 raw34147step1Labels = mixedMoment B raw34147step2 raw34147step2Labels := by
      have ha : raw34147step2 = -raw34147step1 := by apply Matrix.ext; change ∀ i j, raw34147step2 i j = -(raw34147step1 i j); unfold raw34147step2 raw34147step1; decide +kernel
      have hl : raw34147step2Labels = raw34147step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34147step2 raw34147step2Labels = mixedMoment B raw34147step3 raw34147step3Labels := by
      have ha : raw34147step3 = raw34147step2 := by apply Matrix.ext; unfold raw34147step3 raw34147step2; decide +kernel
      have hl : raw34147step2Labels = labelEmbedding1 ∘ raw34147step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34147step2 raw34147step2Labels raw34147step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2220 node2220Labels := by rfl

def raw34148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34148Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34148step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34148step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34148 raw34148Labels = mixedMoment B node3395 node3395Labels := by
  calc
    mixedMoment B raw34148 raw34148Labels = mixedMoment B raw34148step0 raw34148step0Labels := by
      have hz : ∀ j, raw34148 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34148step0 = (fun i j => raw34148 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34148step0 raw34148; decide +kernel
      have hl : raw34148step0Labels = raw34148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34148 raw34148Labels permutation346 hz
    mixedMoment B raw34148step0 raw34148step0Labels = mixedMoment B raw34148step1 raw34148step1Labels := by
      have ha : raw34148step1 = (fun i j => raw34148step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34148step1 raw34148step0; decide +kernel
      have hl : raw34148step1Labels = raw34148step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34148step0 raw34148step0Labels permutation34 permutation2
    _ = mixedMoment B node3395 node3395Labels := by rfl

def raw34149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34149Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34149step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34149step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34149 raw34149Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw34149 raw34149Labels = mixedMoment B raw34149step0 raw34149step0Labels := by
      have hz : ∀ j, raw34149 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34149step0 = (fun i j => raw34149 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34149step0 raw34149; decide +kernel
      have hl : raw34149step0Labels = raw34149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34149 raw34149Labels permutation346 hz
    mixedMoment B raw34149step0 raw34149step0Labels = mixedMoment B raw34149step1 raw34149step1Labels := by
      have ha : raw34149step1 = (fun i j => raw34149step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34149step1 raw34149step0; decide +kernel
      have hl : raw34149step1Labels = raw34149step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34149step0 raw34149step0Labels permutation34 permutation2
    _ = mixedMoment B node2058 node2058Labels := by rfl

def raw34150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34150Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34150step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34150step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34150 raw34150Labels = mixedMoment B node1806 node1806Labels := by
  calc
    mixedMoment B raw34150 raw34150Labels = mixedMoment B raw34150step0 raw34150step0Labels := by
      have ha : raw34150step0 = (fun i j => raw34150 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34150step0 raw34150; decide +kernel
      have hl : raw34150step0Labels = raw34150Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34150 raw34150Labels permutation154 permutation2
    _ = mixedMoment B node1806 node1806Labels := by rfl

def raw34151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34151Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw34151step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34151step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34151 raw34151Labels = mixedMoment B node1814 node1814Labels := by
  calc
    mixedMoment B raw34151 raw34151Labels = mixedMoment B raw34151step0 raw34151step0Labels := by
      have hz : ∀ j, raw34151 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34151step0 = (fun i j => raw34151 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34151step0 raw34151; decide +kernel
      have hl : raw34151step0Labels = raw34151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34151 raw34151Labels permutation346 hz
    mixedMoment B raw34151step0 raw34151step0Labels = mixedMoment B raw34151step1 raw34151step1Labels := by
      have ha : raw34151step1 = (fun i j => raw34151step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34151step1 raw34151step0; decide +kernel
      have hl : raw34151step1Labels = raw34151step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34151step0 raw34151step0Labels permutation35 permutation2
    _ = mixedMoment B node1814 node1814Labels := by rfl

def raw34152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34152Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw34152step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34152step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34152 raw34152Labels = mixedMoment B node1816 node1816Labels := by
  calc
    mixedMoment B raw34152 raw34152Labels = mixedMoment B raw34152step0 raw34152step0Labels := by
      have hz : ∀ j, raw34152 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34152step0 = (fun i j => raw34152 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34152step0 raw34152; decide +kernel
      have hl : raw34152step0Labels = raw34152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34152 raw34152Labels permutation346 hz
    mixedMoment B raw34152step0 raw34152step0Labels = mixedMoment B raw34152step1 raw34152step1Labels := by
      have ha : raw34152step1 = (fun i j => raw34152step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34152step1 raw34152step0; decide +kernel
      have hl : raw34152step1Labels = raw34152step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34152step0 raw34152step0Labels permutation33 permutation2
    _ = mixedMoment B node1816 node1816Labels := by rfl

def raw34153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34153Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw34153step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw34153step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34153 raw34153Labels = mixedMoment B node1813 node1813Labels := by
  calc
    mixedMoment B raw34153 raw34153Labels = mixedMoment B raw34153step0 raw34153step0Labels := by
      have hz : ∀ j, raw34153 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34153step0 = (fun i j => raw34153 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34153step0 raw34153; decide +kernel
      have hl : raw34153step0Labels = raw34153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34153 raw34153Labels permutation346 hz
    mixedMoment B raw34153step0 raw34153step0Labels = mixedMoment B raw34153step1 raw34153step1Labels := by
      have ha : raw34153step1 = (fun i j => raw34153step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34153step1 raw34153step0; decide +kernel
      have hl : raw34153step1Labels = raw34153step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34153step0 raw34153step0Labels permutation34 permutation2
    _ = mixedMoment B node1813 node1813Labels := by rfl

def raw34154 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![1, -1], ![0, 0]]
def raw34154Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34154step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]
def raw34154step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34154step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1]]
def raw34154step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34154step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw34154step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw34154step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw34154step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical34154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34154 raw34154Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw34154 raw34154Labels = mixedMoment B raw34154step0 raw34154step0Labels := by
      have hz : ∀ j, raw34154 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34154step0 = (fun i j => raw34154 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34154step0 raw34154; decide +kernel
      have hl : raw34154step0Labels = raw34154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34154 raw34154Labels permutation590 hz
    mixedMoment B raw34154step0 raw34154step0Labels = mixedMoment B raw34154step1 raw34154step1Labels := by
      have hz : ∀ j, raw34154step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34154step1 = (fun i j => raw34154step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34154step1 raw34154step0; decide +kernel
      have hl : raw34154step1Labels = raw34154step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34154step0 raw34154step0Labels permutation80 hz
    mixedMoment B raw34154step1 raw34154step1Labels = mixedMoment B raw34154step2 raw34154step2Labels := by
      have hz : ∀ j, raw34154step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw34154step2 = (fun i j => raw34154step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw34154step2 raw34154step1; decide +kernel
      have hl : raw34154step2Labels = raw34154step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34154step1 raw34154step1Labels permutation14 hz
    mixedMoment B raw34154step2 raw34154step2Labels = mixedMoment B raw34154step3 raw34154step3Labels := by
      have ha : raw34154step3 = (fun i j => raw34154step2 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw34154step3 raw34154step2; decide +kernel
      have hl : raw34154step3Labels = raw34154step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34154step2 raw34154step2Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw34155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34155step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34155step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34155step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34155 raw34155Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw34155 raw34155Labels = mixedMoment B raw34155step0 raw34155step0Labels := by
      have hz : ∀ j, raw34155 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34155step0 = (fun i j => raw34155 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34155step0 raw34155; decide +kernel
      have hl : raw34155step0Labels = raw34155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34155 raw34155Labels permutation346 hz
    mixedMoment B raw34155step0 raw34155step0Labels = mixedMoment B raw34155step1 raw34155step1Labels := by
      have ha : raw34155step1 = (fun i j => raw34155step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34155step1 raw34155step0; decide +kernel
      have hl : raw34155step1Labels = raw34155step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34155step0 raw34155step0Labels permutation34 permutation3
    mixedMoment B raw34155step1 raw34155step1Labels = mixedMoment B raw34155step2 raw34155step2Labels := by
      have ha : raw34155step2 = raw34155step1 := by apply Matrix.ext; unfold raw34155step2 raw34155step1; decide +kernel
      have hl : raw34155step1Labels = labelEmbedding6 ∘ raw34155step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34155step1 raw34155step1Labels raw34155step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw34156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34156step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34156step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34156step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34156step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34156 raw34156Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw34156 raw34156Labels = mixedMoment B raw34156step0 raw34156step0Labels := by
      have ha : raw34156step0 = (fun i j => raw34156 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34156step0 raw34156; decide +kernel
      have hl : raw34156step0Labels = raw34156Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34156 raw34156Labels permutation178 permutation3
    mixedMoment B raw34156step0 raw34156step0Labels = mixedMoment B raw34156step1 raw34156step1Labels := by
      have ha : raw34156step1 = raw34156step0 := by apply Matrix.ext; unfold raw34156step1 raw34156step0; decide +kernel
      have hl : raw34156step0Labels = labelEmbedding6 ∘ raw34156step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34156step0 raw34156step0Labels raw34156step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw34157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34157step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw34157step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34157step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34157step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34157 raw34157Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw34157 raw34157Labels = mixedMoment B raw34157step0 raw34157step0Labels := by
      have hz : ∀ j, raw34157 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34157step0 = (fun i j => raw34157 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34157step0 raw34157; decide +kernel
      have hl : raw34157step0Labels = raw34157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34157 raw34157Labels permutation346 hz
    mixedMoment B raw34157step0 raw34157step0Labels = mixedMoment B raw34157step1 raw34157step1Labels := by
      have ha : raw34157step1 = (fun i j => raw34157step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34157step1 raw34157step0; decide +kernel
      have hl : raw34157step1Labels = raw34157step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34157step0 raw34157step0Labels permutation151 permutation2
    mixedMoment B raw34157step1 raw34157step1Labels = mixedMoment B raw34157step2 raw34157step2Labels := by
      have ha : raw34157step2 = -raw34157step1 := by apply Matrix.ext; change ∀ i j, raw34157step2 i j = -(raw34157step1 i j); unfold raw34157step2 raw34157step1; decide +kernel
      have hl : raw34157step2Labels = raw34157step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw34158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw34158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw34158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34158step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw34158step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34158step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34158step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34158step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34158step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34158 raw34158Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw34158 raw34158Labels = mixedMoment B raw34158step0 raw34158step0Labels := by
      have hz : ∀ j, raw34158 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34158step0 = (fun i j => raw34158 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34158step0 raw34158; decide +kernel
      have hl : raw34158step0Labels = raw34158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34158 raw34158Labels permutation520 hz
    mixedMoment B raw34158step0 raw34158step0Labels = mixedMoment B raw34158step1 raw34158step1Labels := by
      have hz : ∀ j, raw34158step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34158step1 = (fun i j => raw34158step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34158step1 raw34158step0; decide +kernel
      have hl : raw34158step1Labels = raw34158step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34158step0 raw34158step0Labels permutation80 hz
    mixedMoment B raw34158step1 raw34158step1Labels = mixedMoment B raw34158step2 raw34158step2Labels := by
      have ha : raw34158step2 = (fun i j => raw34158step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34158step2 raw34158step1; decide +kernel
      have hl : raw34158step2Labels = raw34158step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34158step1 raw34158step1Labels permutation8 permutation3
    mixedMoment B raw34158step2 raw34158step2Labels = mixedMoment B raw34158step3 raw34158step3Labels := by
      have ha : raw34158step3 = raw34158step2 := by apply Matrix.ext; unfold raw34158step3 raw34158step2; decide +kernel
      have hl : raw34158step2Labels = labelEmbedding6 ∘ raw34158step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34158step2 raw34158step2Labels raw34158step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw34159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw34159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw34159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34159step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34159step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw34159step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34159 raw34159Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw34159 raw34159Labels = mixedMoment B raw34159step0 raw34159step0Labels := by
      have hz : ∀ j, raw34159 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34159step0 = (fun i j => raw34159 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34159step0 raw34159; decide +kernel
      have hl : raw34159step0Labels = raw34159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34159 raw34159Labels permutation346 hz
    mixedMoment B raw34159step0 raw34159step0Labels = mixedMoment B raw34159step1 raw34159step1Labels := by
      have ha : raw34159step1 = (fun i j => raw34159step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34159step1 raw34159step0; decide +kernel
      have hl : raw34159step1Labels = raw34159step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34159step0 raw34159step0Labels permutation37 permutation3
    mixedMoment B raw34159step1 raw34159step1Labels = mixedMoment B raw34159step2 raw34159step2Labels := by
      have ha : raw34159step2 = raw34159step1 := by apply Matrix.ext; unfold raw34159step2 raw34159step1; decide +kernel
      have hl : raw34159step1Labels = labelEmbedding6 ∘ raw34159step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34159step1 raw34159step1Labels raw34159step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw34160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34160step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34160step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34160step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34160step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34160 raw34160Labels = mixedMoment B node4268 node4268Labels := by
  calc
    mixedMoment B raw34160 raw34160Labels = mixedMoment B raw34160step0 raw34160step0Labels := by
      have hz : ∀ j, raw34160 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34160step0 = (fun i j => raw34160 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34160step0 raw34160; decide +kernel
      have hl : raw34160step0Labels = raw34160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34160 raw34160Labels permutation346 hz
    mixedMoment B raw34160step0 raw34160step0Labels = mixedMoment B raw34160step1 raw34160step1Labels := by
      have ha : raw34160step1 = (fun i j => raw34160step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34160step1 raw34160step0; decide +kernel
      have hl : raw34160step1Labels = raw34160step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34160step0 raw34160step0Labels permutation34 permutation3
    mixedMoment B raw34160step1 raw34160step1Labels = mixedMoment B raw34160step2 raw34160step2Labels := by
      have ha : raw34160step2 = raw34160step1 := by apply Matrix.ext; unfold raw34160step2 raw34160step1; decide +kernel
      have hl : raw34160step1Labels = labelEmbedding6 ∘ raw34160step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34160step1 raw34160step1Labels raw34160step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4268 node4268Labels := by rfl

def raw34161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34161step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34161step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34161step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34161 raw34161Labels = mixedMoment B node4740 node4740Labels := by
  calc
    mixedMoment B raw34161 raw34161Labels = mixedMoment B raw34161step0 raw34161step0Labels := by
      have ha : raw34161step0 = (fun i j => raw34161 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34161step0 raw34161; decide +kernel
      have hl : raw34161step0Labels = raw34161Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34161 raw34161Labels permutation178 permutation3
    mixedMoment B raw34161step0 raw34161step0Labels = mixedMoment B raw34161step1 raw34161step1Labels := by
      have ha : raw34161step1 = raw34161step0 := by apply Matrix.ext; unfold raw34161step1 raw34161step0; decide +kernel
      have hl : raw34161step0Labels = labelEmbedding6 ∘ raw34161step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34161step0 raw34161step0Labels raw34161step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4740 node4740Labels := by rfl

def raw34162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34162step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34162step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34162step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34162 raw34162Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw34162 raw34162Labels = mixedMoment B raw34162step0 raw34162step0Labels := by
      have hz : ∀ j, raw34162 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34162step0 = (fun i j => raw34162 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34162step0 raw34162; decide +kernel
      have hl : raw34162step0Labels = raw34162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34162 raw34162Labels permutation346 hz
    mixedMoment B raw34162step0 raw34162step0Labels = mixedMoment B raw34162step1 raw34162step1Labels := by
      have ha : raw34162step1 = (fun i j => raw34162step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34162step1 raw34162step0; decide +kernel
      have hl : raw34162step1Labels = raw34162step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34162step0 raw34162step0Labels permutation32 permutation3
    mixedMoment B raw34162step1 raw34162step1Labels = mixedMoment B raw34162step2 raw34162step2Labels := by
      have ha : raw34162step2 = raw34162step1 := by apply Matrix.ext; unfold raw34162step2 raw34162step1; decide +kernel
      have hl : raw34162step1Labels = labelEmbedding6 ∘ raw34162step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34162step1 raw34162step1Labels raw34162step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw34163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw34163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw34163step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34163step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw34163step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34163step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34163step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34163step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34163step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34163 raw34163Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw34163 raw34163Labels = mixedMoment B raw34163step0 raw34163step0Labels := by
      have hz : ∀ j, raw34163 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34163step0 = (fun i j => raw34163 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34163step0 raw34163; decide +kernel
      have hl : raw34163step0Labels = raw34163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34163 raw34163Labels permutation520 hz
    mixedMoment B raw34163step0 raw34163step0Labels = mixedMoment B raw34163step1 raw34163step1Labels := by
      have hz : ∀ j, raw34163step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34163step1 = (fun i j => raw34163step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34163step1 raw34163step0; decide +kernel
      have hl : raw34163step1Labels = raw34163step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34163step0 raw34163step0Labels permutation80 hz
    mixedMoment B raw34163step1 raw34163step1Labels = mixedMoment B raw34163step2 raw34163step2Labels := by
      have ha : raw34163step2 = (fun i j => raw34163step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34163step2 raw34163step1; decide +kernel
      have hl : raw34163step2Labels = raw34163step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34163step1 raw34163step1Labels permutation8 permutation3
    mixedMoment B raw34163step2 raw34163step2Labels = mixedMoment B raw34163step3 raw34163step3Labels := by
      have ha : raw34163step3 = raw34163step2 := by apply Matrix.ext; unfold raw34163step3 raw34163step2; decide +kernel
      have hl : raw34163step2Labels = labelEmbedding6 ∘ raw34163step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34163step2 raw34163step2Labels raw34163step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw34164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw34164Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw34164step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw34164step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34164step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34164step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34164step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34164step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34164 raw34164Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw34164 raw34164Labels = mixedMoment B raw34164step0 raw34164step0Labels := by
      have hz : ∀ j, raw34164 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34164step0 = (fun i j => raw34164 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34164step0 raw34164; decide +kernel
      have hl : raw34164step0Labels = raw34164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34164 raw34164Labels permutation346 hz
    mixedMoment B raw34164step0 raw34164step0Labels = mixedMoment B raw34164step1 raw34164step1Labels := by
      have ha : raw34164step1 = (fun i j => raw34164step0 (permutation51 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34164step1 raw34164step0; decide +kernel
      have hl : raw34164step1Labels = raw34164step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34164step0 raw34164step0Labels permutation51 permutation5
    mixedMoment B raw34164step1 raw34164step1Labels = mixedMoment B raw34164step2 raw34164step2Labels := by
      have ha : raw34164step2 = -raw34164step1 := by apply Matrix.ext; change ∀ i j, raw34164step2 i j = -(raw34164step1 i j); unfold raw34164step2 raw34164step1; decide +kernel
      have hl : raw34164step2Labels = raw34164step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34164step2 raw34164step2Labels = mixedMoment B raw34164step3 raw34164step3Labels := by
      have ha : raw34164step3 = raw34164step2 := by apply Matrix.ext; unfold raw34164step3 raw34164step2; decide +kernel
      have hl : raw34164step2Labels = labelEmbedding8 ∘ raw34164step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34164step2 raw34164step2Labels raw34164step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw34165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34165Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34165step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34165step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34165step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34165step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34165 raw34165Labels = mixedMoment B node4217 node4217Labels := by
  calc
    mixedMoment B raw34165 raw34165Labels = mixedMoment B raw34165step0 raw34165step0Labels := by
      have ha : raw34165step0 = (fun i j => raw34165 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34165step0 raw34165; decide +kernel
      have hl : raw34165step0Labels = raw34165Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34165 raw34165Labels permutation154 permutation3
    mixedMoment B raw34165step0 raw34165step0Labels = mixedMoment B raw34165step1 raw34165step1Labels := by
      have ha : raw34165step1 = raw34165step0 := by apply Matrix.ext; unfold raw34165step1 raw34165step0; decide +kernel
      have hl : raw34165step0Labels = labelEmbedding6 ∘ raw34165step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34165step0 raw34165step0Labels raw34165step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4217 node4217Labels := by rfl

def raw34166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34166Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34166step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34166step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34166step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34166 raw34166Labels = mixedMoment B node4648 node4648Labels := by
  calc
    mixedMoment B raw34166 raw34166Labels = mixedMoment B raw34166step0 raw34166step0Labels := by
      have ha : raw34166step0 = (fun i j => raw34166 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34166step0 raw34166; decide +kernel
      have hl : raw34166step0Labels = raw34166Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34166 raw34166Labels permutation154 permutation3
    mixedMoment B raw34166step0 raw34166step0Labels = mixedMoment B raw34166step1 raw34166step1Labels := by
      have ha : raw34166step1 = raw34166step0 := by apply Matrix.ext; unfold raw34166step1 raw34166step0; decide +kernel
      have hl : raw34166step0Labels = labelEmbedding6 ∘ raw34166step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34166step0 raw34166step0Labels raw34166step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4648 node4648Labels := by rfl

def raw34167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34167Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34167step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34167step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34167step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34167step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34167 raw34167Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw34167 raw34167Labels = mixedMoment B raw34167step0 raw34167step0Labels := by
      have ha : raw34167step0 = (fun i j => raw34167 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34167step0 raw34167; decide +kernel
      have hl : raw34167step0Labels = raw34167Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34167 raw34167Labels permutation158 permutation3
    mixedMoment B raw34167step0 raw34167step0Labels = mixedMoment B raw34167step1 raw34167step1Labels := by
      have ha : raw34167step1 = raw34167step0 := by apply Matrix.ext; unfold raw34167step1 raw34167step0; decide +kernel
      have hl : raw34167step0Labels = labelEmbedding6 ∘ raw34167step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34167step0 raw34167step0Labels raw34167step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

def raw34168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw34168Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw34168step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34168step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw34168step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34168 raw34168Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw34168 raw34168Labels = mixedMoment B raw34168step0 raw34168step0Labels := by
      have hz : ∀ j, raw34168 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34168step0 = (fun i j => raw34168 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34168step0 raw34168; decide +kernel
      have hl : raw34168step0Labels = raw34168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34168 raw34168Labels permutation520 hz
    mixedMoment B raw34168step0 raw34168step0Labels = mixedMoment B raw34168step1 raw34168step1Labels := by
      have ha : raw34168step1 = (fun i j => raw34168step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34168step1 raw34168step0; decide +kernel
      have hl : raw34168step1Labels = raw34168step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34168step0 raw34168step0Labels permutation32 permutation3
    mixedMoment B raw34168step1 raw34168step1Labels = mixedMoment B raw34168step2 raw34168step2Labels := by
      have ha : raw34168step2 = raw34168step1 := by apply Matrix.ext; unfold raw34168step2 raw34168step1; decide +kernel
      have hl : raw34168step1Labels = labelEmbedding6 ∘ raw34168step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34168step1 raw34168step1Labels raw34168step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw34169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw34169Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34169step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34169step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34169step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34169step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34169 raw34169Labels = mixedMoment B node4826 node4826Labels := by
  calc
    mixedMoment B raw34169 raw34169Labels = mixedMoment B raw34169step0 raw34169step0Labels := by
      have ha : raw34169step0 = (fun i j => raw34169 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34169step0 raw34169; decide +kernel
      have hl : raw34169step0Labels = raw34169Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34169 raw34169Labels permutation171 permutation3
    mixedMoment B raw34169step0 raw34169step0Labels = mixedMoment B raw34169step1 raw34169step1Labels := by
      have ha : raw34169step1 = raw34169step0 := by apply Matrix.ext; unfold raw34169step1 raw34169step0; decide +kernel
      have hl : raw34169step0Labels = labelEmbedding6 ∘ raw34169step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34169step0 raw34169step0Labels raw34169step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4826 node4826Labels := by rfl

def raw34170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34170Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34170step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw34170step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34170step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw34170step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34170 raw34170Labels = mixedMoment B node4220 node4220Labels := by
  calc
    mixedMoment B raw34170 raw34170Labels = mixedMoment B raw34170step0 raw34170step0Labels := by
      have hz : ∀ j, raw34170 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34170step0 = (fun i j => raw34170 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34170step0 raw34170; decide +kernel
      have hl : raw34170step0Labels = raw34170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34170 raw34170Labels permutation346 hz
    mixedMoment B raw34170step0 raw34170step0Labels = mixedMoment B raw34170step1 raw34170step1Labels := by
      have ha : raw34170step1 = (fun i j => raw34170step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34170step1 raw34170step0; decide +kernel
      have hl : raw34170step1Labels = raw34170step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34170step0 raw34170step0Labels permutation35 permutation3
    mixedMoment B raw34170step1 raw34170step1Labels = mixedMoment B raw34170step2 raw34170step2Labels := by
      have ha : raw34170step2 = raw34170step1 := by apply Matrix.ext; unfold raw34170step2 raw34170step1; decide +kernel
      have hl : raw34170step1Labels = labelEmbedding6 ∘ raw34170step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34170step1 raw34170step1Labels raw34170step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4220 node4220Labels := by rfl

def raw34171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34171Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 1, 1], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34171step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw34171step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34171step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw34171step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34171 raw34171Labels = mixedMoment B node4651 node4651Labels := by
  calc
    mixedMoment B raw34171 raw34171Labels = mixedMoment B raw34171step0 raw34171step0Labels := by
      have hz : ∀ j, raw34171 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34171step0 = (fun i j => raw34171 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34171step0 raw34171; decide +kernel
      have hl : raw34171step0Labels = raw34171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34171 raw34171Labels permutation346 hz
    mixedMoment B raw34171step0 raw34171step0Labels = mixedMoment B raw34171step1 raw34171step1Labels := by
      have ha : raw34171step1 = (fun i j => raw34171step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34171step1 raw34171step0; decide +kernel
      have hl : raw34171step1Labels = raw34171step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34171step0 raw34171step0Labels permutation35 permutation3
    mixedMoment B raw34171step1 raw34171step1Labels = mixedMoment B raw34171step2 raw34171step2Labels := by
      have ha : raw34171step2 = raw34171step1 := by apply Matrix.ext; unfold raw34171step2 raw34171step1; decide +kernel
      have hl : raw34171step1Labels = labelEmbedding6 ∘ raw34171step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34171step1 raw34171step1Labels raw34171step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4651 node4651Labels := by rfl

def raw34172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![2, 0, -2]]
def raw34172Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34172step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw34172step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34172step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw34172step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34172 raw34172Labels = mixedMoment B node4714 node4714Labels := by
  calc
    mixedMoment B raw34172 raw34172Labels = mixedMoment B raw34172step0 raw34172step0Labels := by
      have ha : raw34172step0 = (fun i j => raw34172 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34172step0 raw34172; decide +kernel
      have hl : raw34172step0Labels = raw34172Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34172 raw34172Labels permutation179 permutation3
    mixedMoment B raw34172step0 raw34172step0Labels = mixedMoment B raw34172step1 raw34172step1Labels := by
      have ha : raw34172step1 = raw34172step0 := by apply Matrix.ext; unfold raw34172step1 raw34172step0; decide +kernel
      have hl : raw34172step0Labels = labelEmbedding6 ∘ raw34172step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34172step0 raw34172step0Labels raw34172step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4714 node4714Labels := by rfl

def raw34173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![0, 0, 0], ![2, 0, -2]]
def raw34173Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw34173step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![2, -3, 1], ![2, 0, -2]]
def raw34173step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34173step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34173step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34173step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw34173step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34173 raw34173Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw34173 raw34173Labels = mixedMoment B raw34173step0 raw34173step0Labels := by
      have hz : ∀ j, raw34173 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34173step0 = (fun i j => raw34173 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34173step0 raw34173; decide +kernel
      have hl : raw34173step0Labels = raw34173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34173 raw34173Labels permutation520 hz
    mixedMoment B raw34173step0 raw34173step0Labels = mixedMoment B raw34173step1 raw34173step1Labels := by
      have hz : ∀ j, raw34173step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34173step1 = (fun i j => raw34173step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34173step1 raw34173step0; decide +kernel
      have hl : raw34173step1Labels = raw34173step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34173step0 raw34173step0Labels permutation80 hz
    mixedMoment B raw34173step1 raw34173step1Labels = mixedMoment B raw34173step2 raw34173step2Labels := by
      have ha : raw34173step2 = (fun i j => raw34173step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34173step2 raw34173step1; decide +kernel
      have hl : raw34173step2Labels = raw34173step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34173step1 raw34173step1Labels permutation9 permutation3
    mixedMoment B raw34173step2 raw34173step2Labels = mixedMoment B raw34173step3 raw34173step3Labels := by
      have ha : raw34173step3 = raw34173step2 := by apply Matrix.ext; unfold raw34173step3 raw34173step2; decide +kernel
      have hl : raw34173step2Labels = labelEmbedding6 ∘ raw34173step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34173step2 raw34173step2Labels raw34173step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4845 node4845Labels := by rfl

def raw34174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw34174Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw34174step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw34174step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw34174step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34174 raw34174Labels = mixedMoment B node4827 node4827Labels := by
  calc
    mixedMoment B raw34174 raw34174Labels = mixedMoment B raw34174step0 raw34174step0Labels := by
      have hz : ∀ j, raw34174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34174step0 = (fun i j => raw34174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34174step0 raw34174; decide +kernel
      have hl : raw34174step0Labels = raw34174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34174 raw34174Labels permutation346 hz
    mixedMoment B raw34174step0 raw34174step0Labels = mixedMoment B raw34174step1 raw34174step1Labels := by
      have ha : raw34174step1 = (fun i j => raw34174step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34174step1 raw34174step0; decide +kernel
      have hl : raw34174step1Labels = raw34174step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34174step0 raw34174step0Labels permutation37 permutation3
    mixedMoment B raw34174step1 raw34174step1Labels = mixedMoment B raw34174step2 raw34174step2Labels := by
      have ha : raw34174step2 = raw34174step1 := by apply Matrix.ext; unfold raw34174step2 raw34174step1; decide +kernel
      have hl : raw34174step1Labels = labelEmbedding6 ∘ raw34174step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34174step1 raw34174step1Labels raw34174step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4827 node4827Labels := by rfl

def raw34175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw34175Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 0, 1], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw34175step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw34175step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34175step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw34175step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34175 raw34175Labels = mixedMoment B node4223 node4223Labels := by
  calc
    mixedMoment B raw34175 raw34175Labels = mixedMoment B raw34175step0 raw34175step0Labels := by
      have hz : ∀ j, raw34175 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34175step0 = (fun i j => raw34175 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34175step0 raw34175; decide +kernel
      have hl : raw34175step0Labels = raw34175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34175 raw34175Labels permutation346 hz
    mixedMoment B raw34175step0 raw34175step0Labels = mixedMoment B raw34175step1 raw34175step1Labels := by
      have ha : raw34175step1 = (fun i j => raw34175step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34175step1 raw34175step0; decide +kernel
      have hl : raw34175step1Labels = raw34175step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34175step0 raw34175step0Labels permutation33 permutation3
    mixedMoment B raw34175step1 raw34175step1Labels = mixedMoment B raw34175step2 raw34175step2Labels := by
      have ha : raw34175step2 = raw34175step1 := by apply Matrix.ext; unfold raw34175step2 raw34175step1; decide +kernel
      have hl : raw34175step1Labels = labelEmbedding6 ∘ raw34175step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34175step1 raw34175step1Labels raw34175step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4223 node4223Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
