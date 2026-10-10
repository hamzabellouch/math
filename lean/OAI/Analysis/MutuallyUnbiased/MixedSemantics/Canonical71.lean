import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw9088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw9088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw9088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9088 raw9088Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw9088 raw9088Labels = mixedMoment B raw9088step0 raw9088step0Labels := by
      have hz : ∀ j, raw9088 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9088step0 = (fun i j => raw9088 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9088step0 raw9088; decide +kernel
      have hl : raw9088step0Labels = raw9088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9088 raw9088Labels permutation520 hz
    mixedMoment B raw9088step0 raw9088step0Labels = mixedMoment B raw9088step1 raw9088step1Labels := by
      have ha : raw9088step1 = (fun i j => raw9088step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9088step1 raw9088step0; decide +kernel
      have hl : raw9088step1Labels = raw9088step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9088step0 raw9088step0Labels permutation40 permutation2
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw9089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9089step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9089step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9089step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9089 raw9089Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw9089 raw9089Labels = mixedMoment B raw9089step0 raw9089step0Labels := by
      have hz : ∀ j, raw9089 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9089step0 = (fun i j => raw9089 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9089step0 raw9089; decide +kernel
      have hl : raw9089step0Labels = raw9089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9089 raw9089Labels permutation265 hz
    mixedMoment B raw9089step0 raw9089step0Labels = mixedMoment B raw9089step1 raw9089step1Labels := by
      have ha : raw9089step1 = (fun i j => raw9089step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9089step1 raw9089step0; decide +kernel
      have hl : raw9089step1Labels = raw9089step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9089step0 raw9089step0Labels permutation38 permutation3
    mixedMoment B raw9089step1 raw9089step1Labels = mixedMoment B raw9089step2 raw9089step2Labels := by
      have ha : raw9089step2 = raw9089step1 := by apply Matrix.ext; unfold raw9089step2 raw9089step1; decide +kernel
      have hl : raw9089step1Labels = labelEmbedding6 ∘ raw9089step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9089step1 raw9089step1Labels raw9089step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw9090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9090 raw9090Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw9090 raw9090Labels = mixedMoment B raw9090step0 raw9090step0Labels := by
      have ha : raw9090step0 = (fun i j => raw9090 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9090step0 raw9090; decide +kernel
      have hl : raw9090step0Labels = raw9090Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9090 raw9090Labels permutation160 permutation2
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw9091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9091step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9091 raw9091Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw9091 raw9091Labels = mixedMoment B raw9091step0 raw9091step0Labels := by
      have hz : ∀ j, raw9091 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9091step0 = (fun i j => raw9091 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9091step0 raw9091; decide +kernel
      have hl : raw9091step0Labels = raw9091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9091 raw9091Labels permutation265 hz
    mixedMoment B raw9091step0 raw9091step0Labels = mixedMoment B raw9091step1 raw9091step1Labels := by
      have ha : raw9091step1 = (fun i j => raw9091step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9091step1 raw9091step0; decide +kernel
      have hl : raw9091step1Labels = raw9091step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9091step0 raw9091step0Labels permutation40 permutation2
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw9092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw9092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw9092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw9092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9092step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9092step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9092 raw9092Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw9092 raw9092Labels = mixedMoment B raw9092step0 raw9092step0Labels := by
      have hz : ∀ j, raw9092 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9092step0 = (fun i j => raw9092 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9092step0 raw9092; decide +kernel
      have hl : raw9092step0Labels = raw9092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9092 raw9092Labels permutation520 hz
    mixedMoment B raw9092step0 raw9092step0Labels = mixedMoment B raw9092step1 raw9092step1Labels := by
      have hz : ∀ j, raw9092step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9092step1 = (fun i j => raw9092step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9092step1 raw9092step0; decide +kernel
      have hl : raw9092step1Labels = raw9092step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9092step0 raw9092step0Labels permutation56 hz
    mixedMoment B raw9092step1 raw9092step1Labels = mixedMoment B raw9092step2 raw9092step2Labels := by
      have ha : raw9092step2 = (fun i j => raw9092step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9092step2 raw9092step1; decide +kernel
      have hl : raw9092step2Labels = raw9092step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9092step1 raw9092step1Labels permutation10 permutation2
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw9093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9093step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9093step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9093step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9093 raw9093Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw9093 raw9093Labels = mixedMoment B raw9093step0 raw9093step0Labels := by
      have hz : ∀ j, raw9093 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9093step0 = (fun i j => raw9093 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9093step0 raw9093; decide +kernel
      have hl : raw9093step0Labels = raw9093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9093 raw9093Labels permutation265 hz
    mixedMoment B raw9093step0 raw9093step0Labels = mixedMoment B raw9093step1 raw9093step1Labels := by
      have ha : raw9093step1 = (fun i j => raw9093step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9093step1 raw9093step0; decide +kernel
      have hl : raw9093step1Labels = raw9093step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9093step0 raw9093step0Labels permutation32 permutation3
    mixedMoment B raw9093step1 raw9093step1Labels = mixedMoment B raw9093step2 raw9093step2Labels := by
      have ha : raw9093step2 = raw9093step1 := by apply Matrix.ext; unfold raw9093step2 raw9093step1; decide +kernel
      have hl : raw9093step1Labels = labelEmbedding6 ∘ raw9093step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9093step1 raw9093step1Labels raw9093step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw9094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9094step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9094 raw9094Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw9094 raw9094Labels = mixedMoment B raw9094step0 raw9094step0Labels := by
      have ha : raw9094step0 = (fun i j => raw9094 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9094step0 raw9094; decide +kernel
      have hl : raw9094step0Labels = raw9094Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9094 raw9094Labels permutation154 permutation2
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw9095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9095step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9095step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9095 raw9095Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw9095 raw9095Labels = mixedMoment B raw9095step0 raw9095step0Labels := by
      have hz : ∀ j, raw9095 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9095step0 = (fun i j => raw9095 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9095step0 raw9095; decide +kernel
      have hl : raw9095step0Labels = raw9095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9095 raw9095Labels permutation265 hz
    mixedMoment B raw9095step0 raw9095step0Labels = mixedMoment B raw9095step1 raw9095step1Labels := by
      have ha : raw9095step1 = (fun i j => raw9095step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9095step1 raw9095step0; decide +kernel
      have hl : raw9095step1Labels = raw9095step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9095step0 raw9095step0Labels permutation34 permutation2
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw9096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw9096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9096step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9096step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9096step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9096 raw9096Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw9096 raw9096Labels = mixedMoment B raw9096step0 raw9096step0Labels := by
      have hz : ∀ j, raw9096 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9096step0 = (fun i j => raw9096 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9096step0 raw9096; decide +kernel
      have hl : raw9096step0Labels = raw9096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9096 raw9096Labels permutation520 hz
    mixedMoment B raw9096step0 raw9096step0Labels = mixedMoment B raw9096step1 raw9096step1Labels := by
      have hz : ∀ j, raw9096step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9096step1 = (fun i j => raw9096step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9096step1 raw9096step0; decide +kernel
      have hl : raw9096step1Labels = raw9096step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9096step0 raw9096step0Labels permutation56 hz
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw9097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9097step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9097step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw9097step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9097step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw9097step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9097 raw9097Labels = mixedMoment B node4586 node4586Labels := by
  calc
    mixedMoment B raw9097 raw9097Labels = mixedMoment B raw9097step0 raw9097step0Labels := by
      have hz : ∀ j, raw9097 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9097step0 = (fun i j => raw9097 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9097step0 raw9097; decide +kernel
      have hl : raw9097step0Labels = raw9097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9097 raw9097Labels permutation265 hz
    mixedMoment B raw9097step0 raw9097step0Labels = mixedMoment B raw9097step1 raw9097step1Labels := by
      have ha : raw9097step1 = (fun i j => raw9097step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9097step1 raw9097step0; decide +kernel
      have hl : raw9097step1Labels = raw9097step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9097step0 raw9097step0Labels permutation32 permutation3
    mixedMoment B raw9097step1 raw9097step1Labels = mixedMoment B raw9097step2 raw9097step2Labels := by
      have ha : raw9097step2 = raw9097step1 := by apply Matrix.ext; unfold raw9097step2 raw9097step1; decide +kernel
      have hl : raw9097step1Labels = labelEmbedding6 ∘ raw9097step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9097step1 raw9097step1Labels raw9097step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4586 node4586Labels := by rfl

def raw9098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9098 raw9098Labels = mixedMoment B node5142 node5142Labels := by
  calc
    _ = mixedMoment B node5142 node5142Labels := by rfl

def raw9099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9099step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9099 raw9099Labels = mixedMoment B node5193 node5193Labels := by
  calc
    mixedMoment B raw9099 raw9099Labels = mixedMoment B raw9099step0 raw9099step0Labels := by
      have hz : ∀ j, raw9099 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9099step0 = (fun i j => raw9099 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9099step0 raw9099; decide +kernel
      have hl : raw9099step0Labels = raw9099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9099 raw9099Labels permutation265 hz
    _ = mixedMoment B node5193 node5193Labels := by rfl

def raw9100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9100step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9100step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9100 raw9100Labels = mixedMoment B node5193 node5193Labels := by
  calc
    mixedMoment B raw9100 raw9100Labels = mixedMoment B raw9100step0 raw9100step0Labels := by
      have hz : ∀ j, raw9100 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9100step0 = (fun i j => raw9100 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9100step0 raw9100; decide +kernel
      have hl : raw9100step0Labels = raw9100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9100 raw9100Labels permutation265 hz
    mixedMoment B raw9100step0 raw9100step0Labels = mixedMoment B raw9100step1 raw9100step1Labels := by
      have ha : raw9100step1 = (fun i j => raw9100step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9100step1 raw9100step0; decide +kernel
      have hl : raw9100step1Labels = raw9100step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9100step0 raw9100step0Labels permutation38 permutation2
    _ = mixedMoment B node5193 node5193Labels := by rfl

def raw9101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9101step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw9101step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9101step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw9101step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9101 raw9101Labels = mixedMoment B node4583 node4583Labels := by
  calc
    mixedMoment B raw9101 raw9101Labels = mixedMoment B raw9101step0 raw9101step0Labels := by
      have hz : ∀ j, raw9101 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9101step0 = (fun i j => raw9101 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9101step0 raw9101; decide +kernel
      have hl : raw9101step0Labels = raw9101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9101 raw9101Labels permutation265 hz
    mixedMoment B raw9101step0 raw9101step0Labels = mixedMoment B raw9101step1 raw9101step1Labels := by
      have ha : raw9101step1 = (fun i j => raw9101step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9101step1 raw9101step0; decide +kernel
      have hl : raw9101step1Labels = raw9101step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9101step0 raw9101step0Labels permutation32 permutation3
    mixedMoment B raw9101step1 raw9101step1Labels = mixedMoment B raw9101step2 raw9101step2Labels := by
      have ha : raw9101step2 = raw9101step1 := by apply Matrix.ext; unfold raw9101step2 raw9101step1; decide +kernel
      have hl : raw9101step1Labels = labelEmbedding6 ∘ raw9101step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9101step1 raw9101step1Labels raw9101step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4583 node4583Labels := by rfl

def raw9102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw9102step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9102step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9102step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9102step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9102step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9102 raw9102Labels = mixedMoment B node4729 node4729Labels := by
  calc
    mixedMoment B raw9102 raw9102Labels = mixedMoment B raw9102step0 raw9102step0Labels := by
      have ha : raw9102step0 = (fun i j => raw9102 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9102step0 raw9102; decide +kernel
      have hl : raw9102step0Labels = raw9102Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9102 raw9102Labels permutation682 permutation3
    mixedMoment B raw9102step0 raw9102step0Labels = mixedMoment B raw9102step1 raw9102step1Labels := by
      have ha : raw9102step1 = -raw9102step0 := by apply Matrix.ext; change ∀ i j, raw9102step1 i j = -(raw9102step0 i j); unfold raw9102step1 raw9102step0; decide +kernel
      have hl : raw9102step1Labels = raw9102step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9102step1 raw9102step1Labels = mixedMoment B raw9102step2 raw9102step2Labels := by
      have ha : raw9102step2 = raw9102step1 := by apply Matrix.ext; unfold raw9102step2 raw9102step1; decide +kernel
      have hl : raw9102step1Labels = labelEmbedding6 ∘ raw9102step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9102step1 raw9102step1Labels raw9102step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4729 node4729Labels := by rfl

def raw9103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9103step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw9103step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw9103step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9103step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw9103step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9103 raw9103Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw9103 raw9103Labels = mixedMoment B raw9103step0 raw9103step0Labels := by
      have hz : ∀ j, raw9103 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9103step0 = (fun i j => raw9103 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9103step0 raw9103; decide +kernel
      have hl : raw9103step0Labels = raw9103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9103 raw9103Labels permutation265 hz
    mixedMoment B raw9103step0 raw9103step0Labels = mixedMoment B raw9103step1 raw9103step1Labels := by
      have ha : raw9103step1 = (fun i j => raw9103step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9103step1 raw9103step0; decide +kernel
      have hl : raw9103step1Labels = raw9103step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9103step0 raw9103step0Labels permutation151 permutation3
    mixedMoment B raw9103step1 raw9103step1Labels = mixedMoment B raw9103step2 raw9103step2Labels := by
      have ha : raw9103step2 = -raw9103step1 := by apply Matrix.ext; change ∀ i j, raw9103step2 i j = -(raw9103step1 i j); unfold raw9103step2 raw9103step1; decide +kernel
      have hl : raw9103step2Labels = raw9103step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9103step2 raw9103step2Labels = mixedMoment B raw9103step3 raw9103step3Labels := by
      have ha : raw9103step3 = raw9103step2 := by apply Matrix.ext; unfold raw9103step3 raw9103step2; decide +kernel
      have hl : raw9103step2Labels = labelEmbedding6 ∘ raw9103step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9103step2 raw9103step2Labels raw9103step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

def raw9104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9104step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw9104step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9104step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw9104step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9104step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw9104step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9104 raw9104Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw9104 raw9104Labels = mixedMoment B raw9104step0 raw9104step0Labels := by
      have hz : ∀ j, raw9104 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9104step0 = (fun i j => raw9104 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9104step0 raw9104; decide +kernel
      have hl : raw9104step0Labels = raw9104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9104 raw9104Labels permutation265 hz
    mixedMoment B raw9104step0 raw9104step0Labels = mixedMoment B raw9104step1 raw9104step1Labels := by
      have ha : raw9104step1 = (fun i j => raw9104step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9104step1 raw9104step0; decide +kernel
      have hl : raw9104step1Labels = raw9104step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9104step0 raw9104step0Labels permutation149 permutation3
    mixedMoment B raw9104step1 raw9104step1Labels = mixedMoment B raw9104step2 raw9104step2Labels := by
      have ha : raw9104step2 = -raw9104step1 := by apply Matrix.ext; change ∀ i j, raw9104step2 i j = -(raw9104step1 i j); unfold raw9104step2 raw9104step1; decide +kernel
      have hl : raw9104step2Labels = raw9104step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9104step2 raw9104step2Labels = mixedMoment B raw9104step3 raw9104step3Labels := by
      have ha : raw9104step3 = raw9104step2 := by apply Matrix.ext; unfold raw9104step3 raw9104step2; decide +kernel
      have hl : raw9104step2Labels = labelEmbedding6 ∘ raw9104step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9104step2 raw9104step2Labels raw9104step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

def raw9105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw9105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw9105step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw9105step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw9105step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9105step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw9105step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9105step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw9105step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9105 raw9105Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw9105 raw9105Labels = mixedMoment B raw9105step0 raw9105step0Labels := by
      have hz : ∀ j, raw9105 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9105step0 = (fun i j => raw9105 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9105step0 raw9105; decide +kernel
      have hl : raw9105step0Labels = raw9105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9105 raw9105Labels permutation520 hz
    mixedMoment B raw9105step0 raw9105step0Labels = mixedMoment B raw9105step1 raw9105step1Labels := by
      have hz : ∀ j, raw9105step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9105step1 = (fun i j => raw9105step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9105step1 raw9105step0; decide +kernel
      have hl : raw9105step1Labels = raw9105step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9105step0 raw9105step0Labels permutation56 hz
    mixedMoment B raw9105step1 raw9105step1Labels = mixedMoment B raw9105step2 raw9105step2Labels := by
      have ha : raw9105step2 = (fun i j => raw9105step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9105step2 raw9105step1; decide +kernel
      have hl : raw9105step2Labels = raw9105step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9105step1 raw9105step1Labels permutation29 permutation3
    mixedMoment B raw9105step2 raw9105step2Labels = mixedMoment B raw9105step3 raw9105step3Labels := by
      have ha : raw9105step3 = -raw9105step2 := by apply Matrix.ext; change ∀ i j, raw9105step3 i j = -(raw9105step2 i j); unfold raw9105step3 raw9105step2; decide +kernel
      have hl : raw9105step3Labels = raw9105step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9105step3 raw9105step3Labels = mixedMoment B raw9105step4 raw9105step4Labels := by
      have ha : raw9105step4 = raw9105step3 := by apply Matrix.ext; unfold raw9105step4 raw9105step3; decide +kernel
      have hl : raw9105step3Labels = labelEmbedding6 ∘ raw9105step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9105step3 raw9105step3Labels raw9105step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw9106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw9106Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw9106step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9106step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9106 raw9106Labels = mixedMoment B node4039 node4039Labels := by
  calc
    mixedMoment B raw9106 raw9106Labels = mixedMoment B raw9106step0 raw9106step0Labels := by
      have hz : ∀ j, raw9106 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9106step0 = (fun i j => raw9106 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9106step0 raw9106; decide +kernel
      have hl : raw9106step0Labels = raw9106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9106 raw9106Labels permutation265 hz
    mixedMoment B raw9106step0 raw9106step0Labels = mixedMoment B raw9106step1 raw9106step1Labels := by
      have ha : raw9106step1 = (fun i j => raw9106step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9106step1 raw9106step0; decide +kernel
      have hl : raw9106step1Labels = raw9106step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9106step0 raw9106step0Labels permutation32 permutation3
    _ = mixedMoment B node4039 node4039Labels := by rfl

def raw9107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9107Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9107step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9107 raw9107Labels = mixedMoment B node1200 node1200Labels := by
  calc
    mixedMoment B raw9107 raw9107Labels = mixedMoment B raw9107step0 raw9107step0Labels := by
      have ha : raw9107step0 = (fun i j => raw9107 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9107step0 raw9107; decide +kernel
      have hl : raw9107step0Labels = raw9107Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9107 raw9107Labels permutation182 permutation3
    _ = mixedMoment B node1200 node1200Labels := by rfl

def raw9108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9108Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9108step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9108 raw9108Labels = mixedMoment B node2853 node2853Labels := by
  calc
    mixedMoment B raw9108 raw9108Labels = mixedMoment B raw9108step0 raw9108step0Labels := by
      have ha : raw9108step0 = (fun i j => raw9108 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9108step0 raw9108; decide +kernel
      have hl : raw9108step0Labels = raw9108Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9108 raw9108Labels permutation182 permutation3
    _ = mixedMoment B node2853 node2853Labels := by rfl

def raw9109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9109Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9109step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw9109step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9109 raw9109Labels = mixedMoment B node2853 node2853Labels := by
  calc
    mixedMoment B raw9109 raw9109Labels = mixedMoment B raw9109step0 raw9109step0Labels := by
      have ha : raw9109step0 = (fun i j => raw9109 (permutation206 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9109step0 raw9109; decide +kernel
      have hl : raw9109step0Labels = raw9109Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9109 raw9109Labels permutation206 permutation3
    _ = mixedMoment B node2853 node2853Labels := by rfl

def raw9110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw9110Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw9110step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9110 raw9110Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw9110 raw9110Labels = mixedMoment B raw9110step0 raw9110step0Labels := by
      have hz : ∀ j, raw9110 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9110step0 = (fun i j => raw9110 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9110step0 raw9110; decide +kernel
      have hl : raw9110step0Labels = raw9110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9110 raw9110Labels permutation520 hz
    mixedMoment B raw9110step0 raw9110step0Labels = mixedMoment B raw9110step1 raw9110step1Labels := by
      have ha : raw9110step1 = (fun i j => raw9110step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9110step1 raw9110step0; decide +kernel
      have hl : raw9110step1Labels = raw9110step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9110step0 raw9110step0Labels permutation40 permutation3
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw9111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9111Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9111step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9111step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9111 raw9111Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw9111 raw9111Labels = mixedMoment B raw9111step0 raw9111step0Labels := by
      have hz : ∀ j, raw9111 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9111step0 = (fun i j => raw9111 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9111step0 raw9111; decide +kernel
      have hl : raw9111step0Labels = raw9111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9111 raw9111Labels permutation265 hz
    mixedMoment B raw9111step0 raw9111step0Labels = mixedMoment B raw9111step1 raw9111step1Labels := by
      have ha : raw9111step1 = (fun i j => raw9111step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9111step1 raw9111step0; decide +kernel
      have hl : raw9111step1Labels = raw9111step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9111step0 raw9111step0Labels permutation38 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw9112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9112Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9112step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9112 raw9112Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw9112 raw9112Labels = mixedMoment B raw9112step0 raw9112step0Labels := by
      have ha : raw9112step0 = (fun i j => raw9112 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9112step0 raw9112; decide +kernel
      have hl : raw9112step0Labels = raw9112Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9112 raw9112Labels permutation158 permutation3
    _ = mixedMoment B node2924 node2924Labels := by rfl

def raw9113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9113Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9113step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9113step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9113 raw9113Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw9113 raw9113Labels = mixedMoment B raw9113step0 raw9113step0Labels := by
      have hz : ∀ j, raw9113 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9113step0 = (fun i j => raw9113 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9113step0 raw9113; decide +kernel
      have hl : raw9113step0Labels = raw9113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9113 raw9113Labels permutation265 hz
    mixedMoment B raw9113step0 raw9113step0Labels = mixedMoment B raw9113step1 raw9113step1Labels := by
      have ha : raw9113step1 = (fun i j => raw9113step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9113step1 raw9113step0; decide +kernel
      have hl : raw9113step1Labels = raw9113step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9113step0 raw9113step0Labels permutation38 permutation3
    _ = mixedMoment B node2881 node2881Labels := by rfl

def raw9114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw9114Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw9114step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw9114step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9114step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9114step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9114 raw9114Labels = mixedMoment B node3101 node3101Labels := by
  calc
    mixedMoment B raw9114 raw9114Labels = mixedMoment B raw9114step0 raw9114step0Labels := by
      have hz : ∀ j, raw9114 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9114step0 = (fun i j => raw9114 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9114step0 raw9114; decide +kernel
      have hl : raw9114step0Labels = raw9114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9114 raw9114Labels permutation520 hz
    mixedMoment B raw9114step0 raw9114step0Labels = mixedMoment B raw9114step1 raw9114step1Labels := by
      have hz : ∀ j, raw9114step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9114step1 = (fun i j => raw9114step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9114step1 raw9114step0; decide +kernel
      have hl : raw9114step1Labels = raw9114step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9114step0 raw9114step0Labels permutation56 hz
    mixedMoment B raw9114step1 raw9114step1Labels = mixedMoment B raw9114step2 raw9114step2Labels := by
      have ha : raw9114step2 = (fun i j => raw9114step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9114step2 raw9114step1; decide +kernel
      have hl : raw9114step2Labels = raw9114step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9114step1 raw9114step1Labels permutation10 permutation3
    _ = mixedMoment B node3101 node3101Labels := by rfl

def raw9115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9115Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9115step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9115 raw9115Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw9115 raw9115Labels = mixedMoment B raw9115step0 raw9115step0Labels := by
      have hz : ∀ j, raw9115 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9115step0 = (fun i j => raw9115 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9115step0 raw9115; decide +kernel
      have hl : raw9115step0Labels = raw9115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9115 raw9115Labels permutation265 hz
    mixedMoment B raw9115step0 raw9115step0Labels = mixedMoment B raw9115step1 raw9115step1Labels := by
      have ha : raw9115step1 = (fun i j => raw9115step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9115step1 raw9115step0; decide +kernel
      have hl : raw9115step1Labels = raw9115step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9115step0 raw9115step0Labels permutation32 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw9116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9116Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9116step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9116step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9116 raw9116Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw9116 raw9116Labels = mixedMoment B raw9116step0 raw9116step0Labels := by
      have ha : raw9116step0 = (fun i j => raw9116 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9116step0 raw9116; decide +kernel
      have hl : raw9116step0Labels = raw9116Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9116 raw9116Labels permutation152 permutation3
    _ = mixedMoment B node2924 node2924Labels := by rfl

def raw9117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9117Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9117step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw9117step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9117 raw9117Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw9117 raw9117Labels = mixedMoment B raw9117step0 raw9117step0Labels := by
      have hz : ∀ j, raw9117 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9117step0 = (fun i j => raw9117 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9117step0 raw9117; decide +kernel
      have hl : raw9117step0Labels = raw9117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9117 raw9117Labels permutation265 hz
    mixedMoment B raw9117step0 raw9117step0Labels = mixedMoment B raw9117step1 raw9117step1Labels := by
      have ha : raw9117step1 = (fun i j => raw9117step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9117step1 raw9117step0; decide +kernel
      have hl : raw9117step1Labels = raw9117step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9117step0 raw9117step0Labels permutation32 permutation3
    _ = mixedMoment B node2881 node2881Labels := by rfl

def raw9118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw9118Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9118step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9118step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9118step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9118step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9118step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9118 raw9118Labels = mixedMoment B node3101 node3101Labels := by
  calc
    mixedMoment B raw9118 raw9118Labels = mixedMoment B raw9118step0 raw9118step0Labels := by
      have hz : ∀ j, raw9118 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9118step0 = (fun i j => raw9118 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9118step0 raw9118; decide +kernel
      have hl : raw9118step0Labels = raw9118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9118 raw9118Labels permutation520 hz
    mixedMoment B raw9118step0 raw9118step0Labels = mixedMoment B raw9118step1 raw9118step1Labels := by
      have hz : ∀ j, raw9118step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9118step1 = (fun i j => raw9118step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9118step1 raw9118step0; decide +kernel
      have hl : raw9118step1Labels = raw9118step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9118step0 raw9118step0Labels permutation56 hz
    mixedMoment B raw9118step1 raw9118step1Labels = mixedMoment B raw9118step2 raw9118step2Labels := by
      have ha : raw9118step2 = (fun i j => raw9118step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9118step2 raw9118step1; decide +kernel
      have hl : raw9118step2Labels = raw9118step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9118step1 raw9118step1Labels permutation8 permutation3
    _ = mixedMoment B node3101 node3101Labels := by rfl

def raw9119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9119Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9119step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw9119step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9119 raw9119Labels = mixedMoment B node1205 node1205Labels := by
  calc
    mixedMoment B raw9119 raw9119Labels = mixedMoment B raw9119step0 raw9119step0Labels := by
      have hz : ∀ j, raw9119 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9119step0 = (fun i j => raw9119 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9119step0 raw9119; decide +kernel
      have hl : raw9119step0Labels = raw9119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9119 raw9119Labels permutation265 hz
    mixedMoment B raw9119step0 raw9119step0Labels = mixedMoment B raw9119step1 raw9119step1Labels := by
      have ha : raw9119step1 = (fun i j => raw9119step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9119step1 raw9119step0; decide +kernel
      have hl : raw9119step1Labels = raw9119step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9119step0 raw9119step0Labels permutation32 permutation3
    _ = mixedMoment B node1205 node1205Labels := by rfl

def raw9120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9120Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw9120step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9120 raw9120Labels = mixedMoment B node2913 node2913Labels := by
  calc
    mixedMoment B raw9120 raw9120Labels = mixedMoment B raw9120step0 raw9120step0Labels := by
      have ha : raw9120step0 = (fun i j => raw9120 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9120step0 raw9120; decide +kernel
      have hl : raw9120step0Labels = raw9120Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9120 raw9120Labels permutation152 permutation3
    _ = mixedMoment B node2913 node2913Labels := by rfl

def raw9121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9121Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9121step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw9121step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9121 raw9121Labels = mixedMoment B node2856 node2856Labels := by
  calc
    mixedMoment B raw9121 raw9121Labels = mixedMoment B raw9121step0 raw9121step0Labels := by
      have hz : ∀ j, raw9121 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9121step0 = (fun i j => raw9121 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9121step0 raw9121; decide +kernel
      have hl : raw9121step0Labels = raw9121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9121 raw9121Labels permutation265 hz
    mixedMoment B raw9121step0 raw9121step0Labels = mixedMoment B raw9121step1 raw9121step1Labels := by
      have ha : raw9121step1 = (fun i j => raw9121step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9121step1 raw9121step0; decide +kernel
      have hl : raw9121step1Labels = raw9121step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9121step0 raw9121step0Labels permutation32 permutation3
    _ = mixedMoment B node2856 node2856Labels := by rfl

def raw9122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9122Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -2, 0]]
def raw9122step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw9122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9122 raw9122Labels = mixedMoment B node2856 node2856Labels := by
  calc
    mixedMoment B raw9122 raw9122Labels = mixedMoment B raw9122step0 raw9122step0Labels := by
      have hz : ∀ j, raw9122 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9122step0 = (fun i j => raw9122 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9122step0 raw9122; decide +kernel
      have hl : raw9122step0Labels = raw9122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9122 raw9122Labels permutation265 hz
    mixedMoment B raw9122step0 raw9122step0Labels = mixedMoment B raw9122step1 raw9122step1Labels := by
      have ha : raw9122step1 = (fun i j => raw9122step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9122step1 raw9122step0; decide +kernel
      have hl : raw9122step1Labels = raw9122step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9122step0 raw9122step0Labels permutation38 permutation3
    _ = mixedMoment B node2856 node2856Labels := by rfl

def raw9123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9123Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9123step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw9123step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9123 raw9123Labels = mixedMoment B node1202 node1202Labels := by
  calc
    mixedMoment B raw9123 raw9123Labels = mixedMoment B raw9123step0 raw9123step0Labels := by
      have hz : ∀ j, raw9123 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9123step0 = (fun i j => raw9123 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9123step0 raw9123; decide +kernel
      have hl : raw9123step0Labels = raw9123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9123 raw9123Labels permutation265 hz
    mixedMoment B raw9123step0 raw9123step0Labels = mixedMoment B raw9123step1 raw9123step1Labels := by
      have ha : raw9123step1 = (fun i j => raw9123step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9123step1 raw9123step0; decide +kernel
      have hl : raw9123step1Labels = raw9123step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9123step0 raw9123step0Labels permutation32 permutation3
    _ = mixedMoment B node1202 node1202Labels := by rfl

def raw9124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9124Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw9124step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9124step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9124 raw9124Labels = mixedMoment B node1898 node1898Labels := by
  calc
    mixedMoment B raw9124 raw9124Labels = mixedMoment B raw9124step0 raw9124step0Labels := by
      have ha : raw9124step0 = (fun i j => raw9124 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9124step0 raw9124; decide +kernel
      have hl : raw9124step0Labels = raw9124Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9124 raw9124Labels permutation682 permutation3
    mixedMoment B raw9124step0 raw9124step0Labels = mixedMoment B raw9124step1 raw9124step1Labels := by
      have ha : raw9124step1 = -raw9124step0 := by apply Matrix.ext; change ∀ i j, raw9124step1 i j = -(raw9124step0 i j); unfold raw9124step1 raw9124step0; decide +kernel
      have hl : raw9124step1Labels = raw9124step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1898 node1898Labels := by rfl

def raw9125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9125Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9125step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw9125step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9125step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw9125step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9125 raw9125Labels = mixedMoment B node1915 node1915Labels := by
  calc
    mixedMoment B raw9125 raw9125Labels = mixedMoment B raw9125step0 raw9125step0Labels := by
      have hz : ∀ j, raw9125 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9125step0 = (fun i j => raw9125 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9125step0 raw9125; decide +kernel
      have hl : raw9125step0Labels = raw9125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9125 raw9125Labels permutation265 hz
    mixedMoment B raw9125step0 raw9125step0Labels = mixedMoment B raw9125step1 raw9125step1Labels := by
      have ha : raw9125step1 = (fun i j => raw9125step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9125step1 raw9125step0; decide +kernel
      have hl : raw9125step1Labels = raw9125step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9125step0 raw9125step0Labels permutation151 permutation3
    mixedMoment B raw9125step1 raw9125step1Labels = mixedMoment B raw9125step2 raw9125step2Labels := by
      have ha : raw9125step2 = -raw9125step1 := by apply Matrix.ext; change ∀ i j, raw9125step2 i j = -(raw9125step1 i j); unfold raw9125step2 raw9125step1; decide +kernel
      have hl : raw9125step2Labels = raw9125step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1915 node1915Labels := by rfl

def raw9126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9126Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -3, 0]]
def raw9126step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw9126step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw9126step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9126 raw9126Labels = mixedMoment B node1915 node1915Labels := by
  calc
    mixedMoment B raw9126 raw9126Labels = mixedMoment B raw9126step0 raw9126step0Labels := by
      have hz : ∀ j, raw9126 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9126step0 = (fun i j => raw9126 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9126step0 raw9126; decide +kernel
      have hl : raw9126step0Labels = raw9126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9126 raw9126Labels permutation265 hz
    mixedMoment B raw9126step0 raw9126step0Labels = mixedMoment B raw9126step1 raw9126step1Labels := by
      have ha : raw9126step1 = (fun i j => raw9126step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9126step1 raw9126step0; decide +kernel
      have hl : raw9126step1Labels = raw9126step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9126step0 raw9126step0Labels permutation149 permutation3
    mixedMoment B raw9126step1 raw9126step1Labels = mixedMoment B raw9126step2 raw9126step2Labels := by
      have ha : raw9126step2 = -raw9126step1 := by apply Matrix.ext; change ∀ i j, raw9126step2 i j = -(raw9126step1 i j); unfold raw9126step2 raw9126step1; decide +kernel
      have hl : raw9126step2Labels = raw9126step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1915 node1915Labels := by rfl

def raw9127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw9127Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw9127step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9127step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw9127step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9127step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw9127step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw9127step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw9127step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9127 raw9127Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw9127 raw9127Labels = mixedMoment B raw9127step0 raw9127step0Labels := by
      have hz : ∀ j, raw9127 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9127step0 = (fun i j => raw9127 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9127step0 raw9127; decide +kernel
      have hl : raw9127step0Labels = raw9127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9127 raw9127Labels permutation520 hz
    mixedMoment B raw9127step0 raw9127step0Labels = mixedMoment B raw9127step1 raw9127step1Labels := by
      have hz : ∀ j, raw9127step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw9127step1 = (fun i j => raw9127step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw9127step1 raw9127step0; decide +kernel
      have hl : raw9127step1Labels = raw9127step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9127step0 raw9127step0Labels permutation56 hz
    mixedMoment B raw9127step1 raw9127step1Labels = mixedMoment B raw9127step2 raw9127step2Labels := by
      have ha : raw9127step2 = (fun i j => raw9127step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9127step2 raw9127step1; decide +kernel
      have hl : raw9127step2Labels = raw9127step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9127step1 raw9127step1Labels permutation29 permutation3
    mixedMoment B raw9127step2 raw9127step2Labels = mixedMoment B raw9127step3 raw9127step3Labels := by
      have ha : raw9127step3 = -raw9127step2 := by apply Matrix.ext; change ∀ i j, raw9127step3 i j = -(raw9127step2 i j); unfold raw9127step3 raw9127step2; decide +kernel
      have hl : raw9127step3Labels = raw9127step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2247 node2247Labels := by rfl

def raw9128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9128step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9128step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9128step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9128 raw9128Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw9128 raw9128Labels = mixedMoment B raw9128step0 raw9128step0Labels := by
      have ha : raw9128step0 = (fun i j => raw9128 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9128step0 raw9128; decide +kernel
      have hl : raw9128step0Labels = raw9128Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9128 raw9128Labels permutation682 permutation2
    mixedMoment B raw9128step0 raw9128step0Labels = mixedMoment B raw9128step1 raw9128step1Labels := by
      have ha : raw9128step1 = -raw9128step0 := by apply Matrix.ext; change ∀ i j, raw9128step1 i j = -(raw9128step0 i j); unfold raw9128step1 raw9128step0; decide +kernel
      have hl : raw9128step1Labels = raw9128step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw9129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9129step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw9129step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9129step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9129step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9129 raw9129Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw9129 raw9129Labels = mixedMoment B raw9129step0 raw9129step0Labels := by
      have hz : ∀ j, raw9129 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9129step0 = (fun i j => raw9129 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9129step0 raw9129; decide +kernel
      have hl : raw9129step0Labels = raw9129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9129 raw9129Labels permutation265 hz
    mixedMoment B raw9129step0 raw9129step0Labels = mixedMoment B raw9129step1 raw9129step1Labels := by
      have ha : raw9129step1 = (fun i j => raw9129step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9129step1 raw9129step0; decide +kernel
      have hl : raw9129step1Labels = raw9129step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9129step0 raw9129step0Labels permutation151 permutation2
    mixedMoment B raw9129step1 raw9129step1Labels = mixedMoment B raw9129step2 raw9129step2Labels := by
      have ha : raw9129step2 = -raw9129step1 := by apply Matrix.ext; change ∀ i j, raw9129step2 i j = -(raw9129step1 i j); unfold raw9129step2 raw9129step1; decide +kernel
      have hl : raw9129step2Labels = raw9129step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw9130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9130step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw9130step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw9130step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9130 raw9130Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw9130 raw9130Labels = mixedMoment B raw9130step0 raw9130step0Labels := by
      have hz : ∀ j, raw9130 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9130step0 = (fun i j => raw9130 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9130step0 raw9130; decide +kernel
      have hl : raw9130step0Labels = raw9130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9130 raw9130Labels permutation265 hz
    mixedMoment B raw9130step0 raw9130step0Labels = mixedMoment B raw9130step1 raw9130step1Labels := by
      have ha : raw9130step1 = (fun i j => raw9130step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9130step1 raw9130step0; decide +kernel
      have hl : raw9130step1Labels = raw9130step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9130step0 raw9130step0Labels permutation149 permutation2
    mixedMoment B raw9130step1 raw9130step1Labels = mixedMoment B raw9130step2 raw9130step2Labels := by
      have ha : raw9130step2 = -raw9130step1 := by apply Matrix.ext; change ∀ i j, raw9130step2 i j = -(raw9130step1 i j); unfold raw9130step2 raw9130step1; decide +kernel
      have hl : raw9130step2Labels = raw9130step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw9131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9131step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9131step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9131step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9131step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9131 raw9131Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw9131 raw9131Labels = mixedMoment B raw9131step0 raw9131step0Labels := by
      have hz : ∀ j, raw9131 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9131step0 = (fun i j => raw9131 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9131step0 raw9131; decide +kernel
      have hl : raw9131step0Labels = raw9131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9131 raw9131Labels permutation265 hz
    mixedMoment B raw9131step0 raw9131step0Labels = mixedMoment B raw9131step1 raw9131step1Labels := by
      have ha : raw9131step1 = (fun i j => raw9131step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9131step1 raw9131step0; decide +kernel
      have hl : raw9131step1Labels = raw9131step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9131step0 raw9131step0Labels permutation149 permutation7
    mixedMoment B raw9131step1 raw9131step1Labels = mixedMoment B raw9131step2 raw9131step2Labels := by
      have ha : raw9131step2 = raw9131step1 := by apply Matrix.ext; unfold raw9131step2 raw9131step1; decide +kernel
      have hl : raw9131step1Labels = labelEmbedding10 ∘ raw9131step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9131step1 raw9131step1Labels raw9131step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw9132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9132step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9132step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw9132step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9132step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9132 raw9132Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw9132 raw9132Labels = mixedMoment B raw9132step0 raw9132step0Labels := by
      have hz : ∀ j, raw9132 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9132step0 = (fun i j => raw9132 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9132step0 raw9132; decide +kernel
      have hl : raw9132step0Labels = raw9132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9132 raw9132Labels permutation265 hz
    mixedMoment B raw9132step0 raw9132step0Labels = mixedMoment B raw9132step1 raw9132step1Labels := by
      have ha : raw9132step1 = (fun i j => raw9132step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9132step1 raw9132step0; decide +kernel
      have hl : raw9132step1Labels = raw9132step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9132step0 raw9132step0Labels permutation149 permutation7
    mixedMoment B raw9132step1 raw9132step1Labels = mixedMoment B raw9132step2 raw9132step2Labels := by
      have ha : raw9132step2 = raw9132step1 := by apply Matrix.ext; unfold raw9132step2 raw9132step1; decide +kernel
      have hl : raw9132step1Labels = labelEmbedding10 ∘ raw9132step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9132step1 raw9132step1Labels raw9132step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw9133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9133step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9133step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9133step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9133 raw9133Labels = mixedMoment B node4439 node4439Labels := by
  calc
    mixedMoment B raw9133 raw9133Labels = mixedMoment B raw9133step0 raw9133step0Labels := by
      have ha : raw9133step0 = (fun i j => raw9133 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9133step0 raw9133; decide +kernel
      have hl : raw9133step0Labels = raw9133Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9133 raw9133Labels permutation184 permutation3
    mixedMoment B raw9133step0 raw9133step0Labels = mixedMoment B raw9133step1 raw9133step1Labels := by
      have ha : raw9133step1 = raw9133step0 := by apply Matrix.ext; unfold raw9133step1 raw9133step0; decide +kernel
      have hl : raw9133step0Labels = labelEmbedding6 ∘ raw9133step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9133step0 raw9133step0Labels raw9133step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4439 node4439Labels := by rfl

def raw9134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9134step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9134step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9134step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9134 raw9134Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw9134 raw9134Labels = mixedMoment B raw9134step0 raw9134step0Labels := by
      have ha : raw9134step0 = (fun i j => raw9134 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9134step0 raw9134; decide +kernel
      have hl : raw9134step0Labels = raw9134Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9134 raw9134Labels permutation184 permutation3
    mixedMoment B raw9134step0 raw9134step0Labels = mixedMoment B raw9134step1 raw9134step1Labels := by
      have ha : raw9134step1 = raw9134step0 := by apply Matrix.ext; unfold raw9134step1 raw9134step0; decide +kernel
      have hl : raw9134step0Labels = labelEmbedding6 ∘ raw9134step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9134step0 raw9134step0Labels raw9134step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw9135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9135step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9135step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9135step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9135step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9135 raw9135Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw9135 raw9135Labels = mixedMoment B raw9135step0 raw9135step0Labels := by
      have ha : raw9135step0 = (fun i j => raw9135 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9135step0 raw9135; decide +kernel
      have hl : raw9135step0Labels = raw9135Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9135 raw9135Labels permutation208 permutation3
    mixedMoment B raw9135step0 raw9135step0Labels = mixedMoment B raw9135step1 raw9135step1Labels := by
      have ha : raw9135step1 = raw9135step0 := by apply Matrix.ext; unfold raw9135step1 raw9135step0; decide +kernel
      have hl : raw9135step0Labels = labelEmbedding6 ∘ raw9135step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9135step0 raw9135step0Labels raw9135step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw9136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9136step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9136step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9136 raw9136Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw9136 raw9136Labels = mixedMoment B raw9136step0 raw9136step0Labels := by
      have ha : raw9136step0 = (fun i j => raw9136 (permutation232 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9136step0 raw9136; decide +kernel
      have hl : raw9136step0Labels = raw9136Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9136 raw9136Labels permutation232 permutation3
    mixedMoment B raw9136step0 raw9136step0Labels = mixedMoment B raw9136step1 raw9136step1Labels := by
      have ha : raw9136step1 = raw9136step0 := by apply Matrix.ext; unfold raw9136step1 raw9136step0; decide +kernel
      have hl : raw9136step0Labels = labelEmbedding6 ∘ raw9136step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9136step0 raw9136step0Labels raw9136step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw9137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw9137step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9137step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw9137step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9137 raw9137Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw9137 raw9137Labels = mixedMoment B raw9137step0 raw9137step0Labels := by
      have ha : raw9137step0 = (fun i j => raw9137 (permutation187 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9137step0 raw9137; decide +kernel
      have hl : raw9137step0Labels = raw9137Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9137 raw9137Labels permutation187 permutation3
    mixedMoment B raw9137step0 raw9137step0Labels = mixedMoment B raw9137step1 raw9137step1Labels := by
      have ha : raw9137step1 = raw9137step0 := by apply Matrix.ext; unfold raw9137step1 raw9137step0; decide +kernel
      have hl : raw9137step0Labels = labelEmbedding6 ∘ raw9137step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9137step0 raw9137step0Labels raw9137step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw9138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9138step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9138step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9138step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9138 raw9138Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw9138 raw9138Labels = mixedMoment B raw9138step0 raw9138step0Labels := by
      have hz : ∀ j, raw9138 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9138step0 = (fun i j => raw9138 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9138step0 raw9138; decide +kernel
      have hl : raw9138step0Labels = raw9138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9138 raw9138Labels permutation265 hz
    mixedMoment B raw9138step0 raw9138step0Labels = mixedMoment B raw9138step1 raw9138step1Labels := by
      have ha : raw9138step1 = (fun i j => raw9138step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9138step1 raw9138step0; decide +kernel
      have hl : raw9138step1Labels = raw9138step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9138step0 raw9138step0Labels permutation40 permutation3
    mixedMoment B raw9138step1 raw9138step1Labels = mixedMoment B raw9138step2 raw9138step2Labels := by
      have ha : raw9138step2 = raw9138step1 := by apply Matrix.ext; unfold raw9138step2 raw9138step1; decide +kernel
      have hl : raw9138step1Labels = labelEmbedding6 ∘ raw9138step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9138step1 raw9138step1Labels raw9138step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4459 node4459Labels := by rfl

def raw9139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9139step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9139step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9139step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9139 raw9139Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw9139 raw9139Labels = mixedMoment B raw9139step0 raw9139step0Labels := by
      have ha : raw9139step0 = (fun i j => raw9139 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9139step0 raw9139; decide +kernel
      have hl : raw9139step0Labels = raw9139Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9139 raw9139Labels permutation160 permutation3
    mixedMoment B raw9139step0 raw9139step0Labels = mixedMoment B raw9139step1 raw9139step1Labels := by
      have ha : raw9139step1 = raw9139step0 := by apply Matrix.ext; unfold raw9139step1 raw9139step0; decide +kernel
      have hl : raw9139step0Labels = labelEmbedding6 ∘ raw9139step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9139step0 raw9139step0Labels raw9139step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5074 node5074Labels := by rfl

def raw9140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9140step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9140step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9140 raw9140Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw9140 raw9140Labels = mixedMoment B raw9140step0 raw9140step0Labels := by
      have hz : ∀ j, raw9140 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9140step0 = (fun i j => raw9140 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9140step0 raw9140; decide +kernel
      have hl : raw9140step0Labels = raw9140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9140 raw9140Labels permutation265 hz
    mixedMoment B raw9140step0 raw9140step0Labels = mixedMoment B raw9140step1 raw9140step1Labels := by
      have ha : raw9140step1 = (fun i j => raw9140step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9140step1 raw9140step0; decide +kernel
      have hl : raw9140step1Labels = raw9140step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9140step0 raw9140step0Labels permutation40 permutation3
    mixedMoment B raw9140step1 raw9140step1Labels = mixedMoment B raw9140step2 raw9140step2Labels := by
      have ha : raw9140step2 = raw9140step1 := by apply Matrix.ext; unfold raw9140step2 raw9140step1; decide +kernel
      have hl : raw9140step1Labels = labelEmbedding6 ∘ raw9140step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9140step1 raw9140step1Labels raw9140step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw9141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9141step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9141step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9141step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9141step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9141step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9141 raw9141Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw9141 raw9141Labels = mixedMoment B raw9141step0 raw9141step0Labels := by
      have hz : ∀ j, raw9141 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9141step0 = (fun i j => raw9141 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9141step0 raw9141; decide +kernel
      have hl : raw9141step0Labels = raw9141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9141 raw9141Labels permutation265 hz
    mixedMoment B raw9141step0 raw9141step0Labels = mixedMoment B raw9141step1 raw9141step1Labels := by
      have ha : raw9141step1 = (fun i j => raw9141step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9141step1 raw9141step0; decide +kernel
      have hl : raw9141step1Labels = raw9141step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9141step0 raw9141step0Labels permutation46 permutation3
    mixedMoment B raw9141step1 raw9141step1Labels = mixedMoment B raw9141step2 raw9141step2Labels := by
      have ha : raw9141step2 = raw9141step1 := by apply Matrix.ext; unfold raw9141step2 raw9141step1; decide +kernel
      have hl : raw9141step1Labels = labelEmbedding6 ∘ raw9141step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9141step1 raw9141step1Labels raw9141step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw9142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9142step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9142step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9142 raw9142Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw9142 raw9142Labels = mixedMoment B raw9142step0 raw9142step0Labels := by
      have hz : ∀ j, raw9142 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9142step0 = (fun i j => raw9142 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9142step0 raw9142; decide +kernel
      have hl : raw9142step0Labels = raw9142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9142 raw9142Labels permutation265 hz
    mixedMoment B raw9142step0 raw9142step0Labels = mixedMoment B raw9142step1 raw9142step1Labels := by
      have ha : raw9142step1 = (fun i j => raw9142step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9142step1 raw9142step0; decide +kernel
      have hl : raw9142step1Labels = raw9142step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9142step0 raw9142step0Labels permutation43 permutation3
    mixedMoment B raw9142step1 raw9142step1Labels = mixedMoment B raw9142step2 raw9142step2Labels := by
      have ha : raw9142step2 = raw9142step1 := by apply Matrix.ext; unfold raw9142step2 raw9142step1; decide +kernel
      have hl : raw9142step1Labels = labelEmbedding6 ∘ raw9142step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9142step1 raw9142step1Labels raw9142step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw9143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9143step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9143step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9143 raw9143Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw9143 raw9143Labels = mixedMoment B raw9143step0 raw9143step0Labels := by
      have hz : ∀ j, raw9143 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9143step0 = (fun i j => raw9143 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9143step0 raw9143; decide +kernel
      have hl : raw9143step0Labels = raw9143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9143 raw9143Labels permutation265 hz
    mixedMoment B raw9143step0 raw9143step0Labels = mixedMoment B raw9143step1 raw9143step1Labels := by
      have ha : raw9143step1 = (fun i j => raw9143step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9143step1 raw9143step0; decide +kernel
      have hl : raw9143step1Labels = raw9143step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9143step0 raw9143step0Labels permutation34 permutation3
    mixedMoment B raw9143step1 raw9143step1Labels = mixedMoment B raw9143step2 raw9143step2Labels := by
      have ha : raw9143step2 = raw9143step1 := by apply Matrix.ext; unfold raw9143step2 raw9143step1; decide +kernel
      have hl : raw9143step1Labels = labelEmbedding6 ∘ raw9143step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9143step1 raw9143step1Labels raw9143step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4459 node4459Labels := by rfl

def raw9144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9144step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9144step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9144step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9144 raw9144Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw9144 raw9144Labels = mixedMoment B raw9144step0 raw9144step0Labels := by
      have ha : raw9144step0 = (fun i j => raw9144 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9144step0 raw9144; decide +kernel
      have hl : raw9144step0Labels = raw9144Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9144 raw9144Labels permutation154 permutation3
    mixedMoment B raw9144step0 raw9144step0Labels = mixedMoment B raw9144step1 raw9144step1Labels := by
      have ha : raw9144step1 = raw9144step0 := by apply Matrix.ext; unfold raw9144step1 raw9144step0; decide +kernel
      have hl : raw9144step0Labels = labelEmbedding6 ∘ raw9144step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9144step0 raw9144step0Labels raw9144step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5074 node5074Labels := by rfl

def raw9145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9145step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9145step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9145step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9145 raw9145Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw9145 raw9145Labels = mixedMoment B raw9145step0 raw9145step0Labels := by
      have hz : ∀ j, raw9145 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9145step0 = (fun i j => raw9145 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9145step0 raw9145; decide +kernel
      have hl : raw9145step0Labels = raw9145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9145 raw9145Labels permutation265 hz
    mixedMoment B raw9145step0 raw9145step0Labels = mixedMoment B raw9145step1 raw9145step1Labels := by
      have ha : raw9145step1 = (fun i j => raw9145step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9145step1 raw9145step0; decide +kernel
      have hl : raw9145step1Labels = raw9145step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9145step0 raw9145step0Labels permutation34 permutation3
    mixedMoment B raw9145step1 raw9145step1Labels = mixedMoment B raw9145step2 raw9145step2Labels := by
      have ha : raw9145step2 = raw9145step1 := by apply Matrix.ext; unfold raw9145step2 raw9145step1; decide +kernel
      have hl : raw9145step1Labels = labelEmbedding6 ∘ raw9145step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9145step1 raw9145step1Labels raw9145step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw9146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9146step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9146step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9146step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9146 raw9146Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw9146 raw9146Labels = mixedMoment B raw9146step0 raw9146step0Labels := by
      have hz : ∀ j, raw9146 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9146step0 = (fun i j => raw9146 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9146step0 raw9146; decide +kernel
      have hl : raw9146step0Labels = raw9146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9146 raw9146Labels permutation265 hz
    mixedMoment B raw9146step0 raw9146step0Labels = mixedMoment B raw9146step1 raw9146step1Labels := by
      have ha : raw9146step1 = (fun i j => raw9146step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9146step1 raw9146step0; decide +kernel
      have hl : raw9146step1Labels = raw9146step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9146step0 raw9146step0Labels permutation44 permutation3
    mixedMoment B raw9146step1 raw9146step1Labels = mixedMoment B raw9146step2 raw9146step2Labels := by
      have ha : raw9146step2 = raw9146step1 := by apply Matrix.ext; unfold raw9146step2 raw9146step1; decide +kernel
      have hl : raw9146step1Labels = labelEmbedding6 ∘ raw9146step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9146step1 raw9146step1Labels raw9146step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw9147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9147step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9147step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9147 raw9147Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw9147 raw9147Labels = mixedMoment B raw9147step0 raw9147step0Labels := by
      have hz : ∀ j, raw9147 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9147step0 = (fun i j => raw9147 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9147step0 raw9147; decide +kernel
      have hl : raw9147step0Labels = raw9147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9147 raw9147Labels permutation265 hz
    mixedMoment B raw9147step0 raw9147step0Labels = mixedMoment B raw9147step1 raw9147step1Labels := by
      have ha : raw9147step1 = (fun i j => raw9147step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9147step1 raw9147step0; decide +kernel
      have hl : raw9147step1Labels = raw9147step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9147step0 raw9147step0Labels permutation37 permutation3
    mixedMoment B raw9147step1 raw9147step1Labels = mixedMoment B raw9147step2 raw9147step2Labels := by
      have ha : raw9147step2 = raw9147step1 := by apply Matrix.ext; unfold raw9147step2 raw9147step1; decide +kernel
      have hl : raw9147step1Labels = labelEmbedding6 ∘ raw9147step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9147step1 raw9147step1Labels raw9147step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw9148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9148step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9148step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9148 raw9148Labels = mixedMoment B node4444 node4444Labels := by
  calc
    mixedMoment B raw9148 raw9148Labels = mixedMoment B raw9148step0 raw9148step0Labels := by
      have hz : ∀ j, raw9148 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9148step0 = (fun i j => raw9148 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9148step0 raw9148; decide +kernel
      have hl : raw9148step0Labels = raw9148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9148 raw9148Labels permutation265 hz
    mixedMoment B raw9148step0 raw9148step0Labels = mixedMoment B raw9148step1 raw9148step1Labels := by
      have ha : raw9148step1 = (fun i j => raw9148step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9148step1 raw9148step0; decide +kernel
      have hl : raw9148step1Labels = raw9148step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9148step0 raw9148step0Labels permutation33 permutation3
    mixedMoment B raw9148step1 raw9148step1Labels = mixedMoment B raw9148step2 raw9148step2Labels := by
      have ha : raw9148step2 = raw9148step1 := by apply Matrix.ext; unfold raw9148step2 raw9148step1; decide +kernel
      have hl : raw9148step1Labels = labelEmbedding6 ∘ raw9148step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9148step1 raw9148step1Labels raw9148step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4444 node4444Labels := by rfl

def raw9149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9149step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9149step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9149step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9149 raw9149Labels = mixedMoment B node5067 node5067Labels := by
  calc
    mixedMoment B raw9149 raw9149Labels = mixedMoment B raw9149step0 raw9149step0Labels := by
      have ha : raw9149step0 = (fun i j => raw9149 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9149step0 raw9149; decide +kernel
      have hl : raw9149step0Labels = raw9149Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9149 raw9149Labels permutation153 permutation3
    mixedMoment B raw9149step0 raw9149step0Labels = mixedMoment B raw9149step1 raw9149step1Labels := by
      have ha : raw9149step1 = raw9149step0 := by apply Matrix.ext; unfold raw9149step1 raw9149step0; decide +kernel
      have hl : raw9149step0Labels = labelEmbedding6 ∘ raw9149step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9149step0 raw9149step0Labels raw9149step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5067 node5067Labels := by rfl

def raw9150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9150step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9150step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9150 raw9150Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw9150 raw9150Labels = mixedMoment B raw9150step0 raw9150step0Labels := by
      have hz : ∀ j, raw9150 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9150step0 = (fun i j => raw9150 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9150step0 raw9150; decide +kernel
      have hl : raw9150step0Labels = raw9150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9150 raw9150Labels permutation265 hz
    mixedMoment B raw9150step0 raw9150step0Labels = mixedMoment B raw9150step1 raw9150step1Labels := by
      have ha : raw9150step1 = (fun i j => raw9150step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9150step1 raw9150step0; decide +kernel
      have hl : raw9150step1Labels = raw9150step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9150step0 raw9150step0Labels permutation33 permutation3
    mixedMoment B raw9150step1 raw9150step1Labels = mixedMoment B raw9150step2 raw9150step2Labels := by
      have ha : raw9150step2 = raw9150step1 := by apply Matrix.ext; unfold raw9150step2 raw9150step1; decide +kernel
      have hl : raw9150step1Labels = labelEmbedding6 ∘ raw9150step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9150step1 raw9150step1Labels raw9150step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw9151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9151step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9151step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9151step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9151 raw9151Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw9151 raw9151Labels = mixedMoment B raw9151step0 raw9151step0Labels := by
      have hz : ∀ j, raw9151 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9151step0 = (fun i j => raw9151 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9151step0 raw9151; decide +kernel
      have hl : raw9151step0Labels = raw9151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9151 raw9151Labels permutation265 hz
    mixedMoment B raw9151step0 raw9151step0Labels = mixedMoment B raw9151step1 raw9151step1Labels := by
      have ha : raw9151step1 = (fun i j => raw9151step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9151step1 raw9151step0; decide +kernel
      have hl : raw9151step1Labels = raw9151step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9151step0 raw9151step0Labels permutation39 permutation3
    mixedMoment B raw9151step1 raw9151step1Labels = mixedMoment B raw9151step2 raw9151step2Labels := by
      have ha : raw9151step2 = raw9151step1 := by apply Matrix.ext; unfold raw9151step2 raw9151step1; decide +kernel
      have hl : raw9151step1Labels = labelEmbedding6 ∘ raw9151step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9151step1 raw9151step1Labels raw9151step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw9152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw9152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw9152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw9152step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw9152step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9152 raw9152Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw9152 raw9152Labels = mixedMoment B raw9152step0 raw9152step0Labels := by
      have hz : ∀ j, raw9152 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9152step0 = (fun i j => raw9152 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9152step0 raw9152; decide +kernel
      have hl : raw9152step0Labels = raw9152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9152 raw9152Labels permutation265 hz
    mixedMoment B raw9152step0 raw9152step0Labels = mixedMoment B raw9152step1 raw9152step1Labels := by
      have ha : raw9152step1 = (fun i j => raw9152step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9152step1 raw9152step0; decide +kernel
      have hl : raw9152step1Labels = raw9152step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9152step0 raw9152step0Labels permutation33 permutation3
    mixedMoment B raw9152step1 raw9152step1Labels = mixedMoment B raw9152step2 raw9152step2Labels := by
      have ha : raw9152step2 = raw9152step1 := by apply Matrix.ext; unfold raw9152step2 raw9152step1; decide +kernel
      have hl : raw9152step1Labels = labelEmbedding6 ∘ raw9152step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9152step1 raw9152step1Labels raw9152step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw9153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9153step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9153step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9153step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9153 raw9153Labels = mixedMoment B node4440 node4440Labels := by
  calc
    mixedMoment B raw9153 raw9153Labels = mixedMoment B raw9153step0 raw9153step0Labels := by
      have hz : ∀ j, raw9153 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9153step0 = (fun i j => raw9153 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9153step0 raw9153; decide +kernel
      have hl : raw9153step0Labels = raw9153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9153 raw9153Labels permutation265 hz
    mixedMoment B raw9153step0 raw9153step0Labels = mixedMoment B raw9153step1 raw9153step1Labels := by
      have ha : raw9153step1 = (fun i j => raw9153step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9153step1 raw9153step0; decide +kernel
      have hl : raw9153step1Labels = raw9153step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9153step0 raw9153step0Labels permutation32 permutation3
    mixedMoment B raw9153step1 raw9153step1Labels = mixedMoment B raw9153step2 raw9153step2Labels := by
      have ha : raw9153step2 = raw9153step1 := by apply Matrix.ext; unfold raw9153step2 raw9153step1; decide +kernel
      have hl : raw9153step1Labels = labelEmbedding6 ∘ raw9153step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9153step1 raw9153step1Labels raw9153step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4440 node4440Labels := by rfl

def raw9154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw9154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9154step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9154step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9154 raw9154Labels = mixedMoment B node5065 node5065Labels := by
  calc
    mixedMoment B raw9154 raw9154Labels = mixedMoment B raw9154step0 raw9154step0Labels := by
      have ha : raw9154step0 = (fun i j => raw9154 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9154step0 raw9154; decide +kernel
      have hl : raw9154step0Labels = raw9154Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9154 raw9154Labels permutation682 permutation2
    mixedMoment B raw9154step0 raw9154step0Labels = mixedMoment B raw9154step1 raw9154step1Labels := by
      have ha : raw9154step1 = -raw9154step0 := by apply Matrix.ext; change ∀ i j, raw9154step1 i j = -(raw9154step0 i j); unfold raw9154step1 raw9154step0; decide +kernel
      have hl : raw9154step1Labels = raw9154step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5065 node5065Labels := by rfl

def raw9155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw9155step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9155step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9155step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9155 raw9155Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw9155 raw9155Labels = mixedMoment B raw9155step0 raw9155step0Labels := by
      have hz : ∀ j, raw9155 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9155step0 = (fun i j => raw9155 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9155step0 raw9155; decide +kernel
      have hl : raw9155step0Labels = raw9155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9155 raw9155Labels permutation265 hz
    mixedMoment B raw9155step0 raw9155step0Labels = mixedMoment B raw9155step1 raw9155step1Labels := by
      have ha : raw9155step1 = (fun i j => raw9155step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9155step1 raw9155step0; decide +kernel
      have hl : raw9155step1Labels = raw9155step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9155step0 raw9155step0Labels permutation151 permutation2
    mixedMoment B raw9155step1 raw9155step1Labels = mixedMoment B raw9155step2 raw9155step2Labels := by
      have ha : raw9155step2 = -raw9155step1 := by apply Matrix.ext; change ∀ i j, raw9155step2 i j = -(raw9155step1 i j); unfold raw9155step2 raw9155step1; decide +kernel
      have hl : raw9155step2Labels = raw9155step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw9156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw9156step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9156step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw9156step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9156 raw9156Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw9156 raw9156Labels = mixedMoment B raw9156step0 raw9156step0Labels := by
      have hz : ∀ j, raw9156 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9156step0 = (fun i j => raw9156 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9156step0 raw9156; decide +kernel
      have hl : raw9156step0Labels = raw9156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9156 raw9156Labels permutation265 hz
    mixedMoment B raw9156step0 raw9156step0Labels = mixedMoment B raw9156step1 raw9156step1Labels := by
      have ha : raw9156step1 = (fun i j => raw9156step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9156step1 raw9156step0; decide +kernel
      have hl : raw9156step1Labels = raw9156step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9156step0 raw9156step0Labels permutation149 permutation2
    mixedMoment B raw9156step1 raw9156step1Labels = mixedMoment B raw9156step2 raw9156step2Labels := by
      have ha : raw9156step2 = -raw9156step1 := by apply Matrix.ext; change ∀ i j, raw9156step2 i j = -(raw9156step1 i j); unfold raw9156step2 raw9156step1; decide +kernel
      have hl : raw9156step2Labels = raw9156step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw9157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9157step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw9157step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9157step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw9157step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9157 raw9157Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw9157 raw9157Labels = mixedMoment B raw9157step0 raw9157step0Labels := by
      have hz : ∀ j, raw9157 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9157step0 = (fun i j => raw9157 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9157step0 raw9157; decide +kernel
      have hl : raw9157step0Labels = raw9157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9157 raw9157Labels permutation265 hz
    mixedMoment B raw9157step0 raw9157step0Labels = mixedMoment B raw9157step1 raw9157step1Labels := by
      have ha : raw9157step1 = (fun i j => raw9157step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9157step1 raw9157step0; decide +kernel
      have hl : raw9157step1Labels = raw9157step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9157step0 raw9157step0Labels permutation149 permutation2
    mixedMoment B raw9157step1 raw9157step1Labels = mixedMoment B raw9157step2 raw9157step2Labels := by
      have ha : raw9157step2 = -raw9157step1 := by apply Matrix.ext; change ∀ i j, raw9157step2 i j = -(raw9157step1 i j); unfold raw9157step2 raw9157step1; decide +kernel
      have hl : raw9157step2Labels = raw9157step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5252 node5252Labels := by rfl

def raw9158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9158Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9158step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9158step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9158 raw9158Labels = mixedMoment B node3977 node3977Labels := by
  calc
    mixedMoment B raw9158 raw9158Labels = mixedMoment B raw9158step0 raw9158step0Labels := by
      have ha : raw9158step0 = (fun i j => raw9158 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9158step0 raw9158; decide +kernel
      have hl : raw9158step0Labels = raw9158Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9158 raw9158Labels permutation152 permutation3
    _ = mixedMoment B node3977 node3977Labels := by rfl

def raw9159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9159Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9159step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9159step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9159 raw9159Labels = mixedMoment B node3996 node3996Labels := by
  calc
    mixedMoment B raw9159 raw9159Labels = mixedMoment B raw9159step0 raw9159step0Labels := by
      have hz : ∀ j, raw9159 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9159step0 = (fun i j => raw9159 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9159step0 raw9159; decide +kernel
      have hl : raw9159step0Labels = raw9159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9159 raw9159Labels permutation265 hz
    mixedMoment B raw9159step0 raw9159step0Labels = mixedMoment B raw9159step1 raw9159step1Labels := by
      have ha : raw9159step1 = (fun i j => raw9159step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9159step1 raw9159step0; decide +kernel
      have hl : raw9159step1Labels = raw9159step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9159step0 raw9159step0Labels permutation32 permutation3
    _ = mixedMoment B node3996 node3996Labels := by rfl

def raw9160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9160Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9160step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw9160step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9160 raw9160Labels = mixedMoment B node3996 node3996Labels := by
  calc
    mixedMoment B raw9160 raw9160Labels = mixedMoment B raw9160step0 raw9160step0Labels := by
      have hz : ∀ j, raw9160 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9160step0 = (fun i j => raw9160 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9160step0 raw9160; decide +kernel
      have hl : raw9160step0Labels = raw9160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9160 raw9160Labels permutation265 hz
    mixedMoment B raw9160step0 raw9160step0Labels = mixedMoment B raw9160step1 raw9160step1Labels := by
      have ha : raw9160step1 = (fun i j => raw9160step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9160step1 raw9160step0; decide +kernel
      have hl : raw9160step1Labels = raw9160step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9160step0 raw9160step0Labels permutation38 permutation3
    _ = mixedMoment B node3996 node3996Labels := by rfl

def raw9161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9161Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9161step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw9161step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9161 raw9161Labels = mixedMoment B node4012 node4012Labels := by
  calc
    mixedMoment B raw9161 raw9161Labels = mixedMoment B raw9161step0 raw9161step0Labels := by
      have hz : ∀ j, raw9161 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9161step0 = (fun i j => raw9161 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9161step0 raw9161; decide +kernel
      have hl : raw9161step0Labels = raw9161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9161 raw9161Labels permutation265 hz
    mixedMoment B raw9161step0 raw9161step0Labels = mixedMoment B raw9161step1 raw9161step1Labels := by
      have ha : raw9161step1 = (fun i j => raw9161step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9161step1 raw9161step0; decide +kernel
      have hl : raw9161step1Labels = raw9161step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9161step0 raw9161step0Labels permutation44 permutation3
    _ = mixedMoment B node4012 node4012Labels := by rfl

def raw9162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9162Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9162step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw9162step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9162 raw9162Labels = mixedMoment B node3998 node3998Labels := by
  calc
    mixedMoment B raw9162 raw9162Labels = mixedMoment B raw9162step0 raw9162step0Labels := by
      have hz : ∀ j, raw9162 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9162step0 = (fun i j => raw9162 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9162step0 raw9162; decide +kernel
      have hl : raw9162step0Labels = raw9162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9162 raw9162Labels permutation265 hz
    mixedMoment B raw9162step0 raw9162step0Labels = mixedMoment B raw9162step1 raw9162step1Labels := by
      have ha : raw9162step1 = (fun i j => raw9162step0 (permutation146 i) (permutation6 j)) := by apply Matrix.ext; unfold raw9162step1 raw9162step0; decide +kernel
      have hl : raw9162step1Labels = raw9162step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9162step0 raw9162step0Labels permutation146 permutation6
    _ = mixedMoment B node3998 node3998Labels := by rfl

def raw9163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9163Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9163step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9163 raw9163Labels = mixedMoment B node1021 node1021Labels := by
  calc
    mixedMoment B raw9163 raw9163Labels = mixedMoment B raw9163step0 raw9163step0Labels := by
      have ha : raw9163step0 = (fun i j => raw9163 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9163step0 raw9163; decide +kernel
      have hl : raw9163step0Labels = raw9163Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9163 raw9163Labels permutation184 permutation3
    _ = mixedMoment B node1021 node1021Labels := by rfl

def raw9164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9164Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9164step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9164 raw9164Labels = mixedMoment B node2570 node2570Labels := by
  calc
    mixedMoment B raw9164 raw9164Labels = mixedMoment B raw9164step0 raw9164step0Labels := by
      have ha : raw9164step0 = (fun i j => raw9164 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9164step0 raw9164; decide +kernel
      have hl : raw9164step0Labels = raw9164Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9164 raw9164Labels permutation184 permutation3
    _ = mixedMoment B node2570 node2570Labels := by rfl

def raw9165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9165step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw9165step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9165 raw9165Labels = mixedMoment B node2570 node2570Labels := by
  calc
    mixedMoment B raw9165 raw9165Labels = mixedMoment B raw9165step0 raw9165step0Labels := by
      have ha : raw9165step0 = (fun i j => raw9165 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9165step0 raw9165; decide +kernel
      have hl : raw9165step0Labels = raw9165Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9165 raw9165Labels permutation208 permutation3
    _ = mixedMoment B node2570 node2570Labels := by rfl

def raw9166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9166step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9166 raw9166Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw9166 raw9166Labels = mixedMoment B raw9166step0 raw9166step0Labels := by
      have ha : raw9166step0 = (fun i j => raw9166 (permutation232 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9166step0 raw9166; decide +kernel
      have hl : raw9166step0Labels = raw9166Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9166 raw9166Labels permutation232 permutation3
    _ = mixedMoment B node2710 node2710Labels := by rfl

def raw9167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9167step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw9167step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9167 raw9167Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw9167 raw9167Labels = mixedMoment B raw9167step0 raw9167step0Labels := by
      have ha : raw9167step0 = (fun i j => raw9167 (permutation187 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9167step0 raw9167; decide +kernel
      have hl : raw9167step0Labels = raw9167Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9167 raw9167Labels permutation187 permutation3
    _ = mixedMoment B node2750 node2750Labels := by rfl

def raw9168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9168step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9168 raw9168Labels = mixedMoment B node1042 node1042Labels := by
  calc
    mixedMoment B raw9168 raw9168Labels = mixedMoment B raw9168step0 raw9168step0Labels := by
      have hz : ∀ j, raw9168 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9168step0 = (fun i j => raw9168 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9168step0 raw9168; decide +kernel
      have hl : raw9168step0Labels = raw9168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9168 raw9168Labels permutation265 hz
    mixedMoment B raw9168step0 raw9168step0Labels = mixedMoment B raw9168step1 raw9168step1Labels := by
      have ha : raw9168step1 = (fun i j => raw9168step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9168step1 raw9168step0; decide +kernel
      have hl : raw9168step1Labels = raw9168step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9168step0 raw9168step0Labels permutation40 permutation3
    _ = mixedMoment B node1042 node1042Labels := by rfl

def raw9169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9169step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9169step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9169 raw9169Labels = mixedMoment B node2481 node2481Labels := by
  calc
    mixedMoment B raw9169 raw9169Labels = mixedMoment B raw9169step0 raw9169step0Labels := by
      have ha : raw9169step0 = (fun i j => raw9169 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9169step0 raw9169; decide +kernel
      have hl : raw9169step0Labels = raw9169Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9169 raw9169Labels permutation160 permutation3
    _ = mixedMoment B node2481 node2481Labels := by rfl

def raw9170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9170step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9170 raw9170Labels = mixedMoment B node2596 node2596Labels := by
  calc
    mixedMoment B raw9170 raw9170Labels = mixedMoment B raw9170step0 raw9170step0Labels := by
      have hz : ∀ j, raw9170 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9170step0 = (fun i j => raw9170 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9170step0 raw9170; decide +kernel
      have hl : raw9170step0Labels = raw9170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9170 raw9170Labels permutation265 hz
    mixedMoment B raw9170step0 raw9170step0Labels = mixedMoment B raw9170step1 raw9170step1Labels := by
      have ha : raw9170step1 = (fun i j => raw9170step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9170step1 raw9170step0; decide +kernel
      have hl : raw9170step1Labels = raw9170step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9170step0 raw9170step0Labels permutation40 permutation3
    _ = mixedMoment B node2596 node2596Labels := by rfl

def raw9171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9171step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9171 raw9171Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw9171 raw9171Labels = mixedMoment B raw9171step0 raw9171step0Labels := by
      have hz : ∀ j, raw9171 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9171step0 = (fun i j => raw9171 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9171step0 raw9171; decide +kernel
      have hl : raw9171step0Labels = raw9171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9171 raw9171Labels permutation265 hz
    mixedMoment B raw9171step0 raw9171step0Labels = mixedMoment B raw9171step1 raw9171step1Labels := by
      have ha : raw9171step1 = (fun i j => raw9171step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9171step1 raw9171step0; decide +kernel
      have hl : raw9171step1Labels = raw9171step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9171step0 raw9171step0Labels permutation46 permutation3
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw9172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9172step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9172 raw9172Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw9172 raw9172Labels = mixedMoment B raw9172step0 raw9172step0Labels := by
      have hz : ∀ j, raw9172 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9172step0 = (fun i j => raw9172 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9172step0 raw9172; decide +kernel
      have hl : raw9172step0Labels = raw9172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9172 raw9172Labels permutation265 hz
    mixedMoment B raw9172step0 raw9172step0Labels = mixedMoment B raw9172step1 raw9172step1Labels := by
      have ha : raw9172step1 = (fun i j => raw9172step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9172step1 raw9172step0; decide +kernel
      have hl : raw9172step1Labels = raw9172step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9172step0 raw9172step0Labels permutation43 permutation3
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw9173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9173step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9173step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9173 raw9173Labels = mixedMoment B node1042 node1042Labels := by
  calc
    mixedMoment B raw9173 raw9173Labels = mixedMoment B raw9173step0 raw9173step0Labels := by
      have hz : ∀ j, raw9173 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9173step0 = (fun i j => raw9173 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9173step0 raw9173; decide +kernel
      have hl : raw9173step0Labels = raw9173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9173 raw9173Labels permutation265 hz
    mixedMoment B raw9173step0 raw9173step0Labels = mixedMoment B raw9173step1 raw9173step1Labels := by
      have ha : raw9173step1 = (fun i j => raw9173step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9173step1 raw9173step0; decide +kernel
      have hl : raw9173step1Labels = raw9173step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9173step0 raw9173step0Labels permutation34 permutation3
    _ = mixedMoment B node1042 node1042Labels := by rfl

def raw9174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9174step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9174step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9174 raw9174Labels = mixedMoment B node2481 node2481Labels := by
  calc
    mixedMoment B raw9174 raw9174Labels = mixedMoment B raw9174step0 raw9174step0Labels := by
      have ha : raw9174step0 = (fun i j => raw9174 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9174step0 raw9174; decide +kernel
      have hl : raw9174step0Labels = raw9174Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9174 raw9174Labels permutation154 permutation3
    _ = mixedMoment B node2481 node2481Labels := by rfl

def raw9175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9175step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw9175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9175 raw9175Labels = mixedMoment B node2596 node2596Labels := by
  calc
    mixedMoment B raw9175 raw9175Labels = mixedMoment B raw9175step0 raw9175step0Labels := by
      have hz : ∀ j, raw9175 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9175step0 = (fun i j => raw9175 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9175step0 raw9175; decide +kernel
      have hl : raw9175step0Labels = raw9175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9175 raw9175Labels permutation265 hz
    mixedMoment B raw9175step0 raw9175step0Labels = mixedMoment B raw9175step1 raw9175step1Labels := by
      have ha : raw9175step1 = (fun i j => raw9175step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9175step1 raw9175step0; decide +kernel
      have hl : raw9175step1Labels = raw9175step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9175step0 raw9175step0Labels permutation34 permutation3
    _ = mixedMoment B node2596 node2596Labels := by rfl

def raw9176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9176step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9176 raw9176Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw9176 raw9176Labels = mixedMoment B raw9176step0 raw9176step0Labels := by
      have hz : ∀ j, raw9176 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9176step0 = (fun i j => raw9176 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9176step0 raw9176; decide +kernel
      have hl : raw9176step0Labels = raw9176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9176 raw9176Labels permutation265 hz
    mixedMoment B raw9176step0 raw9176step0Labels = mixedMoment B raw9176step1 raw9176step1Labels := by
      have ha : raw9176step1 = (fun i j => raw9176step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9176step1 raw9176step0; decide +kernel
      have hl : raw9176step1Labels = raw9176step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9176step0 raw9176step0Labels permutation44 permutation3
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw9177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9177step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9177step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9177 raw9177Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw9177 raw9177Labels = mixedMoment B raw9177step0 raw9177step0Labels := by
      have hz : ∀ j, raw9177 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9177step0 = (fun i j => raw9177 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9177step0 raw9177; decide +kernel
      have hl : raw9177step0Labels = raw9177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9177 raw9177Labels permutation265 hz
    mixedMoment B raw9177step0 raw9177step0Labels = mixedMoment B raw9177step1 raw9177step1Labels := by
      have ha : raw9177step1 = (fun i j => raw9177step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9177step1 raw9177step0; decide +kernel
      have hl : raw9177step1Labels = raw9177step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9177step0 raw9177step0Labels permutation37 permutation3
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw9178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9178step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9178step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9178 raw9178Labels = mixedMoment B node1026 node1026Labels := by
  calc
    mixedMoment B raw9178 raw9178Labels = mixedMoment B raw9178step0 raw9178step0Labels := by
      have hz : ∀ j, raw9178 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9178step0 = (fun i j => raw9178 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9178step0 raw9178; decide +kernel
      have hl : raw9178step0Labels = raw9178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9178 raw9178Labels permutation265 hz
    mixedMoment B raw9178step0 raw9178step0Labels = mixedMoment B raw9178step1 raw9178step1Labels := by
      have ha : raw9178step1 = (fun i j => raw9178step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9178step1 raw9178step0; decide +kernel
      have hl : raw9178step1Labels = raw9178step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9178step0 raw9178step0Labels permutation33 permutation3
    _ = mixedMoment B node1026 node1026Labels := by rfl

def raw9179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9179Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9179 raw9179Labels = mixedMoment B node2473 node2473Labels := by
  calc
    mixedMoment B raw9179 raw9179Labels = mixedMoment B raw9179step0 raw9179step0Labels := by
      have ha : raw9179step0 = (fun i j => raw9179 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9179step0 raw9179; decide +kernel
      have hl : raw9179step0Labels = raw9179Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9179 raw9179Labels permutation153 permutation3
    _ = mixedMoment B node2473 node2473Labels := by rfl

def raw9180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9180Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9180step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9180 raw9180Labels = mixedMoment B node2576 node2576Labels := by
  calc
    mixedMoment B raw9180 raw9180Labels = mixedMoment B raw9180step0 raw9180step0Labels := by
      have hz : ∀ j, raw9180 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9180step0 = (fun i j => raw9180 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9180step0 raw9180; decide +kernel
      have hl : raw9180step0Labels = raw9180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9180 raw9180Labels permutation265 hz
    mixedMoment B raw9180step0 raw9180step0Labels = mixedMoment B raw9180step1 raw9180step1Labels := by
      have ha : raw9180step1 = (fun i j => raw9180step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9180step1 raw9180step0; decide +kernel
      have hl : raw9180step1Labels = raw9180step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9180step0 raw9180step0Labels permutation33 permutation3
    _ = mixedMoment B node2576 node2576Labels := by rfl

def raw9181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9181Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9181step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw9181step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9181 raw9181Labels = mixedMoment B node2576 node2576Labels := by
  calc
    mixedMoment B raw9181 raw9181Labels = mixedMoment B raw9181step0 raw9181step0Labels := by
      have hz : ∀ j, raw9181 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9181step0 = (fun i j => raw9181 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9181step0 raw9181; decide +kernel
      have hl : raw9181step0Labels = raw9181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9181 raw9181Labels permutation265 hz
    mixedMoment B raw9181step0 raw9181step0Labels = mixedMoment B raw9181step1 raw9181step1Labels := by
      have ha : raw9181step1 = (fun i j => raw9181step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9181step1 raw9181step0; decide +kernel
      have hl : raw9181step1Labels = raw9181step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9181step0 raw9181step0Labels permutation39 permutation3
    _ = mixedMoment B node2576 node2576Labels := by rfl

def raw9182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw9182Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw9182step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw9182step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9182 raw9182Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw9182 raw9182Labels = mixedMoment B raw9182step0 raw9182step0Labels := by
      have hz : ∀ j, raw9182 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9182step0 = (fun i j => raw9182 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9182step0 raw9182; decide +kernel
      have hl : raw9182step0Labels = raw9182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9182 raw9182Labels permutation265 hz
    mixedMoment B raw9182step0 raw9182step0Labels = mixedMoment B raw9182step1 raw9182step1Labels := by
      have ha : raw9182step1 = (fun i j => raw9182step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9182step1 raw9182step0; decide +kernel
      have hl : raw9182step1Labels = raw9182step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9182step0 raw9182step0Labels permutation33 permutation3
    _ = mixedMoment B node2751 node2751Labels := by rfl

def raw9183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9183Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9183step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9183step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9183 raw9183Labels = mixedMoment B node1022 node1022Labels := by
  calc
    mixedMoment B raw9183 raw9183Labels = mixedMoment B raw9183step0 raw9183step0Labels := by
      have hz : ∀ j, raw9183 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9183step0 = (fun i j => raw9183 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9183step0 raw9183; decide +kernel
      have hl : raw9183step0Labels = raw9183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9183 raw9183Labels permutation265 hz
    mixedMoment B raw9183step0 raw9183step0Labels = mixedMoment B raw9183step1 raw9183step1Labels := by
      have ha : raw9183step1 = (fun i j => raw9183step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9183step1 raw9183step0; decide +kernel
      have hl : raw9183step1Labels = raw9183step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9183step0 raw9183step0Labels permutation32 permutation3
    _ = mixedMoment B node1022 node1022Labels := by rfl

def raw9184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9184Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9184step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9184step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9184 raw9184Labels = mixedMoment B node2470 node2470Labels := by
  calc
    mixedMoment B raw9184 raw9184Labels = mixedMoment B raw9184step0 raw9184step0Labels := by
      have ha : raw9184step0 = (fun i j => raw9184 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9184step0 raw9184; decide +kernel
      have hl : raw9184step0Labels = raw9184Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9184 raw9184Labels permutation152 permutation3
    _ = mixedMoment B node2470 node2470Labels := by rfl

def raw9185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9185Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9185step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9185step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9185 raw9185Labels = mixedMoment B node2572 node2572Labels := by
  calc
    mixedMoment B raw9185 raw9185Labels = mixedMoment B raw9185step0 raw9185step0Labels := by
      have hz : ∀ j, raw9185 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9185step0 = (fun i j => raw9185 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9185step0 raw9185; decide +kernel
      have hl : raw9185step0Labels = raw9185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9185 raw9185Labels permutation265 hz
    mixedMoment B raw9185step0 raw9185step0Labels = mixedMoment B raw9185step1 raw9185step1Labels := by
      have ha : raw9185step1 = (fun i j => raw9185step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9185step1 raw9185step0; decide +kernel
      have hl : raw9185step1Labels = raw9185step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9185step0 raw9185step0Labels permutation32 permutation3
    _ = mixedMoment B node2572 node2572Labels := by rfl

def raw9186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9186Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9186step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw9186step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9186 raw9186Labels = mixedMoment B node2572 node2572Labels := by
  calc
    mixedMoment B raw9186 raw9186Labels = mixedMoment B raw9186step0 raw9186step0Labels := by
      have hz : ∀ j, raw9186 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9186step0 = (fun i j => raw9186 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9186step0 raw9186; decide +kernel
      have hl : raw9186step0Labels = raw9186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9186 raw9186Labels permutation265 hz
    mixedMoment B raw9186step0 raw9186step0Labels = mixedMoment B raw9186step1 raw9186step1Labels := by
      have ha : raw9186step1 = (fun i j => raw9186step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9186step1 raw9186step0; decide +kernel
      have hl : raw9186step1Labels = raw9186step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9186step0 raw9186step0Labels permutation38 permutation3
    _ = mixedMoment B node2572 node2572Labels := by rfl

def raw9187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9187Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9187step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9187step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw9187step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9187 raw9187Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw9187 raw9187Labels = mixedMoment B raw9187step0 raw9187step0Labels := by
      have hz : ∀ j, raw9187 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9187step0 = (fun i j => raw9187 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9187step0 raw9187; decide +kernel
      have hl : raw9187step0Labels = raw9187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9187 raw9187Labels permutation265 hz
    mixedMoment B raw9187step0 raw9187step0Labels = mixedMoment B raw9187step1 raw9187step1Labels := by
      have ha : raw9187step1 = (fun i j => raw9187step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9187step1 raw9187step0; decide +kernel
      have hl : raw9187step1Labels = raw9187step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9187step0 raw9187step0Labels permutation44 permutation3
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw9188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9188step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9188step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9188step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9188 raw9188Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw9188 raw9188Labels = mixedMoment B raw9188step0 raw9188step0Labels := by
      have ha : raw9188step0 = (fun i j => raw9188 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9188step0 raw9188; decide +kernel
      have hl : raw9188step0Labels = raw9188Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9188 raw9188Labels permutation674 permutation7
    mixedMoment B raw9188step0 raw9188step0Labels = mixedMoment B raw9188step1 raw9188step1Labels := by
      have ha : raw9188step1 = raw9188step0 := by apply Matrix.ext; unfold raw9188step1 raw9188step0; decide +kernel
      have hl : raw9188step0Labels = labelEmbedding1 ∘ raw9188step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9188step0 raw9188step0Labels raw9188step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3805 node3805Labels := by rfl

def raw9189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9189step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9189step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9189 raw9189Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw9189 raw9189Labels = mixedMoment B raw9189step0 raw9189step0Labels := by
      have hz : ∀ j, raw9189 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9189step0 = (fun i j => raw9189 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9189step0 raw9189; decide +kernel
      have hl : raw9189step0Labels = raw9189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9189 raw9189Labels permutation265 hz
    mixedMoment B raw9189step0 raw9189step0Labels = mixedMoment B raw9189step1 raw9189step1Labels := by
      have ha : raw9189step1 = (fun i j => raw9189step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9189step1 raw9189step0; decide +kernel
      have hl : raw9189step1Labels = raw9189step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9189step0 raw9189step0Labels permutation151 permutation7
    mixedMoment B raw9189step1 raw9189step1Labels = mixedMoment B raw9189step2 raw9189step2Labels := by
      have ha : raw9189step2 = raw9189step1 := by apply Matrix.ext; unfold raw9189step2 raw9189step1; decide +kernel
      have hl : raw9189step1Labels = labelEmbedding1 ∘ raw9189step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9189step1 raw9189step1Labels raw9189step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

def raw9190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9190step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9190step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw9190step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9190 raw9190Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw9190 raw9190Labels = mixedMoment B raw9190step0 raw9190step0Labels := by
      have hz : ∀ j, raw9190 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9190step0 = (fun i j => raw9190 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9190step0 raw9190; decide +kernel
      have hl : raw9190step0Labels = raw9190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9190 raw9190Labels permutation265 hz
    mixedMoment B raw9190step0 raw9190step0Labels = mixedMoment B raw9190step1 raw9190step1Labels := by
      have ha : raw9190step1 = (fun i j => raw9190step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9190step1 raw9190step0; decide +kernel
      have hl : raw9190step1Labels = raw9190step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9190step0 raw9190step0Labels permutation149 permutation7
    mixedMoment B raw9190step1 raw9190step1Labels = mixedMoment B raw9190step2 raw9190step2Labels := by
      have ha : raw9190step2 = raw9190step1 := by apply Matrix.ext; unfold raw9190step2 raw9190step1; decide +kernel
      have hl : raw9190step1Labels = labelEmbedding1 ∘ raw9190step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9190step1 raw9190step1Labels raw9190step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

def raw9191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9191Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9191step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9191step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9191step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9191 raw9191Labels = mixedMoment B node3858 node3858Labels := by
  calc
    mixedMoment B raw9191 raw9191Labels = mixedMoment B raw9191step0 raw9191step0Labels := by
      have hz : ∀ j, raw9191 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9191step0 = (fun i j => raw9191 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9191step0 raw9191; decide +kernel
      have hl : raw9191step0Labels = raw9191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9191 raw9191Labels permutation265 hz
    mixedMoment B raw9191step0 raw9191step0Labels = mixedMoment B raw9191step1 raw9191step1Labels := by
      have ha : raw9191step1 = (fun i j => raw9191step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9191step1 raw9191step0; decide +kernel
      have hl : raw9191step1Labels = raw9191step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9191step0 raw9191step0Labels permutation149 permutation7
    mixedMoment B raw9191step1 raw9191step1Labels = mixedMoment B raw9191step2 raw9191step2Labels := by
      have ha : raw9191step2 = raw9191step1 := by apply Matrix.ext; unfold raw9191step2 raw9191step1; decide +kernel
      have hl : raw9191step1Labels = labelEmbedding1 ∘ raw9191step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9191step1 raw9191step1Labels raw9191step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3858 node3858Labels := by rfl

def raw9192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9192step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9192 raw9192Labels = mixedMoment B node3984 node3984Labels := by
  calc
    mixedMoment B raw9192 raw9192Labels = mixedMoment B raw9192step0 raw9192step0Labels := by
      have hz : ∀ j, raw9192 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9192step0 = (fun i j => raw9192 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9192step0 raw9192; decide +kernel
      have hl : raw9192step0Labels = raw9192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9192 raw9192Labels permutation265 hz
    mixedMoment B raw9192step0 raw9192step0Labels = mixedMoment B raw9192step1 raw9192step1Labels := by
      have ha : raw9192step1 = (fun i j => raw9192step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9192step1 raw9192step0; decide +kernel
      have hl : raw9192step1Labels = raw9192step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9192step0 raw9192step0Labels permutation149 permutation7
    mixedMoment B raw9192step1 raw9192step1Labels = mixedMoment B raw9192step2 raw9192step2Labels := by
      have ha : raw9192step2 = raw9192step1 := by apply Matrix.ext; unfold raw9192step2 raw9192step1; decide +kernel
      have hl : raw9192step1Labels = labelEmbedding1 ∘ raw9192step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9192step1 raw9192step1Labels raw9192step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3984 node3984Labels := by rfl

def raw9193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9193Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw9193step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9193step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9193step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9193step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9193step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9193 raw9193Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw9193 raw9193Labels = mixedMoment B raw9193step0 raw9193step0Labels := by
      have ha : raw9193step0 = (fun i j => raw9193 (permutation243 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9193step0 raw9193; decide +kernel
      have hl : raw9193step0Labels = raw9193Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9193 raw9193Labels permutation243 permutation5
    mixedMoment B raw9193step0 raw9193step0Labels = mixedMoment B raw9193step1 raw9193step1Labels := by
      have ha : raw9193step1 = -raw9193step0 := by apply Matrix.ext; change ∀ i j, raw9193step1 i j = -(raw9193step0 i j); unfold raw9193step1 raw9193step0; decide +kernel
      have hl : raw9193step1Labels = raw9193step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9193step1 raw9193step1Labels = mixedMoment B raw9193step2 raw9193step2Labels := by
      have ha : raw9193step2 = raw9193step1 := by apply Matrix.ext; unfold raw9193step2 raw9193step1; decide +kernel
      have hl : raw9193step1Labels = labelEmbedding1 ∘ raw9193step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9193step1 raw9193step1Labels raw9193step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

def raw9194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9194Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw9194step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9194step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw9194step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9194step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw9194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9194 raw9194Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw9194 raw9194Labels = mixedMoment B raw9194step0 raw9194step0Labels := by
      have ha : raw9194step0 = (fun i j => raw9194 (permutation193 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9194step0 raw9194; decide +kernel
      have hl : raw9194step0Labels = raw9194Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9194 raw9194Labels permutation193 permutation5
    mixedMoment B raw9194step0 raw9194step0Labels = mixedMoment B raw9194step1 raw9194step1Labels := by
      have ha : raw9194step1 = -raw9194step0 := by apply Matrix.ext; change ∀ i j, raw9194step1 i j = -(raw9194step0 i j); unfold raw9194step1 raw9194step0; decide +kernel
      have hl : raw9194step1Labels = raw9194step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9194step1 raw9194step1Labels = mixedMoment B raw9194step2 raw9194step2Labels := by
      have ha : raw9194step2 = raw9194step1 := by apply Matrix.ext; unfold raw9194step2 raw9194step1; decide +kernel
      have hl : raw9194step1Labels = labelEmbedding1 ∘ raw9194step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9194step1 raw9194step1Labels raw9194step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

def raw9195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9195Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9195step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw9195step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9195step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw9195step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9195step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw9195step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9195 raw9195Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw9195 raw9195Labels = mixedMoment B raw9195step0 raw9195step0Labels := by
      have ha : raw9195step0 = (fun i j => raw9195 (permutation217 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9195step0 raw9195; decide +kernel
      have hl : raw9195step0Labels = raw9195Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9195 raw9195Labels permutation217 permutation5
    mixedMoment B raw9195step0 raw9195step0Labels = mixedMoment B raw9195step1 raw9195step1Labels := by
      have ha : raw9195step1 = -raw9195step0 := by apply Matrix.ext; change ∀ i j, raw9195step1 i j = -(raw9195step0 i j); unfold raw9195step1 raw9195step0; decide +kernel
      have hl : raw9195step1Labels = raw9195step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9195step1 raw9195step1Labels = mixedMoment B raw9195step2 raw9195step2Labels := by
      have ha : raw9195step2 = raw9195step1 := by apply Matrix.ext; unfold raw9195step2 raw9195step1; decide +kernel
      have hl : raw9195step1Labels = labelEmbedding1 ∘ raw9195step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9195step1 raw9195step1Labels raw9195step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

def raw9196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw9196step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9196step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9196step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9196step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9196 raw9196Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw9196 raw9196Labels = mixedMoment B raw9196step0 raw9196step0Labels := by
      have ha : raw9196step0 = (fun i j => raw9196 (permutation243 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9196step0 raw9196; decide +kernel
      have hl : raw9196step0Labels = raw9196Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9196 raw9196Labels permutation243 permutation5
    mixedMoment B raw9196step0 raw9196step0Labels = mixedMoment B raw9196step1 raw9196step1Labels := by
      have ha : raw9196step1 = -raw9196step0 := by apply Matrix.ext; change ∀ i j, raw9196step1 i j = -(raw9196step0 i j); unfold raw9196step1 raw9196step0; decide +kernel
      have hl : raw9196step1Labels = raw9196step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9196step1 raw9196step1Labels = mixedMoment B raw9196step2 raw9196step2Labels := by
      have ha : raw9196step2 = raw9196step1 := by apply Matrix.ext; unfold raw9196step2 raw9196step1; decide +kernel
      have hl : raw9196step1Labels = labelEmbedding1 ∘ raw9196step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9196step1 raw9196step1Labels raw9196step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

def raw9197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9197Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw9197step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9197step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9197step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9197step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw9197step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9197 raw9197Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw9197 raw9197Labels = mixedMoment B raw9197step0 raw9197step0Labels := by
      have ha : raw9197step0 = (fun i j => raw9197 (permutation263 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9197step0 raw9197; decide +kernel
      have hl : raw9197step0Labels = raw9197Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9197 raw9197Labels permutation263 permutation5
    mixedMoment B raw9197step0 raw9197step0Labels = mixedMoment B raw9197step1 raw9197step1Labels := by
      have ha : raw9197step1 = -raw9197step0 := by apply Matrix.ext; change ∀ i j, raw9197step1 i j = -(raw9197step0 i j); unfold raw9197step1 raw9197step0; decide +kernel
      have hl : raw9197step1Labels = raw9197step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9197step1 raw9197step1Labels = mixedMoment B raw9197step2 raw9197step2Labels := by
      have ha : raw9197step2 = raw9197step1 := by apply Matrix.ext; unfold raw9197step2 raw9197step1; decide +kernel
      have hl : raw9197step1Labels = labelEmbedding1 ∘ raw9197step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9197step1 raw9197step1Labels raw9197step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3571 node3571Labels := by rfl

def raw9198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9198Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9198step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw9198step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9198step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9198step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9198step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9198 raw9198Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw9198 raw9198Labels = mixedMoment B raw9198step0 raw9198step0Labels := by
      have hz : ∀ j, raw9198 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9198step0 = (fun i j => raw9198 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9198step0 raw9198; decide +kernel
      have hl : raw9198step0Labels = raw9198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9198 raw9198Labels permutation265 hz
    mixedMoment B raw9198step0 raw9198step0Labels = mixedMoment B raw9198step1 raw9198step1Labels := by
      have ha : raw9198step1 = (fun i j => raw9198step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9198step1 raw9198step0; decide +kernel
      have hl : raw9198step1Labels = raw9198step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9198step0 raw9198step0Labels permutation49 permutation5
    mixedMoment B raw9198step1 raw9198step1Labels = mixedMoment B raw9198step2 raw9198step2Labels := by
      have ha : raw9198step2 = -raw9198step1 := by apply Matrix.ext; change ∀ i j, raw9198step2 i j = -(raw9198step1 i j); unfold raw9198step2 raw9198step1; decide +kernel
      have hl : raw9198step2Labels = raw9198step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9198step2 raw9198step2Labels = mixedMoment B raw9198step3 raw9198step3Labels := by
      have ha : raw9198step3 = raw9198step2 := by apply Matrix.ext; unfold raw9198step3 raw9198step2; decide +kernel
      have hl : raw9198step2Labels = labelEmbedding1 ∘ raw9198step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9198step2 raw9198step2Labels raw9198step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

def raw9199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9199Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw9199step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9199step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9199step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9199step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9199step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9199 raw9199Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw9199 raw9199Labels = mixedMoment B raw9199step0 raw9199step0Labels := by
      have ha : raw9199step0 = (fun i j => raw9199 (permutation169 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9199step0 raw9199; decide +kernel
      have hl : raw9199step0Labels = raw9199Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9199 raw9199Labels permutation169 permutation5
    mixedMoment B raw9199step0 raw9199step0Labels = mixedMoment B raw9199step1 raw9199step1Labels := by
      have ha : raw9199step1 = -raw9199step0 := by apply Matrix.ext; change ∀ i j, raw9199step1 i j = -(raw9199step0 i j); unfold raw9199step1 raw9199step0; decide +kernel
      have hl : raw9199step1Labels = raw9199step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9199step1 raw9199step1Labels = mixedMoment B raw9199step2 raw9199step2Labels := by
      have ha : raw9199step2 = raw9199step1 := by apply Matrix.ext; unfold raw9199step2 raw9199step1; decide +kernel
      have hl : raw9199step1Labels = labelEmbedding1 ∘ raw9199step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9199step1 raw9199step1Labels raw9199step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

def raw9200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9200Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9200step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw9200step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9200step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw9200step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9200step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw9200step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9200 raw9200Labels = mixedMoment B node3606 node3606Labels := by
  calc
    mixedMoment B raw9200 raw9200Labels = mixedMoment B raw9200step0 raw9200step0Labels := by
      have hz : ∀ j, raw9200 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9200step0 = (fun i j => raw9200 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9200step0 raw9200; decide +kernel
      have hl : raw9200step0Labels = raw9200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9200 raw9200Labels permutation265 hz
    mixedMoment B raw9200step0 raw9200step0Labels = mixedMoment B raw9200step1 raw9200step1Labels := by
      have ha : raw9200step1 = (fun i j => raw9200step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9200step1 raw9200step0; decide +kernel
      have hl : raw9200step1Labels = raw9200step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9200step0 raw9200step0Labels permutation41 permutation5
    mixedMoment B raw9200step1 raw9200step1Labels = mixedMoment B raw9200step2 raw9200step2Labels := by
      have ha : raw9200step2 = -raw9200step1 := by apply Matrix.ext; change ∀ i j, raw9200step2 i j = -(raw9200step1 i j); unfold raw9200step2 raw9200step1; decide +kernel
      have hl : raw9200step2Labels = raw9200step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9200step2 raw9200step2Labels = mixedMoment B raw9200step3 raw9200step3Labels := by
      have ha : raw9200step3 = raw9200step2 := by apply Matrix.ext; unfold raw9200step3 raw9200step2; decide +kernel
      have hl : raw9200step2Labels = labelEmbedding1 ∘ raw9200step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9200step2 raw9200step2Labels raw9200step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3606 node3606Labels := by rfl

def raw9201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9201Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9201step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw9201step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9201step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9201step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9201step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9201 raw9201Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw9201 raw9201Labels = mixedMoment B raw9201step0 raw9201step0Labels := by
      have hz : ∀ j, raw9201 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9201step0 = (fun i j => raw9201 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9201step0 raw9201; decide +kernel
      have hl : raw9201step0Labels = raw9201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9201 raw9201Labels permutation265 hz
    mixedMoment B raw9201step0 raw9201step0Labels = mixedMoment B raw9201step1 raw9201step1Labels := by
      have ha : raw9201step1 = (fun i j => raw9201step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9201step1 raw9201step0; decide +kernel
      have hl : raw9201step1Labels = raw9201step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9201step0 raw9201step0Labels permutation49 permutation5
    mixedMoment B raw9201step1 raw9201step1Labels = mixedMoment B raw9201step2 raw9201step2Labels := by
      have ha : raw9201step2 = -raw9201step1 := by apply Matrix.ext; change ∀ i j, raw9201step2 i j = -(raw9201step1 i j); unfold raw9201step2 raw9201step1; decide +kernel
      have hl : raw9201step2Labels = raw9201step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9201step2 raw9201step2Labels = mixedMoment B raw9201step3 raw9201step3Labels := by
      have ha : raw9201step3 = raw9201step2 := by apply Matrix.ext; unfold raw9201step3 raw9201step2; decide +kernel
      have hl : raw9201step2Labels = labelEmbedding1 ∘ raw9201step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9201step2 raw9201step2Labels raw9201step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw9202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9202Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9202step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9202step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9202step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9202step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9202step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9202 raw9202Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw9202 raw9202Labels = mixedMoment B raw9202step0 raw9202step0Labels := by
      have hz : ∀ j, raw9202 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9202step0 = (fun i j => raw9202 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9202step0 raw9202; decide +kernel
      have hl : raw9202step0Labels = raw9202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9202 raw9202Labels permutation265 hz
    mixedMoment B raw9202step0 raw9202step0Labels = mixedMoment B raw9202step1 raw9202step1Labels := by
      have ha : raw9202step1 = (fun i j => raw9202step0 (permutation55 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9202step1 raw9202step0; decide +kernel
      have hl : raw9202step1Labels = raw9202step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9202step0 raw9202step0Labels permutation55 permutation5
    mixedMoment B raw9202step1 raw9202step1Labels = mixedMoment B raw9202step2 raw9202step2Labels := by
      have ha : raw9202step2 = -raw9202step1 := by apply Matrix.ext; change ∀ i j, raw9202step2 i j = -(raw9202step1 i j); unfold raw9202step2 raw9202step1; decide +kernel
      have hl : raw9202step2Labels = raw9202step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9202step2 raw9202step2Labels = mixedMoment B raw9202step3 raw9202step3Labels := by
      have ha : raw9202step3 = raw9202step2 := by apply Matrix.ext; unfold raw9202step3 raw9202step2; decide +kernel
      have hl : raw9202step2Labels = labelEmbedding1 ∘ raw9202step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9202step2 raw9202step2Labels raw9202step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw9203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9203Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9203step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw9203step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9203step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9203step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9203step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9203 raw9203Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw9203 raw9203Labels = mixedMoment B raw9203step0 raw9203step0Labels := by
      have hz : ∀ j, raw9203 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9203step0 = (fun i j => raw9203 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9203step0 raw9203; decide +kernel
      have hl : raw9203step0Labels = raw9203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9203 raw9203Labels permutation265 hz
    mixedMoment B raw9203step0 raw9203step0Labels = mixedMoment B raw9203step1 raw9203step1Labels := by
      have ha : raw9203step1 = (fun i j => raw9203step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9203step1 raw9203step0; decide +kernel
      have hl : raw9203step1Labels = raw9203step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9203step0 raw9203step0Labels permutation48 permutation5
    mixedMoment B raw9203step1 raw9203step1Labels = mixedMoment B raw9203step2 raw9203step2Labels := by
      have ha : raw9203step2 = -raw9203step1 := by apply Matrix.ext; change ∀ i j, raw9203step2 i j = -(raw9203step1 i j); unfold raw9203step2 raw9203step1; decide +kernel
      have hl : raw9203step2Labels = raw9203step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9203step2 raw9203step2Labels = mixedMoment B raw9203step3 raw9203step3Labels := by
      have ha : raw9203step3 = raw9203step2 := by apply Matrix.ext; unfold raw9203step3 raw9203step2; decide +kernel
      have hl : raw9203step2Labels = labelEmbedding1 ∘ raw9203step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9203step2 raw9203step2Labels raw9203step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

def raw9204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw9204step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9204step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9204step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9204step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9204step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9204 raw9204Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw9204 raw9204Labels = mixedMoment B raw9204step0 raw9204step0Labels := by
      have ha : raw9204step0 = (fun i j => raw9204 (permutation168 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9204step0 raw9204; decide +kernel
      have hl : raw9204step0Labels = raw9204Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9204 raw9204Labels permutation168 permutation5
    mixedMoment B raw9204step0 raw9204step0Labels = mixedMoment B raw9204step1 raw9204step1Labels := by
      have ha : raw9204step1 = -raw9204step0 := by apply Matrix.ext; change ∀ i j, raw9204step1 i j = -(raw9204step0 i j); unfold raw9204step1 raw9204step0; decide +kernel
      have hl : raw9204step1Labels = raw9204step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9204step1 raw9204step1Labels = mixedMoment B raw9204step2 raw9204step2Labels := by
      have ha : raw9204step2 = raw9204step1 := by apply Matrix.ext; unfold raw9204step2 raw9204step1; decide +kernel
      have hl : raw9204step1Labels = labelEmbedding1 ∘ raw9204step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9204step1 raw9204step1Labels raw9204step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

def raw9205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9205Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw9205step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw9205step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9205step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw9205step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9205step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw9205step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9205 raw9205Labels = mixedMoment B node3606 node3606Labels := by
  calc
    mixedMoment B raw9205 raw9205Labels = mixedMoment B raw9205step0 raw9205step0Labels := by
      have hz : ∀ j, raw9205 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9205step0 = (fun i j => raw9205 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9205step0 raw9205; decide +kernel
      have hl : raw9205step0Labels = raw9205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9205 raw9205Labels permutation265 hz
    mixedMoment B raw9205step0 raw9205step0Labels = mixedMoment B raw9205step1 raw9205step1Labels := by
      have ha : raw9205step1 = (fun i j => raw9205step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9205step1 raw9205step0; decide +kernel
      have hl : raw9205step1Labels = raw9205step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9205step0 raw9205step0Labels permutation35 permutation5
    mixedMoment B raw9205step1 raw9205step1Labels = mixedMoment B raw9205step2 raw9205step2Labels := by
      have ha : raw9205step2 = -raw9205step1 := by apply Matrix.ext; change ∀ i j, raw9205step2 i j = -(raw9205step1 i j); unfold raw9205step2 raw9205step1; decide +kernel
      have hl : raw9205step2Labels = raw9205step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9205step2 raw9205step2Labels = mixedMoment B raw9205step3 raw9205step3Labels := by
      have ha : raw9205step3 = raw9205step2 := by apply Matrix.ext; unfold raw9205step3 raw9205step2; decide +kernel
      have hl : raw9205step2Labels = labelEmbedding1 ∘ raw9205step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9205step2 raw9205step2Labels raw9205step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3606 node3606Labels := by rfl

def raw9206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9206Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw9206step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw9206step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9206step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9206step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9206step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw9206step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9206 raw9206Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw9206 raw9206Labels = mixedMoment B raw9206step0 raw9206step0Labels := by
      have hz : ∀ j, raw9206 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9206step0 = (fun i j => raw9206 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9206step0 raw9206; decide +kernel
      have hl : raw9206step0Labels = raw9206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9206 raw9206Labels permutation265 hz
    mixedMoment B raw9206step0 raw9206step0Labels = mixedMoment B raw9206step1 raw9206step1Labels := by
      have ha : raw9206step1 = (fun i j => raw9206step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9206step1 raw9206step0; decide +kernel
      have hl : raw9206step1Labels = raw9206step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9206step0 raw9206step0Labels permutation48 permutation5
    mixedMoment B raw9206step1 raw9206step1Labels = mixedMoment B raw9206step2 raw9206step2Labels := by
      have ha : raw9206step2 = -raw9206step1 := by apply Matrix.ext; change ∀ i j, raw9206step2 i j = -(raw9206step1 i j); unfold raw9206step2 raw9206step1; decide +kernel
      have hl : raw9206step2Labels = raw9206step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9206step2 raw9206step2Labels = mixedMoment B raw9206step3 raw9206step3Labels := by
      have ha : raw9206step3 = raw9206step2 := by apply Matrix.ext; unfold raw9206step3 raw9206step2; decide +kernel
      have hl : raw9206step2Labels = labelEmbedding1 ∘ raw9206step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9206step2 raw9206step2Labels raw9206step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw9207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9207Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw9207step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9207step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw9207step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9207step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9207step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9207step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw9207step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9207 raw9207Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw9207 raw9207Labels = mixedMoment B raw9207step0 raw9207step0Labels := by
      have hz : ∀ j, raw9207 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9207step0 = (fun i j => raw9207 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9207step0 raw9207; decide +kernel
      have hl : raw9207step0Labels = raw9207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9207 raw9207Labels permutation265 hz
    mixedMoment B raw9207step0 raw9207step0Labels = mixedMoment B raw9207step1 raw9207step1Labels := by
      have ha : raw9207step1 = (fun i j => raw9207step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9207step1 raw9207step0; decide +kernel
      have hl : raw9207step1Labels = raw9207step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9207step0 raw9207step0Labels permutation54 permutation5
    mixedMoment B raw9207step1 raw9207step1Labels = mixedMoment B raw9207step2 raw9207step2Labels := by
      have ha : raw9207step2 = -raw9207step1 := by apply Matrix.ext; change ∀ i j, raw9207step2 i j = -(raw9207step1 i j); unfold raw9207step2 raw9207step1; decide +kernel
      have hl : raw9207step2Labels = raw9207step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9207step2 raw9207step2Labels = mixedMoment B raw9207step3 raw9207step3Labels := by
      have ha : raw9207step3 = raw9207step2 := by apply Matrix.ext; unfold raw9207step3 raw9207step2; decide +kernel
      have hl : raw9207step2Labels = labelEmbedding1 ∘ raw9207step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9207step2 raw9207step2Labels raw9207step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw9208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9208Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9208step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw9208step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9208step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9208step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9208step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9208 raw9208Labels = mixedMoment B node1736 node1736Labels := by
  calc
    mixedMoment B raw9208 raw9208Labels = mixedMoment B raw9208step0 raw9208step0Labels := by
      have hz : ∀ j, raw9208 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9208step0 = (fun i j => raw9208 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9208step0 raw9208; decide +kernel
      have hl : raw9208step0Labels = raw9208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9208 raw9208Labels permutation265 hz
    mixedMoment B raw9208step0 raw9208step0Labels = mixedMoment B raw9208step1 raw9208step1Labels := by
      have ha : raw9208step1 = (fun i j => raw9208step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9208step1 raw9208step0; decide +kernel
      have hl : raw9208step1Labels = raw9208step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9208step0 raw9208step0Labels permutation50 permutation5
    mixedMoment B raw9208step1 raw9208step1Labels = mixedMoment B raw9208step2 raw9208step2Labels := by
      have ha : raw9208step2 = -raw9208step1 := by apply Matrix.ext; change ∀ i j, raw9208step2 i j = -(raw9208step1 i j); unfold raw9208step2 raw9208step1; decide +kernel
      have hl : raw9208step2Labels = raw9208step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9208step2 raw9208step2Labels = mixedMoment B raw9208step3 raw9208step3Labels := by
      have ha : raw9208step3 = raw9208step2 := by apply Matrix.ext; unfold raw9208step3 raw9208step2; decide +kernel
      have hl : raw9208step2Labels = labelEmbedding1 ∘ raw9208step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9208step2 raw9208step2Labels raw9208step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1736 node1736Labels := by rfl

def raw9209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9209Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw9209step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9209step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9209step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9209step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9209step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9209 raw9209Labels = mixedMoment B node3476 node3476Labels := by
  calc
    mixedMoment B raw9209 raw9209Labels = mixedMoment B raw9209step0 raw9209step0Labels := by
      have ha : raw9209step0 = (fun i j => raw9209 (permutation170 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9209step0 raw9209; decide +kernel
      have hl : raw9209step0Labels = raw9209Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9209 raw9209Labels permutation170 permutation5
    mixedMoment B raw9209step0 raw9209step0Labels = mixedMoment B raw9209step1 raw9209step1Labels := by
      have ha : raw9209step1 = -raw9209step0 := by apply Matrix.ext; change ∀ i j, raw9209step1 i j = -(raw9209step0 i j); unfold raw9209step1 raw9209step0; decide +kernel
      have hl : raw9209step1Labels = raw9209step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9209step1 raw9209step1Labels = mixedMoment B raw9209step2 raw9209step2Labels := by
      have ha : raw9209step2 = raw9209step1 := by apply Matrix.ext; unfold raw9209step2 raw9209step1; decide +kernel
      have hl : raw9209step1Labels = labelEmbedding1 ∘ raw9209step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9209step1 raw9209step1Labels raw9209step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3476 node3476Labels := by rfl

def raw9210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9210Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9210step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw9210step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9210step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw9210step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9210step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw9210step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9210 raw9210Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw9210 raw9210Labels = mixedMoment B raw9210step0 raw9210step0Labels := by
      have hz : ∀ j, raw9210 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9210step0 = (fun i j => raw9210 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9210step0 raw9210; decide +kernel
      have hl : raw9210step0Labels = raw9210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9210 raw9210Labels permutation265 hz
    mixedMoment B raw9210step0 raw9210step0Labels = mixedMoment B raw9210step1 raw9210step1Labels := by
      have ha : raw9210step1 = (fun i j => raw9210step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9210step1 raw9210step0; decide +kernel
      have hl : raw9210step1Labels = raw9210step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9210step0 raw9210step0Labels permutation36 permutation5
    mixedMoment B raw9210step1 raw9210step1Labels = mixedMoment B raw9210step2 raw9210step2Labels := by
      have ha : raw9210step2 = -raw9210step1 := by apply Matrix.ext; change ∀ i j, raw9210step2 i j = -(raw9210step1 i j); unfold raw9210step2 raw9210step1; decide +kernel
      have hl : raw9210step2Labels = raw9210step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9210step2 raw9210step2Labels = mixedMoment B raw9210step3 raw9210step3Labels := by
      have ha : raw9210step3 = raw9210step2 := by apply Matrix.ext; unfold raw9210step3 raw9210step2; decide +kernel
      have hl : raw9210step2Labels = labelEmbedding1 ∘ raw9210step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9210step2 raw9210step2Labels raw9210step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3612 node3612Labels := by rfl

def raw9211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9211Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw9211step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw9211step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9211step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw9211step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9211step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw9211step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9211 raw9211Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw9211 raw9211Labels = mixedMoment B raw9211step0 raw9211step0Labels := by
      have hz : ∀ j, raw9211 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9211step0 = (fun i j => raw9211 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9211step0 raw9211; decide +kernel
      have hl : raw9211step0Labels = raw9211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9211 raw9211Labels permutation265 hz
    mixedMoment B raw9211step0 raw9211step0Labels = mixedMoment B raw9211step1 raw9211step1Labels := by
      have ha : raw9211step1 = (fun i j => raw9211step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9211step1 raw9211step0; decide +kernel
      have hl : raw9211step1Labels = raw9211step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9211step0 raw9211step0Labels permutation42 permutation5
    mixedMoment B raw9211step1 raw9211step1Labels = mixedMoment B raw9211step2 raw9211step2Labels := by
      have ha : raw9211step2 = -raw9211step1 := by apply Matrix.ext; change ∀ i j, raw9211step2 i j = -(raw9211step1 i j); unfold raw9211step2 raw9211step1; decide +kernel
      have hl : raw9211step2Labels = raw9211step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9211step2 raw9211step2Labels = mixedMoment B raw9211step3 raw9211step3Labels := by
      have ha : raw9211step3 = raw9211step2 := by apply Matrix.ext; unfold raw9211step3 raw9211step2; decide +kernel
      have hl : raw9211step2Labels = labelEmbedding1 ∘ raw9211step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9211step2 raw9211step2Labels raw9211step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3612 node3612Labels := by rfl

def raw9212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw9212Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw9212step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9212step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw9212step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9212step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9212step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9212step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw9212step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9212 raw9212Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw9212 raw9212Labels = mixedMoment B raw9212step0 raw9212step0Labels := by
      have hz : ∀ j, raw9212 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9212step0 = (fun i j => raw9212 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9212step0 raw9212; decide +kernel
      have hl : raw9212step0Labels = raw9212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9212 raw9212Labels permutation265 hz
    mixedMoment B raw9212step0 raw9212step0Labels = mixedMoment B raw9212step1 raw9212step1Labels := by
      have ha : raw9212step1 = (fun i j => raw9212step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9212step1 raw9212step0; decide +kernel
      have hl : raw9212step1Labels = raw9212step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9212step0 raw9212step0Labels permutation50 permutation5
    mixedMoment B raw9212step1 raw9212step1Labels = mixedMoment B raw9212step2 raw9212step2Labels := by
      have ha : raw9212step2 = -raw9212step1 := by apply Matrix.ext; change ∀ i j, raw9212step2 i j = -(raw9212step1 i j); unfold raw9212step2 raw9212step1; decide +kernel
      have hl : raw9212step2Labels = raw9212step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9212step2 raw9212step2Labels = mixedMoment B raw9212step3 raw9212step3Labels := by
      have ha : raw9212step3 = raw9212step2 := by apply Matrix.ext; unfold raw9212step3 raw9212step2; decide +kernel
      have hl : raw9212step2Labels = labelEmbedding1 ∘ raw9212step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9212step2 raw9212step2Labels raw9212step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3580 node3580Labels := by rfl

def raw9213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9213Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9213step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw9213step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9213step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9213step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9213step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9213step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9213 raw9213Labels = mixedMoment B node1723 node1723Labels := by
  calc
    mixedMoment B raw9213 raw9213Labels = mixedMoment B raw9213step0 raw9213step0Labels := by
      have hz : ∀ j, raw9213 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9213step0 = (fun i j => raw9213 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9213step0 raw9213; decide +kernel
      have hl : raw9213step0Labels = raw9213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9213 raw9213Labels permutation265 hz
    mixedMoment B raw9213step0 raw9213step0Labels = mixedMoment B raw9213step1 raw9213step1Labels := by
      have ha : raw9213step1 = (fun i j => raw9213step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9213step1 raw9213step0; decide +kernel
      have hl : raw9213step1Labels = raw9213step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9213step0 raw9213step0Labels permutation44 permutation5
    mixedMoment B raw9213step1 raw9213step1Labels = mixedMoment B raw9213step2 raw9213step2Labels := by
      have ha : raw9213step2 = -raw9213step1 := by apply Matrix.ext; change ∀ i j, raw9213step2 i j = -(raw9213step1 i j); unfold raw9213step2 raw9213step1; decide +kernel
      have hl : raw9213step2Labels = raw9213step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9213step2 raw9213step2Labels = mixedMoment B raw9213step3 raw9213step3Labels := by
      have ha : raw9213step3 = raw9213step2 := by apply Matrix.ext; unfold raw9213step3 raw9213step2; decide +kernel
      have hl : raw9213step2Labels = labelEmbedding1 ∘ raw9213step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9213step2 raw9213step2Labels raw9213step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1723 node1723Labels := by rfl

def raw9214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9214Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw9214step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9214step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9214step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9214step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw9214step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9214 raw9214Labels = mixedMoment B node3466 node3466Labels := by
  calc
    mixedMoment B raw9214 raw9214Labels = mixedMoment B raw9214step0 raw9214step0Labels := by
      have ha : raw9214step0 = (fun i j => raw9214 (permutation164 i) (permutation5 j)) := by apply Matrix.ext; unfold raw9214step0 raw9214; decide +kernel
      have hl : raw9214step0Labels = raw9214Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9214 raw9214Labels permutation164 permutation5
    mixedMoment B raw9214step0 raw9214step0Labels = mixedMoment B raw9214step1 raw9214step1Labels := by
      have ha : raw9214step1 = -raw9214step0 := by apply Matrix.ext; change ∀ i j, raw9214step1 i j = -(raw9214step0 i j); unfold raw9214step1 raw9214step0; decide +kernel
      have hl : raw9214step1Labels = raw9214step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw9214step1 raw9214step1Labels = mixedMoment B raw9214step2 raw9214step2Labels := by
      have ha : raw9214step2 = raw9214step1 := by apply Matrix.ext; unfold raw9214step2 raw9214step1; decide +kernel
      have hl : raw9214step1Labels = labelEmbedding1 ∘ raw9214step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9214step1 raw9214step1Labels raw9214step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3466 node3466Labels := by rfl

def raw9215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9215Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw9215step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw9215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9215step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw9215step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw9215step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9215 raw9215Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw9215 raw9215Labels = mixedMoment B raw9215step0 raw9215step0Labels := by
      have hz : ∀ j, raw9215 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw9215step0 = (fun i j => raw9215 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw9215step0 raw9215; decide +kernel
      have hl : raw9215step0Labels = raw9215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9215 raw9215Labels permutation265 hz
    mixedMoment B raw9215step0 raw9215step0Labels = mixedMoment B raw9215step1 raw9215step1Labels := by
      have ha : raw9215step1 = (fun i j => raw9215step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw9215step1 raw9215step0; decide +kernel
      have hl : raw9215step1Labels = raw9215step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9215step0 raw9215step0Labels permutation151 permutation7
    mixedMoment B raw9215step1 raw9215step1Labels = mixedMoment B raw9215step2 raw9215step2Labels := by
      have ha : raw9215step2 = raw9215step1 := by apply Matrix.ext; unfold raw9215step2 raw9215step1; decide +kernel
      have hl : raw9215step1Labels = labelEmbedding1 ∘ raw9215step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9215step1 raw9215step1Labels raw9215step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
