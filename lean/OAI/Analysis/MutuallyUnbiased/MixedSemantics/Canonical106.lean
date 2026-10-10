import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw13568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13568Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13568step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13568step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13568 raw13568Labels = mixedMoment B node2741 node2741Labels := by
  calc
    mixedMoment B raw13568 raw13568Labels = mixedMoment B raw13568step0 raw13568step0Labels := by
      have hz : ∀ j, raw13568 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13568step0 = (fun i j => raw13568 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13568step0 raw13568; decide +kernel
      have hl : raw13568step0Labels = raw13568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13568 raw13568Labels permutation346 hz
    mixedMoment B raw13568step0 raw13568step0Labels = mixedMoment B raw13568step1 raw13568step1Labels := by
      have ha : raw13568step1 = (fun i j => raw13568step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13568step1 raw13568step0; decide +kernel
      have hl : raw13568step1Labels = raw13568step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13568step0 raw13568step0Labels permutation50 permutation2
    _ = mixedMoment B node2741 node2741Labels := by rfl

def raw13569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13569Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13569step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13569 raw13569Labels = mixedMoment B node2631 node2631Labels := by
  calc
    mixedMoment B raw13569 raw13569Labels = mixedMoment B raw13569step0 raw13569step0Labels := by
      have ha : raw13569step0 = (fun i j => raw13569 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13569step0 raw13569; decide +kernel
      have hl : raw13569step0Labels = raw13569Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13569 raw13569Labels permutation170 permutation2
    _ = mixedMoment B node2631 node2631Labels := by rfl

def raw13570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13570Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13570step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13570 raw13570Labels = mixedMoment B node2633 node2633Labels := by
  calc
    mixedMoment B raw13570 raw13570Labels = mixedMoment B raw13570step0 raw13570step0Labels := by
      have hz : ∀ j, raw13570 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13570step0 = (fun i j => raw13570 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13570step0 raw13570; decide +kernel
      have hl : raw13570step0Labels = raw13570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13570 raw13570Labels permutation346 hz
    mixedMoment B raw13570step0 raw13570step0Labels = mixedMoment B raw13570step1 raw13570step1Labels := by
      have ha : raw13570step1 = (fun i j => raw13570step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13570step1 raw13570step0; decide +kernel
      have hl : raw13570step1Labels = raw13570step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13570step0 raw13570step0Labels permutation37 permutation2
    _ = mixedMoment B node2633 node2633Labels := by rfl

def raw13571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13571Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13571step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13571step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13571 raw13571Labels = mixedMoment B node2633 node2633Labels := by
  calc
    mixedMoment B raw13571 raw13571Labels = mixedMoment B raw13571step0 raw13571step0Labels := by
      have hz : ∀ j, raw13571 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13571step0 = (fun i j => raw13571 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13571step0 raw13571; decide +kernel
      have hl : raw13571step0Labels = raw13571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13571 raw13571Labels permutation346 hz
    mixedMoment B raw13571step0 raw13571step0Labels = mixedMoment B raw13571step1 raw13571step1Labels := by
      have ha : raw13571step1 = (fun i j => raw13571step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13571step1 raw13571step0; decide +kernel
      have hl : raw13571step1Labels = raw13571step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13571step0 raw13571step0Labels permutation36 permutation2
    _ = mixedMoment B node2633 node2633Labels := by rfl

def raw13572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13572step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13572 raw13572Labels = mixedMoment B node2641 node2641Labels := by
  calc
    mixedMoment B raw13572 raw13572Labels = mixedMoment B raw13572step0 raw13572step0Labels := by
      have hz : ∀ j, raw13572 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13572step0 = (fun i j => raw13572 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13572step0 raw13572; decide +kernel
      have hl : raw13572step0Labels = raw13572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13572 raw13572Labels permutation346 hz
    _ = mixedMoment B node2641 node2641Labels := by rfl

def raw13573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13573step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13573 raw13573Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw13573 raw13573Labels = mixedMoment B raw13573step0 raw13573step0Labels := by
      have hz : ∀ j, raw13573 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13573step0 = (fun i j => raw13573 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13573step0 raw13573; decide +kernel
      have hl : raw13573step0Labels = raw13573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13573 raw13573Labels permutation434 hz
    mixedMoment B raw13573step0 raw13573step0Labels = mixedMoment B raw13573step1 raw13573step1Labels := by
      have hz : ∀ j, raw13573step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw13573step1 = (fun i j => raw13573step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw13573step1 raw13573step0; decide +kernel
      have hl : raw13573step1Labels = raw13573step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13573step0 raw13573step0Labels permutation80 hz
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw13574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13574step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13574step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13574step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13574 raw13574Labels = mixedMoment B node4489 node4489Labels := by
  calc
    mixedMoment B raw13574 raw13574Labels = mixedMoment B raw13574step0 raw13574step0Labels := by
      have hz : ∀ j, raw13574 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13574step0 = (fun i j => raw13574 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13574step0 raw13574; decide +kernel
      have hl : raw13574step0Labels = raw13574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13574 raw13574Labels permutation346 hz
    mixedMoment B raw13574step0 raw13574step0Labels = mixedMoment B raw13574step1 raw13574step1Labels := by
      have ha : raw13574step1 = (fun i j => raw13574step0 (permutation53 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13574step1 raw13574step0; decide +kernel
      have hl : raw13574step1Labels = raw13574step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13574step0 raw13574step0Labels permutation53 permutation3
    mixedMoment B raw13574step1 raw13574step1Labels = mixedMoment B raw13574step2 raw13574step2Labels := by
      have ha : raw13574step2 = raw13574step1 := by apply Matrix.ext; unfold raw13574step2 raw13574step1; decide +kernel
      have hl : raw13574step1Labels = labelEmbedding6 ∘ raw13574step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13574step1 raw13574step1Labels raw13574step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4489 node4489Labels := by rfl

def raw13575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13575step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13575step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13575step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13575 raw13575Labels = mixedMoment B node5093 node5093Labels := by
  calc
    mixedMoment B raw13575 raw13575Labels = mixedMoment B raw13575step0 raw13575step0Labels := by
      have ha : raw13575step0 = (fun i j => raw13575 (permutation197 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13575step0 raw13575; decide +kernel
      have hl : raw13575step0Labels = raw13575Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13575 raw13575Labels permutation197 permutation3
    mixedMoment B raw13575step0 raw13575step0Labels = mixedMoment B raw13575step1 raw13575step1Labels := by
      have ha : raw13575step1 = raw13575step0 := by apply Matrix.ext; unfold raw13575step1 raw13575step0; decide +kernel
      have hl : raw13575step0Labels = labelEmbedding6 ∘ raw13575step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13575step0 raw13575step0Labels raw13575step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5093 node5093Labels := by rfl

def raw13576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw13576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13576step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13576step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13576step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13576step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13576step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13576step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13576step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13576 raw13576Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw13576 raw13576Labels = mixedMoment B raw13576step0 raw13576step0Labels := by
      have hz : ∀ j, raw13576 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13576step0 = (fun i j => raw13576 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13576step0 raw13576; decide +kernel
      have hl : raw13576step0Labels = raw13576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13576 raw13576Labels permutation520 hz
    mixedMoment B raw13576step0 raw13576step0Labels = mixedMoment B raw13576step1 raw13576step1Labels := by
      have hz : ∀ j, raw13576step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw13576step1 = (fun i j => raw13576step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw13576step1 raw13576step0; decide +kernel
      have hl : raw13576step1Labels = raw13576step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13576step0 raw13576step0Labels permutation80 hz
    mixedMoment B raw13576step1 raw13576step1Labels = mixedMoment B raw13576step2 raw13576step2Labels := by
      have ha : raw13576step2 = (fun i j => raw13576step1 (permutation13 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13576step2 raw13576step1; decide +kernel
      have hl : raw13576step2Labels = raw13576step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13576step1 raw13576step1Labels permutation13 permutation3
    mixedMoment B raw13576step2 raw13576step2Labels = mixedMoment B raw13576step3 raw13576step3Labels := by
      have ha : raw13576step3 = raw13576step2 := by apply Matrix.ext; unfold raw13576step3 raw13576step2; decide +kernel
      have hl : raw13576step2Labels = labelEmbedding6 ∘ raw13576step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13576step2 raw13576step2Labels raw13576step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw13577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw13577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw13577step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13577step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13577step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13577step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13577 raw13577Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw13577 raw13577Labels = mixedMoment B raw13577step0 raw13577step0Labels := by
      have hz : ∀ j, raw13577 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13577step0 = (fun i j => raw13577 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13577step0 raw13577; decide +kernel
      have hl : raw13577step0Labels = raw13577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13577 raw13577Labels permutation346 hz
    mixedMoment B raw13577step0 raw13577step0Labels = mixedMoment B raw13577step1 raw13577step1Labels := by
      have ha : raw13577step1 = (fun i j => raw13577step0 (permutation53 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13577step1 raw13577step0; decide +kernel
      have hl : raw13577step1Labels = raw13577step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13577step0 raw13577step0Labels permutation53 permutation3
    mixedMoment B raw13577step1 raw13577step1Labels = mixedMoment B raw13577step2 raw13577step2Labels := by
      have ha : raw13577step2 = raw13577step1 := by apply Matrix.ext; unfold raw13577step2 raw13577step1; decide +kernel
      have hl : raw13577step1Labels = labelEmbedding6 ∘ raw13577step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13577step1 raw13577step1Labels raw13577step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

def raw13578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13578step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13578step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13578step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13578 raw13578Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw13578 raw13578Labels = mixedMoment B raw13578step0 raw13578step0Labels := by
      have ha : raw13578step0 = (fun i j => raw13578 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13578step0 raw13578; decide +kernel
      have hl : raw13578step0Labels = raw13578Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13578 raw13578Labels permutation170 permutation3
    mixedMoment B raw13578step0 raw13578step0Labels = mixedMoment B raw13578step1 raw13578step1Labels := by
      have ha : raw13578step1 = raw13578step0 := by apply Matrix.ext; unfold raw13578step1 raw13578step0; decide +kernel
      have hl : raw13578step0Labels = labelEmbedding6 ∘ raw13578step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13578step0 raw13578step0Labels raw13578step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4451 node4451Labels := by rfl

def raw13579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13579step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13579step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13579step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13579 raw13579Labels = mixedMoment B node5162 node5162Labels := by
  calc
    mixedMoment B raw13579 raw13579Labels = mixedMoment B raw13579step0 raw13579step0Labels := by
      have ha : raw13579step0 = (fun i j => raw13579 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13579step0 raw13579; decide +kernel
      have hl : raw13579step0Labels = raw13579Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13579 raw13579Labels permutation170 permutation3
    mixedMoment B raw13579step0 raw13579step0Labels = mixedMoment B raw13579step1 raw13579step1Labels := by
      have ha : raw13579step1 = raw13579step0 := by apply Matrix.ext; unfold raw13579step1 raw13579step0; decide +kernel
      have hl : raw13579step0Labels = labelEmbedding6 ∘ raw13579step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13579step0 raw13579step0Labels raw13579step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5162 node5162Labels := by rfl

def raw13580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw13580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13580step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13580step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13580step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13580step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13580 raw13580Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw13580 raw13580Labels = mixedMoment B raw13580step0 raw13580step0Labels := by
      have hz : ∀ j, raw13580 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13580step0 = (fun i j => raw13580 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13580step0 raw13580; decide +kernel
      have hl : raw13580step0Labels = raw13580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13580 raw13580Labels permutation520 hz
    mixedMoment B raw13580step0 raw13580step0Labels = mixedMoment B raw13580step1 raw13580step1Labels := by
      have ha : raw13580step1 = (fun i j => raw13580step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13580step1 raw13580step0; decide +kernel
      have hl : raw13580step1Labels = raw13580step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13580step0 raw13580step0Labels permutation36 permutation3
    mixedMoment B raw13580step1 raw13580step1Labels = mixedMoment B raw13580step2 raw13580step2Labels := by
      have ha : raw13580step2 = raw13580step1 := by apply Matrix.ext; unfold raw13580step2 raw13580step1; decide +kernel
      have hl : raw13580step1Labels = labelEmbedding6 ∘ raw13580step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13580step1 raw13580step1Labels raw13580step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw13581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw13581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13581step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13581step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13581 raw13581Labels = mixedMoment B node5227 node5227Labels := by
  calc
    mixedMoment B raw13581 raw13581Labels = mixedMoment B raw13581step0 raw13581step0Labels := by
      have ha : raw13581step0 = (fun i j => raw13581 (permutation246 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13581step0 raw13581; decide +kernel
      have hl : raw13581step0Labels = raw13581Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13581 raw13581Labels permutation246 permutation3
    mixedMoment B raw13581step0 raw13581step0Labels = mixedMoment B raw13581step1 raw13581step1Labels := by
      have ha : raw13581step1 = raw13581step0 := by apply Matrix.ext; unfold raw13581step1 raw13581step0; decide +kernel
      have hl : raw13581step0Labels = labelEmbedding6 ∘ raw13581step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13581step0 raw13581step0Labels raw13581step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5227 node5227Labels := by rfl

def raw13582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13582step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13582step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13582step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13582step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13582 raw13582Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw13582 raw13582Labels = mixedMoment B raw13582step0 raw13582step0Labels := by
      have hz : ∀ j, raw13582 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13582step0 = (fun i j => raw13582 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13582step0 raw13582; decide +kernel
      have hl : raw13582step0Labels = raw13582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13582 raw13582Labels permutation346 hz
    mixedMoment B raw13582step0 raw13582step0Labels = mixedMoment B raw13582step1 raw13582step1Labels := by
      have ha : raw13582step1 = (fun i j => raw13582step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13582step1 raw13582step0; decide +kernel
      have hl : raw13582step1Labels = raw13582step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13582step0 raw13582step0Labels permutation37 permutation3
    mixedMoment B raw13582step1 raw13582step1Labels = mixedMoment B raw13582step2 raw13582step2Labels := by
      have ha : raw13582step2 = raw13582step1 := by apply Matrix.ext; unfold raw13582step2 raw13582step1; decide +kernel
      have hl : raw13582step1Labels = labelEmbedding6 ∘ raw13582step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13582step1 raw13582step1Labels raw13582step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

def raw13583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13583step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13583step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13583step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13583step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13583step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13583 raw13583Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw13583 raw13583Labels = mixedMoment B raw13583step0 raw13583step0Labels := by
      have hz : ∀ j, raw13583 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13583step0 = (fun i j => raw13583 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13583step0 raw13583; decide +kernel
      have hl : raw13583step0Labels = raw13583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13583 raw13583Labels permutation346 hz
    mixedMoment B raw13583step0 raw13583step0Labels = mixedMoment B raw13583step1 raw13583step1Labels := by
      have ha : raw13583step1 = (fun i j => raw13583step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13583step1 raw13583step0; decide +kernel
      have hl : raw13583step1Labels = raw13583step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13583step0 raw13583step0Labels permutation37 permutation3
    mixedMoment B raw13583step1 raw13583step1Labels = mixedMoment B raw13583step2 raw13583step2Labels := by
      have ha : raw13583step2 = raw13583step1 := by apply Matrix.ext; unfold raw13583step2 raw13583step1; decide +kernel
      have hl : raw13583step1Labels = labelEmbedding6 ∘ raw13583step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13583step1 raw13583step1Labels raw13583step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw13584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13584step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13584step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13584step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13584 raw13584Labels = mixedMoment B node5070 node5070Labels := by
  calc
    mixedMoment B raw13584 raw13584Labels = mixedMoment B raw13584step0 raw13584step0Labels := by
      have ha : raw13584step0 = (fun i j => raw13584 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13584step0 raw13584; decide +kernel
      have hl : raw13584step0Labels = raw13584Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13584 raw13584Labels permutation181 permutation3
    mixedMoment B raw13584step0 raw13584step0Labels = mixedMoment B raw13584step1 raw13584step1Labels := by
      have ha : raw13584step1 = raw13584step0 := by apply Matrix.ext; unfold raw13584step1 raw13584step0; decide +kernel
      have hl : raw13584step0Labels = labelEmbedding6 ∘ raw13584step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13584step0 raw13584step0Labels raw13584step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5070 node5070Labels := by rfl

def raw13585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw13585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw13585step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw13585step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13585step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw13585step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13585step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw13585step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13585 raw13585Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw13585 raw13585Labels = mixedMoment B raw13585step0 raw13585step0Labels := by
      have hz : ∀ j, raw13585 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13585step0 = (fun i j => raw13585 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13585step0 raw13585; decide +kernel
      have hl : raw13585step0Labels = raw13585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13585 raw13585Labels permutation520 hz
    mixedMoment B raw13585step0 raw13585step0Labels = mixedMoment B raw13585step1 raw13585step1Labels := by
      have hz : ∀ j, raw13585step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw13585step1 = (fun i j => raw13585step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw13585step1 raw13585step0; decide +kernel
      have hl : raw13585step1Labels = raw13585step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13585step0 raw13585step0Labels permutation80 hz
    mixedMoment B raw13585step1 raw13585step1Labels = mixedMoment B raw13585step2 raw13585step2Labels := by
      have ha : raw13585step2 = (fun i j => raw13585step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13585step2 raw13585step1; decide +kernel
      have hl : raw13585step2Labels = raw13585step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13585step1 raw13585step1Labels permutation9 permutation3
    mixedMoment B raw13585step2 raw13585step2Labels = mixedMoment B raw13585step3 raw13585step3Labels := by
      have ha : raw13585step3 = raw13585step2 := by apply Matrix.ext; unfold raw13585step3 raw13585step2; decide +kernel
      have hl : raw13585step2Labels = labelEmbedding6 ∘ raw13585step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13585step2 raw13585step2Labels raw13585step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw13586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw13586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw13586step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13586step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13586step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13586step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13586 raw13586Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw13586 raw13586Labels = mixedMoment B raw13586step0 raw13586step0Labels := by
      have hz : ∀ j, raw13586 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13586step0 = (fun i j => raw13586 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13586step0 raw13586; decide +kernel
      have hl : raw13586step0Labels = raw13586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13586 raw13586Labels permutation346 hz
    mixedMoment B raw13586step0 raw13586step0Labels = mixedMoment B raw13586step1 raw13586step1Labels := by
      have ha : raw13586step1 = (fun i j => raw13586step0 (permutation51 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13586step1 raw13586step0; decide +kernel
      have hl : raw13586step1Labels = raw13586step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13586step0 raw13586step0Labels permutation51 permutation3
    mixedMoment B raw13586step1 raw13586step1Labels = mixedMoment B raw13586step2 raw13586step2Labels := by
      have ha : raw13586step2 = raw13586step1 := by apply Matrix.ext; unfold raw13586step2 raw13586step1; decide +kernel
      have hl : raw13586step1Labels = labelEmbedding6 ∘ raw13586step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13586step1 raw13586step1Labels raw13586step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw13587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw13587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw13587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13587step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13587step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13587step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13587 raw13587Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw13587 raw13587Labels = mixedMoment B raw13587step0 raw13587step0Labels := by
      have hz : ∀ j, raw13587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13587step0 = (fun i j => raw13587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13587step0 raw13587; decide +kernel
      have hl : raw13587step0Labels = raw13587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13587 raw13587Labels permutation346 hz
    mixedMoment B raw13587step0 raw13587step0Labels = mixedMoment B raw13587step1 raw13587step1Labels := by
      have ha : raw13587step1 = (fun i j => raw13587step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13587step1 raw13587step0; decide +kernel
      have hl : raw13587step1Labels = raw13587step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13587step0 raw13587step0Labels permutation36 permutation3
    mixedMoment B raw13587step1 raw13587step1Labels = mixedMoment B raw13587step2 raw13587step2Labels := by
      have ha : raw13587step2 = raw13587step1 := by apply Matrix.ext; unfold raw13587step2 raw13587step1; decide +kernel
      have hl : raw13587step1Labels = labelEmbedding6 ∘ raw13587step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13587step1 raw13587step1Labels raw13587step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

def raw13588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw13588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw13588step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13588step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13588step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13588step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13588 raw13588Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw13588 raw13588Labels = mixedMoment B raw13588step0 raw13588step0Labels := by
      have hz : ∀ j, raw13588 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13588step0 = (fun i j => raw13588 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13588step0 raw13588; decide +kernel
      have hl : raw13588step0Labels = raw13588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13588 raw13588Labels permutation346 hz
    mixedMoment B raw13588step0 raw13588step0Labels = mixedMoment B raw13588step1 raw13588step1Labels := by
      have ha : raw13588step1 = (fun i j => raw13588step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13588step1 raw13588step0; decide +kernel
      have hl : raw13588step1Labels = raw13588step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13588step0 raw13588step0Labels permutation36 permutation3
    mixedMoment B raw13588step1 raw13588step1Labels = mixedMoment B raw13588step2 raw13588step2Labels := by
      have ha : raw13588step2 = raw13588step1 := by apply Matrix.ext; unfold raw13588step2 raw13588step1; decide +kernel
      have hl : raw13588step1Labels = labelEmbedding6 ∘ raw13588step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13588step1 raw13588step1Labels raw13588step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw13589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw13589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13589step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13589step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13589step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13589 raw13589Labels = mixedMoment B node5070 node5070Labels := by
  calc
    mixedMoment B raw13589 raw13589Labels = mixedMoment B raw13589step0 raw13589step0Labels := by
      have ha : raw13589step0 = (fun i j => raw13589 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13589step0 raw13589; decide +kernel
      have hl : raw13589step0Labels = raw13589Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13589 raw13589Labels permutation180 permutation3
    mixedMoment B raw13589step0 raw13589step0Labels = mixedMoment B raw13589step1 raw13589step1Labels := by
      have ha : raw13589step1 = raw13589step0 := by apply Matrix.ext; unfold raw13589step1 raw13589step0; decide +kernel
      have hl : raw13589step0Labels = labelEmbedding6 ∘ raw13589step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13589step0 raw13589step0Labels raw13589step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5070 node5070Labels := by rfl

def raw13590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw13590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw13590step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13590step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13590step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13590step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13590 raw13590Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw13590 raw13590Labels = mixedMoment B raw13590step0 raw13590step0Labels := by
      have hz : ∀ j, raw13590 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13590step0 = (fun i j => raw13590 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13590step0 raw13590; decide +kernel
      have hl : raw13590step0Labels = raw13590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13590 raw13590Labels permutation346 hz
    mixedMoment B raw13590step0 raw13590step0Labels = mixedMoment B raw13590step1 raw13590step1Labels := by
      have ha : raw13590step1 = (fun i j => raw13590step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13590step1 raw13590step0; decide +kernel
      have hl : raw13590step1Labels = raw13590step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13590step0 raw13590step0Labels permutation50 permutation3
    mixedMoment B raw13590step1 raw13590step1Labels = mixedMoment B raw13590step2 raw13590step2Labels := by
      have ha : raw13590step2 = raw13590step1 := by apply Matrix.ext; unfold raw13590step2 raw13590step1; decide +kernel
      have hl : raw13590step1Labels = labelEmbedding6 ∘ raw13590step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13590step1 raw13590step1Labels raw13590step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw13591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13591step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13591step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13591step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13591step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13591 raw13591Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw13591 raw13591Labels = mixedMoment B raw13591step0 raw13591step0Labels := by
      have hz : ∀ j, raw13591 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13591step0 = (fun i j => raw13591 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13591step0 raw13591; decide +kernel
      have hl : raw13591step0Labels = raw13591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13591 raw13591Labels permutation346 hz
    mixedMoment B raw13591step0 raw13591step0Labels = mixedMoment B raw13591step1 raw13591step1Labels := by
      have ha : raw13591step1 = (fun i j => raw13591step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13591step1 raw13591step0; decide +kernel
      have hl : raw13591step1Labels = raw13591step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13591step0 raw13591step0Labels permutation32 permutation3
    mixedMoment B raw13591step1 raw13591step1Labels = mixedMoment B raw13591step2 raw13591step2Labels := by
      have ha : raw13591step2 = raw13591step1 := by apply Matrix.ext; unfold raw13591step2 raw13591step1; decide +kernel
      have hl : raw13591step1Labels = labelEmbedding6 ∘ raw13591step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13591step1 raw13591step1Labels raw13591step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4461 node4461Labels := by rfl

def raw13592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13592step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13592step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13592step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13592step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13592 raw13592Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw13592 raw13592Labels = mixedMoment B raw13592step0 raw13592step0Labels := by
      have hz : ∀ j, raw13592 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13592step0 = (fun i j => raw13592 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13592step0 raw13592; decide +kernel
      have hl : raw13592step0Labels = raw13592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13592 raw13592Labels permutation346 hz
    mixedMoment B raw13592step0 raw13592step0Labels = mixedMoment B raw13592step1 raw13592step1Labels := by
      have ha : raw13592step1 = (fun i j => raw13592step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13592step1 raw13592step0; decide +kernel
      have hl : raw13592step1Labels = raw13592step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13592step0 raw13592step0Labels permutation32 permutation3
    mixedMoment B raw13592step1 raw13592step1Labels = mixedMoment B raw13592step2 raw13592step2Labels := by
      have ha : raw13592step2 = raw13592step1 := by apply Matrix.ext; unfold raw13592step2 raw13592step1; decide +kernel
      have hl : raw13592step1Labels = labelEmbedding6 ∘ raw13592step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13592step1 raw13592step1Labels raw13592step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5172 node5172Labels := by rfl

def raw13593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13593step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13593step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13593step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13593 raw13593Labels = mixedMoment B node5076 node5076Labels := by
  calc
    mixedMoment B raw13593 raw13593Labels = mixedMoment B raw13593step0 raw13593step0Labels := by
      have ha : raw13593step0 = (fun i j => raw13593 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13593step0 raw13593; decide +kernel
      have hl : raw13593step0Labels = raw13593Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13593 raw13593Labels permutation176 permutation3
    mixedMoment B raw13593step0 raw13593step0Labels = mixedMoment B raw13593step1 raw13593step1Labels := by
      have ha : raw13593step1 = raw13593step0 := by apply Matrix.ext; unfold raw13593step1 raw13593step0; decide +kernel
      have hl : raw13593step0Labels = labelEmbedding6 ∘ raw13593step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13593step0 raw13593step0Labels raw13593step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5076 node5076Labels := by rfl

def raw13594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw13594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13594step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13594step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13594step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13594step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13594step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13594step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13594 raw13594Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw13594 raw13594Labels = mixedMoment B raw13594step0 raw13594step0Labels := by
      have hz : ∀ j, raw13594 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13594step0 = (fun i j => raw13594 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13594step0 raw13594; decide +kernel
      have hl : raw13594step0Labels = raw13594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13594 raw13594Labels permutation520 hz
    mixedMoment B raw13594step0 raw13594step0Labels = mixedMoment B raw13594step1 raw13594step1Labels := by
      have hz : ∀ j, raw13594step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw13594step1 = (fun i j => raw13594step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw13594step1 raw13594step0; decide +kernel
      have hl : raw13594step1Labels = raw13594step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13594step0 raw13594step0Labels permutation80 hz
    mixedMoment B raw13594step1 raw13594step1Labels = mixedMoment B raw13594step2 raw13594step2Labels := by
      have ha : raw13594step2 = (fun i j => raw13594step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13594step2 raw13594step1; decide +kernel
      have hl : raw13594step2Labels = raw13594step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13594step1 raw13594step1Labels permutation8 permutation3
    mixedMoment B raw13594step2 raw13594step2Labels = mixedMoment B raw13594step3 raw13594step3Labels := by
      have ha : raw13594step3 = raw13594step2 := by apply Matrix.ext; unfold raw13594step3 raw13594step2; decide +kernel
      have hl : raw13594step2Labels = labelEmbedding6 ∘ raw13594step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13594step2 raw13594step2Labels raw13594step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw13595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13595Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13595step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13595step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13595step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13595step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13595 raw13595Labels = mixedMoment B node4017 node4017Labels := by
  calc
    mixedMoment B raw13595 raw13595Labels = mixedMoment B raw13595step0 raw13595step0Labels := by
      have hz : ∀ j, raw13595 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13595step0 = (fun i j => raw13595 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13595step0 raw13595; decide +kernel
      have hl : raw13595step0Labels = raw13595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13595 raw13595Labels permutation434 hz
    mixedMoment B raw13595step0 raw13595step0Labels = mixedMoment B raw13595step1 raw13595step1Labels := by
      have hz : ∀ j, raw13595step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw13595step1 = (fun i j => raw13595step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw13595step1 raw13595step0; decide +kernel
      have hl : raw13595step1Labels = raw13595step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13595step0 raw13595step0Labels permutation80 hz
    mixedMoment B raw13595step1 raw13595step1Labels = mixedMoment B raw13595step2 raw13595step2Labels := by
      have ha : raw13595step2 = (fun i j => raw13595step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13595step2 raw13595step1; decide +kernel
      have hl : raw13595step2Labels = raw13595step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13595step1 raw13595step1Labels permutation9 permutation3
    _ = mixedMoment B node4017 node4017Labels := by rfl

def raw13596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13596Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13596step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13596step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13596 raw13596Labels = mixedMoment B node1073 node1073Labels := by
  calc
    mixedMoment B raw13596 raw13596Labels = mixedMoment B raw13596step0 raw13596step0Labels := by
      have hz : ∀ j, raw13596 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13596step0 = (fun i j => raw13596 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13596step0 raw13596; decide +kernel
      have hl : raw13596step0Labels = raw13596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13596 raw13596Labels permutation346 hz
    mixedMoment B raw13596step0 raw13596step0Labels = mixedMoment B raw13596step1 raw13596step1Labels := by
      have ha : raw13596step1 = (fun i j => raw13596step0 (permutation53 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13596step1 raw13596step0; decide +kernel
      have hl : raw13596step1Labels = raw13596step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13596step0 raw13596step0Labels permutation53 permutation3
    _ = mixedMoment B node1073 node1073Labels := by rfl

def raw13597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13597Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13597step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13597 raw13597Labels = mixedMoment B node2503 node2503Labels := by
  calc
    mixedMoment B raw13597 raw13597Labels = mixedMoment B raw13597step0 raw13597step0Labels := by
      have ha : raw13597step0 = (fun i j => raw13597 (permutation197 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13597step0 raw13597; decide +kernel
      have hl : raw13597step0Labels = raw13597Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13597 raw13597Labels permutation197 permutation3
    _ = mixedMoment B node2503 node2503Labels := by rfl

def raw13598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw13598Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13598step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13598step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13598step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13598step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13598step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13598 raw13598Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw13598 raw13598Labels = mixedMoment B raw13598step0 raw13598step0Labels := by
      have hz : ∀ j, raw13598 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13598step0 = (fun i j => raw13598 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13598step0 raw13598; decide +kernel
      have hl : raw13598step0Labels = raw13598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13598 raw13598Labels permutation520 hz
    mixedMoment B raw13598step0 raw13598step0Labels = mixedMoment B raw13598step1 raw13598step1Labels := by
      have hz : ∀ j, raw13598step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw13598step1 = (fun i j => raw13598step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw13598step1 raw13598step0; decide +kernel
      have hl : raw13598step1Labels = raw13598step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13598step0 raw13598step0Labels permutation80 hz
    mixedMoment B raw13598step1 raw13598step1Labels = mixedMoment B raw13598step2 raw13598step2Labels := by
      have ha : raw13598step2 = (fun i j => raw13598step1 (permutation13 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13598step2 raw13598step1; decide +kernel
      have hl : raw13598step2Labels = raw13598step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13598step1 raw13598step1Labels permutation13 permutation3
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw13599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw13599Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw13599step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13599step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13599 raw13599Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw13599 raw13599Labels = mixedMoment B raw13599step0 raw13599step0Labels := by
      have hz : ∀ j, raw13599 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13599step0 = (fun i j => raw13599 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13599step0 raw13599; decide +kernel
      have hl : raw13599step0Labels = raw13599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13599 raw13599Labels permutation346 hz
    mixedMoment B raw13599step0 raw13599step0Labels = mixedMoment B raw13599step1 raw13599step1Labels := by
      have ha : raw13599step1 = (fun i j => raw13599step0 (permutation53 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13599step1 raw13599step0; decide +kernel
      have hl : raw13599step1Labels = raw13599step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13599step0 raw13599step0Labels permutation53 permutation3
    _ = mixedMoment B node2684 node2684Labels := by rfl

def raw13600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13600Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13600step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13600 raw13600Labels = mixedMoment B node1034 node1034Labels := by
  calc
    mixedMoment B raw13600 raw13600Labels = mixedMoment B raw13600step0 raw13600step0Labels := by
      have ha : raw13600step0 = (fun i j => raw13600 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13600step0 raw13600; decide +kernel
      have hl : raw13600step0Labels = raw13600Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13600 raw13600Labels permutation170 permutation3
    _ = mixedMoment B node1034 node1034Labels := by rfl

def raw13601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13601Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13601step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13601 raw13601Labels = mixedMoment B node2589 node2589Labels := by
  calc
    mixedMoment B raw13601 raw13601Labels = mixedMoment B raw13601step0 raw13601step0Labels := by
      have ha : raw13601step0 = (fun i j => raw13601 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13601step0 raw13601; decide +kernel
      have hl : raw13601step0Labels = raw13601Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13601 raw13601Labels permutation170 permutation3
    _ = mixedMoment B node2589 node2589Labels := by rfl

def raw13602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw13602Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13602step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13602 raw13602Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw13602 raw13602Labels = mixedMoment B raw13602step0 raw13602step0Labels := by
      have hz : ∀ j, raw13602 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13602step0 = (fun i j => raw13602 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13602step0 raw13602; decide +kernel
      have hl : raw13602step0Labels = raw13602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13602 raw13602Labels permutation520 hz
    mixedMoment B raw13602step0 raw13602step0Labels = mixedMoment B raw13602step1 raw13602step1Labels := by
      have ha : raw13602step1 = (fun i j => raw13602step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13602step1 raw13602step0; decide +kernel
      have hl : raw13602step1Labels = raw13602step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13602step0 raw13602step0Labels permutation36 permutation3
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw13603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw13603Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13603step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13603 raw13603Labels = mixedMoment B node2671 node2671Labels := by
  calc
    mixedMoment B raw13603 raw13603Labels = mixedMoment B raw13603step0 raw13603step0Labels := by
      have ha : raw13603step0 = (fun i j => raw13603 (permutation246 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13603step0 raw13603; decide +kernel
      have hl : raw13603step0Labels = raw13603Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13603 raw13603Labels permutation246 permutation3
    _ = mixedMoment B node2671 node2671Labels := by rfl

def raw13604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13604Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13604step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13604step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13604 raw13604Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw13604 raw13604Labels = mixedMoment B raw13604step0 raw13604step0Labels := by
      have hz : ∀ j, raw13604 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13604step0 = (fun i j => raw13604 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13604step0 raw13604; decide +kernel
      have hl : raw13604step0Labels = raw13604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13604 raw13604Labels permutation346 hz
    mixedMoment B raw13604step0 raw13604step0Labels = mixedMoment B raw13604step1 raw13604step1Labels := by
      have ha : raw13604step1 = (fun i j => raw13604step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13604step1 raw13604step0; decide +kernel
      have hl : raw13604step1Labels = raw13604step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13604step0 raw13604step0Labels permutation37 permutation3
    _ = mixedMoment B node1035 node1035Labels := by rfl

def raw13605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13605Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13605step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13605step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13605 raw13605Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw13605 raw13605Labels = mixedMoment B raw13605step0 raw13605step0Labels := by
      have hz : ∀ j, raw13605 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13605step0 = (fun i j => raw13605 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13605step0 raw13605; decide +kernel
      have hl : raw13605step0Labels = raw13605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13605 raw13605Labels permutation346 hz
    mixedMoment B raw13605step0 raw13605step0Labels = mixedMoment B raw13605step1 raw13605step1Labels := by
      have ha : raw13605step1 = (fun i j => raw13605step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13605step1 raw13605step0; decide +kernel
      have hl : raw13605step1Labels = raw13605step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13605step0 raw13605step0Labels permutation37 permutation3
    _ = mixedMoment B node2590 node2590Labels := by rfl

def raw13606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13606Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13606step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13606 raw13606Labels = mixedMoment B node2477 node2477Labels := by
  calc
    mixedMoment B raw13606 raw13606Labels = mixedMoment B raw13606step0 raw13606step0Labels := by
      have ha : raw13606step0 = (fun i j => raw13606 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13606step0 raw13606; decide +kernel
      have hl : raw13606step0Labels = raw13606Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13606 raw13606Labels permutation181 permutation3
    _ = mixedMoment B node2477 node2477Labels := by rfl

def raw13607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw13607Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw13607step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw13607step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13607step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw13607step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13607 raw13607Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw13607 raw13607Labels = mixedMoment B raw13607step0 raw13607step0Labels := by
      have hz : ∀ j, raw13607 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13607step0 = (fun i j => raw13607 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13607step0 raw13607; decide +kernel
      have hl : raw13607step0Labels = raw13607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13607 raw13607Labels permutation520 hz
    mixedMoment B raw13607step0 raw13607step0Labels = mixedMoment B raw13607step1 raw13607step1Labels := by
      have hz : ∀ j, raw13607step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw13607step1 = (fun i j => raw13607step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw13607step1 raw13607step0; decide +kernel
      have hl : raw13607step1Labels = raw13607step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13607step0 raw13607step0Labels permutation80 hz
    mixedMoment B raw13607step1 raw13607step1Labels = mixedMoment B raw13607step2 raw13607step2Labels := by
      have ha : raw13607step2 = (fun i j => raw13607step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13607step2 raw13607step1; decide +kernel
      have hl : raw13607step2Labels = raw13607step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13607step1 raw13607step1Labels permutation9 permutation3
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw13608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw13608Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw13608step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13608step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13608 raw13608Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw13608 raw13608Labels = mixedMoment B raw13608step0 raw13608step0Labels := by
      have hz : ∀ j, raw13608 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13608step0 = (fun i j => raw13608 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13608step0 raw13608; decide +kernel
      have hl : raw13608step0Labels = raw13608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13608 raw13608Labels permutation346 hz
    mixedMoment B raw13608step0 raw13608step0Labels = mixedMoment B raw13608step1 raw13608step1Labels := by
      have ha : raw13608step1 = (fun i j => raw13608step0 (permutation51 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13608step1 raw13608step0; decide +kernel
      have hl : raw13608step1Labels = raw13608step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13608step0 raw13608step0Labels permutation51 permutation3
    _ = mixedMoment B node2672 node2672Labels := by rfl

def raw13609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw13609Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw13609step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13609step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13609 raw13609Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw13609 raw13609Labels = mixedMoment B raw13609step0 raw13609step0Labels := by
      have hz : ∀ j, raw13609 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13609step0 = (fun i j => raw13609 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13609step0 raw13609; decide +kernel
      have hl : raw13609step0Labels = raw13609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13609 raw13609Labels permutation346 hz
    mixedMoment B raw13609step0 raw13609step0Labels = mixedMoment B raw13609step1 raw13609step1Labels := by
      have ha : raw13609step1 = (fun i j => raw13609step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13609step1 raw13609step0; decide +kernel
      have hl : raw13609step1Labels = raw13609step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13609step0 raw13609step0Labels permutation36 permutation3
    _ = mixedMoment B node1035 node1035Labels := by rfl

def raw13610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw13610Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw13610step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13610step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13610 raw13610Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw13610 raw13610Labels = mixedMoment B raw13610step0 raw13610step0Labels := by
      have hz : ∀ j, raw13610 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13610step0 = (fun i j => raw13610 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13610step0 raw13610; decide +kernel
      have hl : raw13610step0Labels = raw13610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13610 raw13610Labels permutation346 hz
    mixedMoment B raw13610step0 raw13610step0Labels = mixedMoment B raw13610step1 raw13610step1Labels := by
      have ha : raw13610step1 = (fun i j => raw13610step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13610step1 raw13610step0; decide +kernel
      have hl : raw13610step1Labels = raw13610step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13610step0 raw13610step0Labels permutation36 permutation3
    _ = mixedMoment B node2590 node2590Labels := by rfl

def raw13611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw13611Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13611step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw13611step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13611 raw13611Labels = mixedMoment B node2477 node2477Labels := by
  calc
    mixedMoment B raw13611 raw13611Labels = mixedMoment B raw13611step0 raw13611step0Labels := by
      have ha : raw13611step0 = (fun i j => raw13611 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13611step0 raw13611; decide +kernel
      have hl : raw13611step0Labels = raw13611Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13611 raw13611Labels permutation180 permutation3
    _ = mixedMoment B node2477 node2477Labels := by rfl

def raw13612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw13612Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw13612step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13612step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13612 raw13612Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw13612 raw13612Labels = mixedMoment B raw13612step0 raw13612step0Labels := by
      have hz : ∀ j, raw13612 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13612step0 = (fun i j => raw13612 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13612step0 raw13612; decide +kernel
      have hl : raw13612step0Labels = raw13612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13612 raw13612Labels permutation346 hz
    mixedMoment B raw13612step0 raw13612step0Labels = mixedMoment B raw13612step1 raw13612step1Labels := by
      have ha : raw13612step1 = (fun i j => raw13612step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13612step1 raw13612step0; decide +kernel
      have hl : raw13612step1Labels = raw13612step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13612step0 raw13612step0Labels permutation50 permutation3
    _ = mixedMoment B node2672 node2672Labels := by rfl

def raw13613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13613Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13613step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13613step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13613 raw13613Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw13613 raw13613Labels = mixedMoment B raw13613step0 raw13613step0Labels := by
      have hz : ∀ j, raw13613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13613step0 = (fun i j => raw13613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13613step0 raw13613; decide +kernel
      have hl : raw13613step0Labels = raw13613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13613 raw13613Labels permutation346 hz
    mixedMoment B raw13613step0 raw13613step0Labels = mixedMoment B raw13613step1 raw13613step1Labels := by
      have ha : raw13613step1 = (fun i j => raw13613step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13613step1 raw13613step0; decide +kernel
      have hl : raw13613step1Labels = raw13613step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13613step0 raw13613step0Labels permutation32 permutation3
    _ = mixedMoment B node1044 node1044Labels := by rfl

def raw13614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13614Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13614step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13614step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13614 raw13614Labels = mixedMoment B node2599 node2599Labels := by
  calc
    mixedMoment B raw13614 raw13614Labels = mixedMoment B raw13614step0 raw13614step0Labels := by
      have hz : ∀ j, raw13614 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13614step0 = (fun i j => raw13614 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13614step0 raw13614; decide +kernel
      have hl : raw13614step0Labels = raw13614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13614 raw13614Labels permutation346 hz
    mixedMoment B raw13614step0 raw13614step0Labels = mixedMoment B raw13614step1 raw13614step1Labels := by
      have ha : raw13614step1 = (fun i j => raw13614step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13614step1 raw13614step0; decide +kernel
      have hl : raw13614step1Labels = raw13614step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13614step0 raw13614step0Labels permutation32 permutation3
    _ = mixedMoment B node2599 node2599Labels := by rfl

def raw13615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13615Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13615step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13615 raw13615Labels = mixedMoment B node2483 node2483Labels := by
  calc
    mixedMoment B raw13615 raw13615Labels = mixedMoment B raw13615step0 raw13615step0Labels := by
      have ha : raw13615step0 = (fun i j => raw13615 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13615step0 raw13615; decide +kernel
      have hl : raw13615step0Labels = raw13615Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13615 raw13615Labels permutation176 permutation3
    _ = mixedMoment B node2483 node2483Labels := by rfl

def raw13616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw13616Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13616step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13616step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13616step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13616step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13616step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13616 raw13616Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw13616 raw13616Labels = mixedMoment B raw13616step0 raw13616step0Labels := by
      have hz : ∀ j, raw13616 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13616step0 = (fun i j => raw13616 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13616step0 raw13616; decide +kernel
      have hl : raw13616step0Labels = raw13616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13616 raw13616Labels permutation520 hz
    mixedMoment B raw13616step0 raw13616step0Labels = mixedMoment B raw13616step1 raw13616step1Labels := by
      have hz : ∀ j, raw13616step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw13616step1 = (fun i j => raw13616step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw13616step1 raw13616step0; decide +kernel
      have hl : raw13616step1Labels = raw13616step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13616step0 raw13616step0Labels permutation80 hz
    mixedMoment B raw13616step1 raw13616step1Labels = mixedMoment B raw13616step2 raw13616step2Labels := by
      have ha : raw13616step2 = (fun i j => raw13616step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13616step2 raw13616step1; decide +kernel
      have hl : raw13616step2Labels = raw13616step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13616step1 raw13616step1Labels permutation8 permutation3
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw13617 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13617step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13617step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13617step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13617step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13617step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13617step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13617 raw13617Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw13617 raw13617Labels = mixedMoment B raw13617step0 raw13617step0Labels := by
      have hz : ∀ j, raw13617 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13617step0 = (fun i j => raw13617 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13617step0 raw13617; decide +kernel
      have hl : raw13617step0Labels = raw13617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13617 raw13617Labels permutation346 hz
    mixedMoment B raw13617step0 raw13617step0Labels = mixedMoment B raw13617step1 raw13617step1Labels := by
      have hz : ∀ j, raw13617step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13617step1 = (fun i j => raw13617step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13617step1 raw13617step0; decide +kernel
      have hl : raw13617step1Labels = raw13617step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13617step0 raw13617step0Labels permutation56 hz
    mixedMoment B raw13617step1 raw13617step1Labels = mixedMoment B raw13617step2 raw13617step2Labels := by
      have ha : raw13617step2 = (fun i j => raw13617step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13617step2 raw13617step1; decide +kernel
      have hl : raw13617step2Labels = raw13617step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13617step1 raw13617step1Labels permutation8 permutation7
    mixedMoment B raw13617step2 raw13617step2Labels = mixedMoment B raw13617step3 raw13617step3Labels := by
      have ha : raw13617step3 = raw13617step2 := by apply Matrix.ext; unfold raw13617step3 raw13617step2; decide +kernel
      have hl : raw13617step2Labels = labelEmbedding10 ∘ raw13617step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13617step2 raw13617step2Labels raw13617step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw13618 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13618step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13618step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13618 raw13618Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw13618 raw13618Labels = mixedMoment B raw13618step0 raw13618step0Labels := by
      have ha : raw13618step0 = (fun i j => raw13618 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13618step0 raw13618; decide +kernel
      have hl : raw13618step0Labels = raw13618Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13618 raw13618Labels permutation152 permutation7
    mixedMoment B raw13618step0 raw13618step0Labels = mixedMoment B raw13618step1 raw13618step1Labels := by
      have ha : raw13618step1 = raw13618step0 := by apply Matrix.ext; unfold raw13618step1 raw13618step0; decide +kernel
      have hl : raw13618step0Labels = labelEmbedding10 ∘ raw13618step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13618step0 raw13618step0Labels raw13618step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5256 node5256Labels := by rfl

def raw13619 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13619step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13619step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13619 raw13619Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw13619 raw13619Labels = mixedMoment B raw13619step0 raw13619step0Labels := by
      have hz : ∀ j, raw13619 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13619step0 = (fun i j => raw13619 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13619step0 raw13619; decide +kernel
      have hl : raw13619step0Labels = raw13619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13619 raw13619Labels permutation346 hz
    mixedMoment B raw13619step0 raw13619step0Labels = mixedMoment B raw13619step1 raw13619step1Labels := by
      have ha : raw13619step1 = (fun i j => raw13619step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13619step1 raw13619step0; decide +kernel
      have hl : raw13619step1Labels = raw13619step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13619step0 raw13619step0Labels permutation34 permutation7
    mixedMoment B raw13619step1 raw13619step1Labels = mixedMoment B raw13619step2 raw13619step2Labels := by
      have ha : raw13619step2 = raw13619step1 := by apply Matrix.ext; unfold raw13619step2 raw13619step1; decide +kernel
      have hl : raw13619step1Labels = labelEmbedding10 ∘ raw13619step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13619step1 raw13619step1Labels raw13619step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw13620 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13620step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13620step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13620step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13620step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13620 raw13620Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw13620 raw13620Labels = mixedMoment B raw13620step0 raw13620step0Labels := by
      have hz : ∀ j, raw13620 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13620step0 = (fun i j => raw13620 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13620step0 raw13620; decide +kernel
      have hl : raw13620step0Labels = raw13620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13620 raw13620Labels permutation346 hz
    mixedMoment B raw13620step0 raw13620step0Labels = mixedMoment B raw13620step1 raw13620step1Labels := by
      have ha : raw13620step1 = (fun i j => raw13620step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13620step1 raw13620step0; decide +kernel
      have hl : raw13620step1Labels = raw13620step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13620step0 raw13620step0Labels permutation32 permutation7
    mixedMoment B raw13620step1 raw13620step1Labels = mixedMoment B raw13620step2 raw13620step2Labels := by
      have ha : raw13620step2 = raw13620step1 := by apply Matrix.ext; unfold raw13620step2 raw13620step1; decide +kernel
      have hl : raw13620step1Labels = labelEmbedding10 ∘ raw13620step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13620step1 raw13620step1Labels raw13620step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw13621 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13621step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13621step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13621 raw13621Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw13621 raw13621Labels = mixedMoment B raw13621step0 raw13621step0Labels := by
      have hz : ∀ j, raw13621 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13621step0 = (fun i j => raw13621 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13621step0 raw13621; decide +kernel
      have hl : raw13621step0Labels = raw13621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13621 raw13621Labels permutation346 hz
    mixedMoment B raw13621step0 raw13621step0Labels = mixedMoment B raw13621step1 raw13621step1Labels := by
      have ha : raw13621step1 = (fun i j => raw13621step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13621step1 raw13621step0; decide +kernel
      have hl : raw13621step1Labels = raw13621step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13621step0 raw13621step0Labels permutation32 permutation7
    mixedMoment B raw13621step1 raw13621step1Labels = mixedMoment B raw13621step2 raw13621step2Labels := by
      have ha : raw13621step2 = raw13621step1 := by apply Matrix.ext; unfold raw13621step2 raw13621step1; decide +kernel
      have hl : raw13621step1Labels = labelEmbedding10 ∘ raw13621step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13621step1 raw13621step1Labels raw13621step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw13622 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13622step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw13622step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13622step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13622step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13622step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13622 raw13622Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw13622 raw13622Labels = mixedMoment B raw13622step0 raw13622step0Labels := by
      have hz : ∀ j, raw13622 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13622step0 = (fun i j => raw13622 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13622step0 raw13622; decide +kernel
      have hl : raw13622step0Labels = raw13622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13622 raw13622Labels permutation346 hz
    mixedMoment B raw13622step0 raw13622step0Labels = mixedMoment B raw13622step1 raw13622step1Labels := by
      have ha : raw13622step1 = (fun i j => raw13622step0 (permutation53 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13622step1 raw13622step0; decide +kernel
      have hl : raw13622step1Labels = raw13622step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13622step0 raw13622step0Labels permutation53 permutation4
    mixedMoment B raw13622step1 raw13622step1Labels = mixedMoment B raw13622step2 raw13622step2Labels := by
      have ha : raw13622step2 = -raw13622step1 := by apply Matrix.ext; change ∀ i j, raw13622step2 i j = -(raw13622step1 i j); unfold raw13622step2 raw13622step1; decide +kernel
      have hl : raw13622step2Labels = raw13622step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13622step2 raw13622step2Labels = mixedMoment B raw13622step3 raw13622step3Labels := by
      have ha : raw13622step3 = raw13622step2 := by apply Matrix.ext; unfold raw13622step3 raw13622step2; decide +kernel
      have hl : raw13622step2Labels = labelEmbedding7 ∘ raw13622step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13622step2 raw13622step2Labels raw13622step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

def raw13623 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13623step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13623step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13623step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13623 raw13623Labels = mixedMoment B node5263 node5263Labels := by
  calc
    mixedMoment B raw13623 raw13623Labels = mixedMoment B raw13623step0 raw13623step0Labels := by
      have ha : raw13623step0 = (fun i j => raw13623 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13623step0 raw13623; decide +kernel
      have hl : raw13623step0Labels = raw13623Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13623 raw13623Labels permutation180 permutation6
    mixedMoment B raw13623step0 raw13623step0Labels = mixedMoment B raw13623step1 raw13623step1Labels := by
      have ha : raw13623step1 = raw13623step0 := by apply Matrix.ext; unfold raw13623step1 raw13623step0; decide +kernel
      have hl : raw13623step0Labels = labelEmbedding9 ∘ raw13623step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13623step0 raw13623step0Labels raw13623step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5263 node5263Labels := by rfl

def raw13624 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13624step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13624step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13624step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13624step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13624 raw13624Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw13624 raw13624Labels = mixedMoment B raw13624step0 raw13624step0Labels := by
      have hz : ∀ j, raw13624 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13624step0 = (fun i j => raw13624 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13624step0 raw13624; decide +kernel
      have hl : raw13624step0Labels = raw13624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13624 raw13624Labels permutation346 hz
    mixedMoment B raw13624step0 raw13624step0Labels = mixedMoment B raw13624step1 raw13624step1Labels := by
      have ha : raw13624step1 = (fun i j => raw13624step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13624step1 raw13624step0; decide +kernel
      have hl : raw13624step1Labels = raw13624step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13624step0 raw13624step0Labels permutation36 permutation6
    mixedMoment B raw13624step1 raw13624step1Labels = mixedMoment B raw13624step2 raw13624step2Labels := by
      have ha : raw13624step2 = raw13624step1 := by apply Matrix.ext; unfold raw13624step2 raw13624step1; decide +kernel
      have hl : raw13624step1Labels = labelEmbedding9 ∘ raw13624step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13624step1 raw13624step1Labels raw13624step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw13625 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13625step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13625step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13625step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13625step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13625step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13625 raw13625Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw13625 raw13625Labels = mixedMoment B raw13625step0 raw13625step0Labels := by
      have hz : ∀ j, raw13625 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13625step0 = (fun i j => raw13625 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13625step0 raw13625; decide +kernel
      have hl : raw13625step0Labels = raw13625Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13625 raw13625Labels permutation346 hz
    mixedMoment B raw13625step0 raw13625step0Labels = mixedMoment B raw13625step1 raw13625step1Labels := by
      have ha : raw13625step1 = (fun i j => raw13625step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13625step1 raw13625step0; decide +kernel
      have hl : raw13625step1Labels = raw13625step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13625step0 raw13625step0Labels permutation37 permutation6
    mixedMoment B raw13625step1 raw13625step1Labels = mixedMoment B raw13625step2 raw13625step2Labels := by
      have ha : raw13625step2 = raw13625step1 := by apply Matrix.ext; unfold raw13625step2 raw13625step1; decide +kernel
      have hl : raw13625step1Labels = labelEmbedding9 ∘ raw13625step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13625step1 raw13625step1Labels raw13625step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw13626 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13626step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw13626step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw13626step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13626 raw13626Labels = mixedMoment B node5279 node5279Labels := by
  calc
    mixedMoment B raw13626 raw13626Labels = mixedMoment B raw13626step0 raw13626step0Labels := by
      have hz : ∀ j, raw13626 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13626step0 = (fun i j => raw13626 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13626step0 raw13626; decide +kernel
      have hl : raw13626step0Labels = raw13626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13626 raw13626Labels permutation346 hz
    mixedMoment B raw13626step0 raw13626step0Labels = mixedMoment B raw13626step1 raw13626step1Labels := by
      have ha : raw13626step1 = (fun i j => raw13626step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13626step1 raw13626step0; decide +kernel
      have hl : raw13626step1Labels = raw13626step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13626step0 raw13626step0Labels permutation144 permutation3
    mixedMoment B raw13626step1 raw13626step1Labels = mixedMoment B raw13626step2 raw13626step2Labels := by
      have ha : raw13626step2 = raw13626step1 := by apply Matrix.ext; unfold raw13626step2 raw13626step1; decide +kernel
      have hl : raw13626step1Labels = labelEmbedding6 ∘ raw13626step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13626step1 raw13626step1Labels raw13626step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5279 node5279Labels := by rfl

def raw13627 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13627step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13627step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13627step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13627step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13627step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13627 raw13627Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw13627 raw13627Labels = mixedMoment B raw13627step0 raw13627step0Labels := by
      have ha : raw13627step0 = (fun i j => raw13627 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13627step0 raw13627; decide +kernel
      have hl : raw13627step0Labels = raw13627Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13627 raw13627Labels permutation246 permutation4
    mixedMoment B raw13627step0 raw13627step0Labels = mixedMoment B raw13627step1 raw13627step1Labels := by
      have ha : raw13627step1 = -raw13627step0 := by apply Matrix.ext; change ∀ i j, raw13627step1 i j = -(raw13627step0 i j); unfold raw13627step1 raw13627step0; decide +kernel
      have hl : raw13627step1Labels = raw13627step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13627step1 raw13627step1Labels = mixedMoment B raw13627step2 raw13627step2Labels := by
      have ha : raw13627step2 = raw13627step1 := by apply Matrix.ext; unfold raw13627step2 raw13627step1; decide +kernel
      have hl : raw13627step1Labels = labelEmbedding7 ∘ raw13627step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13627step1 raw13627step1Labels raw13627step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4864 node4864Labels := by rfl

def raw13628 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13628step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13628step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13628step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13628step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13628step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13628 raw13628Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw13628 raw13628Labels = mixedMoment B raw13628step0 raw13628step0Labels := by
      have hz : ∀ j, raw13628 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13628step0 = (fun i j => raw13628 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13628step0 raw13628; decide +kernel
      have hl : raw13628step0Labels = raw13628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13628 raw13628Labels permutation265 hz
    mixedMoment B raw13628step0 raw13628step0Labels = mixedMoment B raw13628step1 raw13628step1Labels := by
      have ha : raw13628step1 = (fun i j => raw13628step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13628step1 raw13628step0; decide +kernel
      have hl : raw13628step1Labels = raw13628step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13628step0 raw13628step0Labels permutation36 permutation6
    mixedMoment B raw13628step1 raw13628step1Labels = mixedMoment B raw13628step2 raw13628step2Labels := by
      have ha : raw13628step2 = raw13628step1 := by apply Matrix.ext; unfold raw13628step2 raw13628step1; decide +kernel
      have hl : raw13628step1Labels = labelEmbedding9 ∘ raw13628step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13628step1 raw13628step1Labels raw13628step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw13629 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13629Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw13629step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13629step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw13629step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13629 raw13629Labels = mixedMoment B node5278 node5278Labels := by
  calc
    mixedMoment B raw13629 raw13629Labels = mixedMoment B raw13629step0 raw13629step0Labels := by
      have ha : raw13629step0 = (fun i j => raw13629 (permutation659 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13629step0 raw13629; decide +kernel
      have hl : raw13629step0Labels = raw13629Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13629 raw13629Labels permutation659 permutation3
    mixedMoment B raw13629step0 raw13629step0Labels = mixedMoment B raw13629step1 raw13629step1Labels := by
      have ha : raw13629step1 = raw13629step0 := by apply Matrix.ext; unfold raw13629step1 raw13629step0; decide +kernel
      have hl : raw13629step0Labels = labelEmbedding6 ∘ raw13629step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13629step0 raw13629step0Labels raw13629step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5278 node5278Labels := by rfl

def raw13630 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13630Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13630step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13630step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13630step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13630step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13630step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13630 raw13630Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw13630 raw13630Labels = mixedMoment B raw13630step0 raw13630step0Labels := by
      have hz : ∀ j, raw13630 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13630step0 = (fun i j => raw13630 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13630step0 raw13630; decide +kernel
      have hl : raw13630step0Labels = raw13630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13630 raw13630Labels permutation346 hz
    mixedMoment B raw13630step0 raw13630step0Labels = mixedMoment B raw13630step1 raw13630step1Labels := by
      have ha : raw13630step1 = (fun i j => raw13630step0 (permutation51 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13630step1 raw13630step0; decide +kernel
      have hl : raw13630step1Labels = raw13630step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13630step0 raw13630step0Labels permutation51 permutation4
    mixedMoment B raw13630step1 raw13630step1Labels = mixedMoment B raw13630step2 raw13630step2Labels := by
      have ha : raw13630step2 = -raw13630step1 := by apply Matrix.ext; change ∀ i j, raw13630step2 i j = -(raw13630step1 i j); unfold raw13630step2 raw13630step1; decide +kernel
      have hl : raw13630step2Labels = raw13630step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13630step2 raw13630step2Labels = mixedMoment B raw13630step3 raw13630step3Labels := by
      have ha : raw13630step3 = raw13630step2 := by apply Matrix.ext; unfold raw13630step3 raw13630step2; decide +kernel
      have hl : raw13630step2Labels = labelEmbedding7 ∘ raw13630step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13630step2 raw13630step2Labels raw13630step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw13631 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13631Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13631step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13631step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13631step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13631step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13631step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13631step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13631step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13631 raw13631Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw13631 raw13631Labels = mixedMoment B raw13631step0 raw13631step0Labels := by
      have hz : ∀ j, raw13631 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13631step0 = (fun i j => raw13631 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13631step0 raw13631; decide +kernel
      have hl : raw13631step0Labels = raw13631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13631 raw13631Labels permutation346 hz
    mixedMoment B raw13631step0 raw13631step0Labels = mixedMoment B raw13631step1 raw13631step1Labels := by
      have hz : ∀ j, raw13631step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13631step1 = (fun i j => raw13631step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13631step1 raw13631step0; decide +kernel
      have hl : raw13631step1Labels = raw13631step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13631step0 raw13631step0Labels permutation56 hz
    mixedMoment B raw13631step1 raw13631step1Labels = mixedMoment B raw13631step2 raw13631step2Labels := by
      have ha : raw13631step2 = (fun i j => raw13631step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13631step2 raw13631step1; decide +kernel
      have hl : raw13631step2Labels = raw13631step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13631step1 raw13631step1Labels permutation13 permutation6
    mixedMoment B raw13631step2 raw13631step2Labels = mixedMoment B raw13631step3 raw13631step3Labels := by
      have ha : raw13631step3 = raw13631step2 := by apply Matrix.ext; unfold raw13631step3 raw13631step2; decide +kernel
      have hl : raw13631step2Labels = labelEmbedding9 ∘ raw13631step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13631step2 raw13631step2Labels raw13631step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw13632 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13632Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13632step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13632step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13632 raw13632Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw13632 raw13632Labels = mixedMoment B raw13632step0 raw13632step0Labels := by
      have ha : raw13632step0 = (fun i j => raw13632 (permutation181 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13632step0 raw13632; decide +kernel
      have hl : raw13632step0Labels = raw13632Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13632 raw13632Labels permutation181 permutation6
    mixedMoment B raw13632step0 raw13632step0Labels = mixedMoment B raw13632step1 raw13632step1Labels := by
      have ha : raw13632step1 = raw13632step0 := by apply Matrix.ext; unfold raw13632step1 raw13632step0; decide +kernel
      have hl : raw13632step0Labels = labelEmbedding9 ∘ raw13632step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13632step0 raw13632step0Labels raw13632step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

def raw13633 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13633Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13633step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13633step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13633step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13633step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13633 raw13633Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw13633 raw13633Labels = mixedMoment B raw13633step0 raw13633step0Labels := by
      have hz : ∀ j, raw13633 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13633step0 = (fun i j => raw13633 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13633step0 raw13633; decide +kernel
      have hl : raw13633step0Labels = raw13633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13633 raw13633Labels permutation346 hz
    mixedMoment B raw13633step0 raw13633step0Labels = mixedMoment B raw13633step1 raw13633step1Labels := by
      have ha : raw13633step1 = (fun i j => raw13633step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13633step1 raw13633step0; decide +kernel
      have hl : raw13633step1Labels = raw13633step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13633step0 raw13633step0Labels permutation37 permutation6
    mixedMoment B raw13633step1 raw13633step1Labels = mixedMoment B raw13633step2 raw13633step2Labels := by
      have ha : raw13633step2 = raw13633step1 := by apply Matrix.ext; unfold raw13633step2 raw13633step1; decide +kernel
      have hl : raw13633step1Labels = labelEmbedding9 ∘ raw13633step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13633step1 raw13633step1Labels raw13633step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw13634 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13634Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13634step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw13634step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw13634step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13634 raw13634Labels = mixedMoment B node5288 node5288Labels := by
  calc
    mixedMoment B raw13634 raw13634Labels = mixedMoment B raw13634step0 raw13634step0Labels := by
      have hz : ∀ j, raw13634 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13634step0 = (fun i j => raw13634 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13634step0 raw13634; decide +kernel
      have hl : raw13634step0Labels = raw13634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13634 raw13634Labels permutation346 hz
    mixedMoment B raw13634step0 raw13634step0Labels = mixedMoment B raw13634step1 raw13634step1Labels := by
      have ha : raw13634step1 = (fun i j => raw13634step0 (permutation146 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13634step1 raw13634step0; decide +kernel
      have hl : raw13634step1Labels = raw13634step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13634step0 raw13634step0Labels permutation146 permutation3
    mixedMoment B raw13634step1 raw13634step1Labels = mixedMoment B raw13634step2 raw13634step2Labels := by
      have ha : raw13634step2 = raw13634step1 := by apply Matrix.ext; unfold raw13634step2 raw13634step1; decide +kernel
      have hl : raw13634step1Labels = labelEmbedding6 ∘ raw13634step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13634step1 raw13634step1Labels raw13634step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5288 node5288Labels := by rfl

def raw13635 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13635step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13635step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13635step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13635step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13635step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13635 raw13635Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw13635 raw13635Labels = mixedMoment B raw13635step0 raw13635step0Labels := by
      have hz : ∀ j, raw13635 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13635step0 = (fun i j => raw13635 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13635step0 raw13635; decide +kernel
      have hl : raw13635step0Labels = raw13635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13635 raw13635Labels permutation346 hz
    mixedMoment B raw13635step0 raw13635step0Labels = mixedMoment B raw13635step1 raw13635step1Labels := by
      have ha : raw13635step1 = (fun i j => raw13635step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13635step1 raw13635step0; decide +kernel
      have hl : raw13635step1Labels = raw13635step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13635step0 raw13635step0Labels permutation50 permutation4
    mixedMoment B raw13635step1 raw13635step1Labels = mixedMoment B raw13635step2 raw13635step2Labels := by
      have ha : raw13635step2 = -raw13635step1 := by apply Matrix.ext; change ∀ i j, raw13635step2 i j = -(raw13635step1 i j); unfold raw13635step2 raw13635step1; decide +kernel
      have hl : raw13635step2Labels = raw13635step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13635step2 raw13635step2Labels = mixedMoment B raw13635step3 raw13635step3Labels := by
      have ha : raw13635step3 = raw13635step2 := by apply Matrix.ext; unfold raw13635step3 raw13635step2; decide +kernel
      have hl : raw13635step2Labels = labelEmbedding7 ∘ raw13635step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13635step2 raw13635step2Labels raw13635step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw13636 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13636step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13636step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13636step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13636step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13636step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13636 raw13636Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw13636 raw13636Labels = mixedMoment B raw13636step0 raw13636step0Labels := by
      have hz : ∀ j, raw13636 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13636step0 = (fun i j => raw13636 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13636step0 raw13636; decide +kernel
      have hl : raw13636step0Labels = raw13636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13636 raw13636Labels permutation346 hz
    mixedMoment B raw13636step0 raw13636step0Labels = mixedMoment B raw13636step1 raw13636step1Labels := by
      have hz : ∀ j, raw13636step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13636step1 = (fun i j => raw13636step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13636step1 raw13636step0; decide +kernel
      have hl : raw13636step1Labels = raw13636step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13636step0 raw13636step0Labels permutation56 hz
    mixedMoment B raw13636step1 raw13636step1Labels = mixedMoment B raw13636step2 raw13636step2Labels := by
      have ha : raw13636step2 = (fun i j => raw13636step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13636step2 raw13636step1; decide +kernel
      have hl : raw13636step2Labels = raw13636step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13636step1 raw13636step1Labels permutation12 permutation6
    mixedMoment B raw13636step2 raw13636step2Labels = mixedMoment B raw13636step3 raw13636step3Labels := by
      have ha : raw13636step3 = raw13636step2 := by apply Matrix.ext; unfold raw13636step3 raw13636step2; decide +kernel
      have hl : raw13636step2Labels = labelEmbedding9 ∘ raw13636step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13636step2 raw13636step2Labels raw13636step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw13637 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13637Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13637step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13637step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13637step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13637step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13637 raw13637Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw13637 raw13637Labels = mixedMoment B raw13637step0 raw13637step0Labels := by
      have ha : raw13637step0 = (fun i j => raw13637 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13637step0 raw13637; decide +kernel
      have hl : raw13637step0Labels = raw13637Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13637 raw13637Labels permutation180 permutation6
    mixedMoment B raw13637step0 raw13637step0Labels = mixedMoment B raw13637step1 raw13637step1Labels := by
      have ha : raw13637step1 = raw13637step0 := by apply Matrix.ext; unfold raw13637step1 raw13637step0; decide +kernel
      have hl : raw13637step0Labels = labelEmbedding9 ∘ raw13637step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13637step0 raw13637step0Labels raw13637step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

def raw13638 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13638Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13638step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13638step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13638step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13638step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13638 raw13638Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw13638 raw13638Labels = mixedMoment B raw13638step0 raw13638step0Labels := by
      have hz : ∀ j, raw13638 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13638step0 = (fun i j => raw13638 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13638step0 raw13638; decide +kernel
      have hl : raw13638step0Labels = raw13638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13638 raw13638Labels permutation346 hz
    mixedMoment B raw13638step0 raw13638step0Labels = mixedMoment B raw13638step1 raw13638step1Labels := by
      have ha : raw13638step1 = (fun i j => raw13638step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13638step1 raw13638step0; decide +kernel
      have hl : raw13638step1Labels = raw13638step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13638step0 raw13638step0Labels permutation36 permutation6
    mixedMoment B raw13638step1 raw13638step1Labels = mixedMoment B raw13638step2 raw13638step2Labels := by
      have ha : raw13638step2 = raw13638step1 := by apply Matrix.ext; unfold raw13638step2 raw13638step1; decide +kernel
      have hl : raw13638step1Labels = labelEmbedding9 ∘ raw13638step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13638step1 raw13638step1Labels raw13638step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw13639 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw13639Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw13639step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw13639step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13639step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw13639step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13639 raw13639Labels = mixedMoment B node5288 node5288Labels := by
  calc
    mixedMoment B raw13639 raw13639Labels = mixedMoment B raw13639step0 raw13639step0Labels := by
      have hz : ∀ j, raw13639 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13639step0 = (fun i j => raw13639 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13639step0 raw13639; decide +kernel
      have hl : raw13639step0Labels = raw13639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13639 raw13639Labels permutation346 hz
    mixedMoment B raw13639step0 raw13639step0Labels = mixedMoment B raw13639step1 raw13639step1Labels := by
      have ha : raw13639step1 = (fun i j => raw13639step0 (permutation140 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13639step1 raw13639step0; decide +kernel
      have hl : raw13639step1Labels = raw13639step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13639step0 raw13639step0Labels permutation140 permutation3
    mixedMoment B raw13639step1 raw13639step1Labels = mixedMoment B raw13639step2 raw13639step2Labels := by
      have ha : raw13639step2 = raw13639step1 := by apply Matrix.ext; unfold raw13639step2 raw13639step1; decide +kernel
      have hl : raw13639step1Labels = labelEmbedding6 ∘ raw13639step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13639step1 raw13639step1Labels raw13639step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5288 node5288Labels := by rfl

def raw13640 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13640Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13640step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13640step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13640step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13640step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13640step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13640step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13640 raw13640Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw13640 raw13640Labels = mixedMoment B raw13640step0 raw13640step0Labels := by
      have hz : ∀ j, raw13640 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13640step0 = (fun i j => raw13640 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13640step0 raw13640; decide +kernel
      have hl : raw13640step0Labels = raw13640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13640 raw13640Labels permutation346 hz
    mixedMoment B raw13640step0 raw13640step0Labels = mixedMoment B raw13640step1 raw13640step1Labels := by
      have ha : raw13640step1 = (fun i j => raw13640step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13640step1 raw13640step0; decide +kernel
      have hl : raw13640step1Labels = raw13640step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13640step0 raw13640step0Labels permutation50 permutation4
    mixedMoment B raw13640step1 raw13640step1Labels = mixedMoment B raw13640step2 raw13640step2Labels := by
      have ha : raw13640step2 = -raw13640step1 := by apply Matrix.ext; change ∀ i j, raw13640step2 i j = -(raw13640step1 i j); unfold raw13640step2 raw13640step1; decide +kernel
      have hl : raw13640step2Labels = raw13640step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13640step2 raw13640step2Labels = mixedMoment B raw13640step3 raw13640step3Labels := by
      have ha : raw13640step3 = raw13640step2 := by apply Matrix.ext; unfold raw13640step3 raw13640step2; decide +kernel
      have hl : raw13640step2Labels = labelEmbedding7 ∘ raw13640step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13640step2 raw13640step2Labels raw13640step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4893 node4893Labels := by rfl

def raw13641 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13641step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13641step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13641step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13641step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13641step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13641step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13641 raw13641Labels = mixedMoment B node5307 node5307Labels := by
  calc
    mixedMoment B raw13641 raw13641Labels = mixedMoment B raw13641step0 raw13641step0Labels := by
      have hz : ∀ j, raw13641 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13641step0 = (fun i j => raw13641 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13641step0 raw13641; decide +kernel
      have hl : raw13641step0Labels = raw13641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13641 raw13641Labels permutation346 hz
    mixedMoment B raw13641step0 raw13641step0Labels = mixedMoment B raw13641step1 raw13641step1Labels := by
      have hz : ∀ j, raw13641step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13641step1 = (fun i j => raw13641step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13641step1 raw13641step0; decide +kernel
      have hl : raw13641step1Labels = raw13641step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13641step0 raw13641step0Labels permutation56 hz
    mixedMoment B raw13641step1 raw13641step1Labels = mixedMoment B raw13641step2 raw13641step2Labels := by
      have ha : raw13641step2 = (fun i j => raw13641step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13641step2 raw13641step1; decide +kernel
      have hl : raw13641step2Labels = raw13641step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13641step1 raw13641step1Labels permutation12 permutation6
    mixedMoment B raw13641step2 raw13641step2Labels = mixedMoment B raw13641step3 raw13641step3Labels := by
      have ha : raw13641step3 = raw13641step2 := by apply Matrix.ext; unfold raw13641step3 raw13641step2; decide +kernel
      have hl : raw13641step2Labels = labelEmbedding9 ∘ raw13641step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13641step2 raw13641step2Labels raw13641step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5307 node5307Labels := by rfl

def raw13642 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13642Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13642step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13642step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13642step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13642 raw13642Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw13642 raw13642Labels = mixedMoment B raw13642step0 raw13642step0Labels := by
      have ha : raw13642step0 = (fun i j => raw13642 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13642step0 raw13642; decide +kernel
      have hl : raw13642step0Labels = raw13642Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13642 raw13642Labels permutation180 permutation6
    mixedMoment B raw13642step0 raw13642step0Labels = mixedMoment B raw13642step1 raw13642step1Labels := by
      have ha : raw13642step1 = raw13642step0 := by apply Matrix.ext; unfold raw13642step1 raw13642step0; decide +kernel
      have hl : raw13642step0Labels = labelEmbedding9 ∘ raw13642step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13642step0 raw13642step0Labels raw13642step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw13643 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13643Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13643step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13643step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13643step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13643step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13643step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13643 raw13643Labels = mixedMoment B node3120 node3120Labels := by
  calc
    mixedMoment B raw13643 raw13643Labels = mixedMoment B raw13643step0 raw13643step0Labels := by
      have hz : ∀ j, raw13643 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13643step0 = (fun i j => raw13643 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13643step0 raw13643; decide +kernel
      have hl : raw13643step0Labels = raw13643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13643 raw13643Labels permutation346 hz
    mixedMoment B raw13643step0 raw13643step0Labels = mixedMoment B raw13643step1 raw13643step1Labels := by
      have hz : ∀ j, raw13643step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13643step1 = (fun i j => raw13643step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13643step1 raw13643step0; decide +kernel
      have hl : raw13643step1Labels = raw13643step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13643step0 raw13643step0Labels permutation56 hz
    mixedMoment B raw13643step1 raw13643step1Labels = mixedMoment B raw13643step2 raw13643step2Labels := by
      have ha : raw13643step2 = (fun i j => raw13643step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13643step2 raw13643step1; decide +kernel
      have hl : raw13643step2Labels = raw13643step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13643step1 raw13643step1Labels permutation12 permutation6
    _ = mixedMoment B node3120 node3120Labels := by rfl

def raw13644 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13644Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13644 raw13644Labels = mixedMoment B node3085 node3085Labels := by
  calc
    mixedMoment B raw13644 raw13644Labels = mixedMoment B raw13644step0 raw13644step0Labels := by
      have ha : raw13644step0 = (fun i j => raw13644 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13644step0 raw13644; decide +kernel
      have hl : raw13644step0Labels = raw13644Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13644 raw13644Labels permutation180 permutation6
    _ = mixedMoment B node3085 node3085Labels := by rfl

def raw13645 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13645Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13645step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13645 raw13645Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw13645 raw13645Labels = mixedMoment B raw13645step0 raw13645step0Labels := by
      have hz : ∀ j, raw13645 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13645step0 = (fun i j => raw13645 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13645step0 raw13645; decide +kernel
      have hl : raw13645step0Labels = raw13645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13645 raw13645Labels permutation346 hz
    mixedMoment B raw13645step0 raw13645step0Labels = mixedMoment B raw13645step1 raw13645step1Labels := by
      have ha : raw13645step1 = (fun i j => raw13645step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13645step1 raw13645step0; decide +kernel
      have hl : raw13645step1Labels = raw13645step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13645step0 raw13645step0Labels permutation36 permutation6
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw13646 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13646Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13646step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13646 raw13646Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw13646 raw13646Labels = mixedMoment B raw13646step0 raw13646step0Labels := by
      have hz : ∀ j, raw13646 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13646step0 = (fun i j => raw13646 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13646step0 raw13646; decide +kernel
      have hl : raw13646step0Labels = raw13646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13646 raw13646Labels permutation346 hz
    mixedMoment B raw13646step0 raw13646step0Labels = mixedMoment B raw13646step1 raw13646step1Labels := by
      have ha : raw13646step1 = (fun i j => raw13646step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13646step1 raw13646step0; decide +kernel
      have hl : raw13646step1Labels = raw13646step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13646step0 raw13646step0Labels permutation37 permutation6
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw13647 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13647Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13647step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13647 raw13647Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw13647 raw13647Labels = mixedMoment B raw13647step0 raw13647step0Labels := by
      have hz : ∀ j, raw13647 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13647step0 = (fun i j => raw13647 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13647step0 raw13647; decide +kernel
      have hl : raw13647step0Labels = raw13647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13647 raw13647Labels permutation346 hz
    mixedMoment B raw13647step0 raw13647step0Labels = mixedMoment B raw13647step1 raw13647step1Labels := by
      have ha : raw13647step1 = (fun i j => raw13647step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13647step1 raw13647step0; decide +kernel
      have hl : raw13647step1Labels = raw13647step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13647step0 raw13647step0Labels permutation145 permutation3
    _ = mixedMoment B node2754 node2754Labels := by rfl

def raw13648 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13648step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13648 raw13648Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw13648 raw13648Labels = mixedMoment B raw13648step0 raw13648step0Labels := by
      have hz : ∀ j, raw13648 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13648step0 = (fun i j => raw13648 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13648step0 raw13648; decide +kernel
      have hl : raw13648step0Labels = raw13648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13648 raw13648Labels permutation346 hz
    mixedMoment B raw13648step0 raw13648step0Labels = mixedMoment B raw13648step1 raw13648step1Labels := by
      have ha : raw13648step1 = (fun i j => raw13648step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13648step1 raw13648step0; decide +kernel
      have hl : raw13648step1Labels = raw13648step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13648step0 raw13648step0Labels permutation36 permutation6
    _ = mixedMoment B node2275 node2275Labels := by rfl

def raw13649 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13649step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13649 raw13649Labels = mixedMoment B node2728 node2728Labels := by
  calc
    mixedMoment B raw13649 raw13649Labels = mixedMoment B raw13649step0 raw13649step0Labels := by
      have ha : raw13649step0 = (fun i j => raw13649 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13649step0 raw13649; decide +kernel
      have hl : raw13649step0Labels = raw13649Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13649 raw13649Labels permutation180 permutation6
    _ = mixedMoment B node2728 node2728Labels := by rfl

def raw13650 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13650step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13650step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13650 raw13650Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw13650 raw13650Labels = mixedMoment B raw13650step0 raw13650step0Labels := by
      have hz : ∀ j, raw13650 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13650step0 = (fun i j => raw13650 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13650step0 raw13650; decide +kernel
      have hl : raw13650step0Labels = raw13650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13650 raw13650Labels permutation346 hz
    mixedMoment B raw13650step0 raw13650step0Labels = mixedMoment B raw13650step1 raw13650step1Labels := by
      have ha : raw13650step1 = (fun i j => raw13650step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13650step1 raw13650step0; decide +kernel
      have hl : raw13650step1Labels = raw13650step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13650step0 raw13650step0Labels permutation36 permutation6
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw13651 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13651Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13651step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13651step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13651 raw13651Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw13651 raw13651Labels = mixedMoment B raw13651step0 raw13651step0Labels := by
      have hz : ∀ j, raw13651 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13651step0 = (fun i j => raw13651 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13651step0 raw13651; decide +kernel
      have hl : raw13651step0Labels = raw13651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13651 raw13651Labels permutation346 hz
    mixedMoment B raw13651step0 raw13651step0Labels = mixedMoment B raw13651step1 raw13651step1Labels := by
      have ha : raw13651step1 = (fun i j => raw13651step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13651step1 raw13651step0; decide +kernel
      have hl : raw13651step1Labels = raw13651step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13651step0 raw13651step0Labels permutation37 permutation6
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw13652 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13652Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13652step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw13652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13652 raw13652Labels = mixedMoment B node2748 node2748Labels := by
  calc
    mixedMoment B raw13652 raw13652Labels = mixedMoment B raw13652step0 raw13652step0Labels := by
      have hz : ∀ j, raw13652 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13652step0 = (fun i j => raw13652 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13652step0 raw13652; decide +kernel
      have hl : raw13652step0Labels = raw13652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13652 raw13652Labels permutation346 hz
    mixedMoment B raw13652step0 raw13652step0Labels = mixedMoment B raw13652step1 raw13652step1Labels := by
      have ha : raw13652step1 = (fun i j => raw13652step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13652step1 raw13652step0; decide +kernel
      have hl : raw13652step1Labels = raw13652step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13652step0 raw13652step0Labels permutation144 permutation3
    _ = mixedMoment B node2748 node2748Labels := by rfl

def raw13653 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13653Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13653step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13653 raw13653Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw13653 raw13653Labels = mixedMoment B raw13653step0 raw13653step0Labels := by
      have ha : raw13653step0 = (fun i j => raw13653 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13653step0 raw13653; decide +kernel
      have hl : raw13653step0Labels = raw13653Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13653 raw13653Labels permutation156 permutation6
    _ = mixedMoment B node2241 node2241Labels := by rfl

def raw13654 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13654Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13654step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13654 raw13654Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw13654 raw13654Labels = mixedMoment B raw13654step0 raw13654step0Labels := by
      have hz : ∀ j, raw13654 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13654step0 = (fun i j => raw13654 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13654step0 raw13654; decide +kernel
      have hl : raw13654step0Labels = raw13654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13654 raw13654Labels permutation265 hz
    mixedMoment B raw13654step0 raw13654step0Labels = mixedMoment B raw13654step1 raw13654step1Labels := by
      have ha : raw13654step1 = (fun i j => raw13654step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13654step1 raw13654step0; decide +kernel
      have hl : raw13654step1Labels = raw13654step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13654step0 raw13654step0Labels permutation36 permutation6
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw13655 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13655Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13655step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13655 raw13655Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw13655 raw13655Labels = mixedMoment B raw13655step0 raw13655step0Labels := by
      have ha : raw13655step0 = (fun i j => raw13655 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13655step0 raw13655; decide +kernel
      have hl : raw13655step0Labels = raw13655Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13655 raw13655Labels permutation156 permutation6
    _ = mixedMoment B node2750 node2750Labels := by rfl

def raw13656 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13656Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13656step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13656 raw13656Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw13656 raw13656Labels = mixedMoment B raw13656step0 raw13656step0Labels := by
      have ha : raw13656step0 = (fun i j => raw13656 (permutation157 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13656step0 raw13656; decide +kernel
      have hl : raw13656step0Labels = raw13656Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13656 raw13656Labels permutation157 permutation6
    _ = mixedMoment B node2750 node2750Labels := by rfl

def raw13657 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13657Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw13657step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13657 raw13657Labels = mixedMoment B node2747 node2747Labels := by
  calc
    mixedMoment B raw13657 raw13657Labels = mixedMoment B raw13657step0 raw13657step0Labels := by
      have ha : raw13657step0 = (fun i j => raw13657 (permutation659 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13657step0 raw13657; decide +kernel
      have hl : raw13657step0Labels = raw13657Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13657 raw13657Labels permutation659 permutation3
    _ = mixedMoment B node2747 node2747Labels := by rfl

def raw13658 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13658Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13658step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13658step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13658step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13658 raw13658Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw13658 raw13658Labels = mixedMoment B raw13658step0 raw13658step0Labels := by
      have hz : ∀ j, raw13658 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13658step0 = (fun i j => raw13658 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13658step0 raw13658; decide +kernel
      have hl : raw13658step0Labels = raw13658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13658 raw13658Labels permutation346 hz
    mixedMoment B raw13658step0 raw13658step0Labels = mixedMoment B raw13658step1 raw13658step1Labels := by
      have ha : raw13658step1 = (fun i j => raw13658step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13658step1 raw13658step0; decide +kernel
      have hl : raw13658step1Labels = raw13658step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13658step0 raw13658step0Labels permutation37 permutation6
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw13659 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13659Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13659step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13659step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13659step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13659step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13659 raw13659Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw13659 raw13659Labels = mixedMoment B raw13659step0 raw13659step0Labels := by
      have hz : ∀ j, raw13659 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13659step0 = (fun i j => raw13659 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13659step0 raw13659; decide +kernel
      have hl : raw13659step0Labels = raw13659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13659 raw13659Labels permutation346 hz
    mixedMoment B raw13659step0 raw13659step0Labels = mixedMoment B raw13659step1 raw13659step1Labels := by
      have hz : ∀ j, raw13659step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13659step1 = (fun i j => raw13659step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13659step1 raw13659step0; decide +kernel
      have hl : raw13659step1Labels = raw13659step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13659step0 raw13659step0Labels permutation56 hz
    mixedMoment B raw13659step1 raw13659step1Labels = mixedMoment B raw13659step2 raw13659step2Labels := by
      have ha : raw13659step2 = (fun i j => raw13659step1 (permutation13 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13659step2 raw13659step1; decide +kernel
      have hl : raw13659step2Labels = raw13659step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13659step1 raw13659step1Labels permutation13 permutation6
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw13660 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13660Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13660step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13660step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13660 raw13660Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw13660 raw13660Labels = mixedMoment B raw13660step0 raw13660step0Labels := by
      have ha : raw13660step0 = (fun i j => raw13660 (permutation181 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13660step0 raw13660; decide +kernel
      have hl : raw13660step0Labels = raw13660Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13660 raw13660Labels permutation181 permutation6
    _ = mixedMoment B node2718 node2718Labels := by rfl

def raw13661 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13661Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13661step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13661step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13661 raw13661Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw13661 raw13661Labels = mixedMoment B raw13661step0 raw13661step0Labels := by
      have hz : ∀ j, raw13661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13661step0 = (fun i j => raw13661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13661step0 raw13661; decide +kernel
      have hl : raw13661step0Labels = raw13661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13661 raw13661Labels permutation346 hz
    mixedMoment B raw13661step0 raw13661step0Labels = mixedMoment B raw13661step1 raw13661step1Labels := by
      have ha : raw13661step1 = (fun i j => raw13661step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13661step1 raw13661step0; decide +kernel
      have hl : raw13661step1Labels = raw13661step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13661step0 raw13661step0Labels permutation37 permutation6
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw13662 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13662Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw13662step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw13662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13662 raw13662Labels = mixedMoment B node2760 node2760Labels := by
  calc
    mixedMoment B raw13662 raw13662Labels = mixedMoment B raw13662step0 raw13662step0Labels := by
      have hz : ∀ j, raw13662 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13662step0 = (fun i j => raw13662 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13662step0 raw13662; decide +kernel
      have hl : raw13662step0Labels = raw13662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13662 raw13662Labels permutation346 hz
    mixedMoment B raw13662step0 raw13662step0Labels = mixedMoment B raw13662step1 raw13662step1Labels := by
      have ha : raw13662step1 = (fun i j => raw13662step0 (permutation146 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13662step1 raw13662step0; decide +kernel
      have hl : raw13662step1Labels = raw13662step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13662step0 raw13662step0Labels permutation146 permutation3
    _ = mixedMoment B node2760 node2760Labels := by rfl

def raw13663 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13663Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13663step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13663step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13663 raw13663Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw13663 raw13663Labels = mixedMoment B raw13663step0 raw13663step0Labels := by
      have hz : ∀ j, raw13663 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13663step0 = (fun i j => raw13663 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13663step0 raw13663; decide +kernel
      have hl : raw13663step0Labels = raw13663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13663 raw13663Labels permutation346 hz
    mixedMoment B raw13663step0 raw13663step0Labels = mixedMoment B raw13663step1 raw13663step1Labels := by
      have ha : raw13663step1 = (fun i j => raw13663step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13663step1 raw13663step0; decide +kernel
      have hl : raw13663step1Labels = raw13663step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13663step0 raw13663step0Labels permutation36 permutation6
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw13664 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13664Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13664step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13664step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13664step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13664step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13664 raw13664Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw13664 raw13664Labels = mixedMoment B raw13664step0 raw13664step0Labels := by
      have hz : ∀ j, raw13664 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13664step0 = (fun i j => raw13664 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13664step0 raw13664; decide +kernel
      have hl : raw13664step0Labels = raw13664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13664 raw13664Labels permutation346 hz
    mixedMoment B raw13664step0 raw13664step0Labels = mixedMoment B raw13664step1 raw13664step1Labels := by
      have hz : ∀ j, raw13664step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13664step1 = (fun i j => raw13664step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13664step1 raw13664step0; decide +kernel
      have hl : raw13664step1Labels = raw13664step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13664step0 raw13664step0Labels permutation56 hz
    mixedMoment B raw13664step1 raw13664step1Labels = mixedMoment B raw13664step2 raw13664step2Labels := by
      have ha : raw13664step2 = (fun i j => raw13664step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13664step2 raw13664step1; decide +kernel
      have hl : raw13664step2Labels = raw13664step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13664step1 raw13664step1Labels permutation12 permutation6
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw13665 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13665Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13665step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13665step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13665 raw13665Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw13665 raw13665Labels = mixedMoment B raw13665step0 raw13665step0Labels := by
      have ha : raw13665step0 = (fun i j => raw13665 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13665step0 raw13665; decide +kernel
      have hl : raw13665step0Labels = raw13665Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13665 raw13665Labels permutation180 permutation6
    _ = mixedMoment B node2718 node2718Labels := by rfl

def raw13666 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13666Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw13666step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13666step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13666 raw13666Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw13666 raw13666Labels = mixedMoment B raw13666step0 raw13666step0Labels := by
      have hz : ∀ j, raw13666 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13666step0 = (fun i j => raw13666 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13666step0 raw13666; decide +kernel
      have hl : raw13666step0Labels = raw13666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13666 raw13666Labels permutation346 hz
    mixedMoment B raw13666step0 raw13666step0Labels = mixedMoment B raw13666step1 raw13666step1Labels := by
      have ha : raw13666step1 = (fun i j => raw13666step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13666step1 raw13666step0; decide +kernel
      have hl : raw13666step1Labels = raw13666step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13666step0 raw13666step0Labels permutation36 permutation6
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw13667 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw13667Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw13667step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw13667step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13667 raw13667Labels = mixedMoment B node2760 node2760Labels := by
  calc
    mixedMoment B raw13667 raw13667Labels = mixedMoment B raw13667step0 raw13667step0Labels := by
      have hz : ∀ j, raw13667 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13667step0 = (fun i j => raw13667 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13667step0 raw13667; decide +kernel
      have hl : raw13667step0Labels = raw13667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13667 raw13667Labels permutation346 hz
    mixedMoment B raw13667step0 raw13667step0Labels = mixedMoment B raw13667step1 raw13667step1Labels := by
      have ha : raw13667step1 = (fun i j => raw13667step0 (permutation140 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13667step1 raw13667step0; decide +kernel
      have hl : raw13667step1Labels = raw13667step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13667step0 raw13667step0Labels permutation140 permutation3
    _ = mixedMoment B node2760 node2760Labels := by rfl

def raw13668 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13668Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13668step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13668step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13668 raw13668Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw13668 raw13668Labels = mixedMoment B raw13668step0 raw13668step0Labels := by
      have hz : ∀ j, raw13668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13668step0 = (fun i j => raw13668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13668step0 raw13668; decide +kernel
      have hl : raw13668step0Labels = raw13668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13668 raw13668Labels permutation346 hz
    mixedMoment B raw13668step0 raw13668step0Labels = mixedMoment B raw13668step1 raw13668step1Labels := by
      have ha : raw13668step1 = (fun i j => raw13668step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13668step1 raw13668step0; decide +kernel
      have hl : raw13668step1Labels = raw13668step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13668step0 raw13668step0Labels permutation36 permutation6
    _ = mixedMoment B node2263 node2263Labels := by rfl

def raw13669 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13669Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13669step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13669step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13669step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13669step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13669step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13669 raw13669Labels = mixedMoment B node2785 node2785Labels := by
  calc
    mixedMoment B raw13669 raw13669Labels = mixedMoment B raw13669step0 raw13669step0Labels := by
      have hz : ∀ j, raw13669 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13669step0 = (fun i j => raw13669 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13669step0 raw13669; decide +kernel
      have hl : raw13669step0Labels = raw13669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13669 raw13669Labels permutation346 hz
    mixedMoment B raw13669step0 raw13669step0Labels = mixedMoment B raw13669step1 raw13669step1Labels := by
      have hz : ∀ j, raw13669step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw13669step1 = (fun i j => raw13669step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw13669step1 raw13669step0; decide +kernel
      have hl : raw13669step1Labels = raw13669step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13669step0 raw13669step0Labels permutation56 hz
    mixedMoment B raw13669step1 raw13669step1Labels = mixedMoment B raw13669step2 raw13669step2Labels := by
      have ha : raw13669step2 = (fun i j => raw13669step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13669step2 raw13669step1; decide +kernel
      have hl : raw13669step2Labels = raw13669step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13669step1 raw13669step1Labels permutation12 permutation6
    _ = mixedMoment B node2785 node2785Labels := by rfl

def raw13670 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13670Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13670step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13670 raw13670Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw13670 raw13670Labels = mixedMoment B raw13670step0 raw13670step0Labels := by
      have ha : raw13670step0 = (fun i j => raw13670 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13670step0 raw13670; decide +kernel
      have hl : raw13670step0Labels = raw13670Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13670 raw13670Labels permutation180 permutation6
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw13671 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13671Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13671step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13671step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13671 raw13671Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw13671 raw13671Labels = mixedMoment B raw13671step0 raw13671step0Labels := by
      have hz : ∀ j, raw13671 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13671step0 = (fun i j => raw13671 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13671step0 raw13671; decide +kernel
      have hl : raw13671step0Labels = raw13671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13671 raw13671Labels permutation346 hz
    mixedMoment B raw13671step0 raw13671step0Labels = mixedMoment B raw13671step1 raw13671step1Labels := by
      have ha : raw13671step1 = (fun i j => raw13671step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13671step1 raw13671step0; decide +kernel
      have hl : raw13671step1Labels = raw13671step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13671step0 raw13671step0Labels permutation33 permutation6
    _ = mixedMoment B node2766 node2766Labels := by rfl

def raw13672 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13672Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13672step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13672step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13672 raw13672Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw13672 raw13672Labels = mixedMoment B raw13672step0 raw13672step0Labels := by
      have hz : ∀ j, raw13672 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13672step0 = (fun i j => raw13672 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13672step0 raw13672; decide +kernel
      have hl : raw13672step0Labels = raw13672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13672 raw13672Labels permutation346 hz
    mixedMoment B raw13672step0 raw13672step0Labels = mixedMoment B raw13672step1 raw13672step1Labels := by
      have ha : raw13672step1 = (fun i j => raw13672step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13672step1 raw13672step0; decide +kernel
      have hl : raw13672step1Labels = raw13672step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13672step0 raw13672step0Labels permutation35 permutation6
    _ = mixedMoment B node2766 node2766Labels := by rfl

def raw13673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13673step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13673step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13673step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13673step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13673step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13673 raw13673Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw13673 raw13673Labels = mixedMoment B raw13673step0 raw13673step0Labels := by
      have ha : raw13673step0 = (fun i j => raw13673 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13673step0 raw13673; decide +kernel
      have hl : raw13673step0Labels = raw13673Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13673 raw13673Labels permutation194 permutation7
    mixedMoment B raw13673step0 raw13673step0Labels = mixedMoment B raw13673step1 raw13673step1Labels := by
      have ha : raw13673step1 = -raw13673step0 := by apply Matrix.ext; change ∀ i j, raw13673step1 i j = -(raw13673step0 i j); unfold raw13673step1 raw13673step0; decide +kernel
      have hl : raw13673step1Labels = raw13673step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13673step1 raw13673step1Labels = mixedMoment B raw13673step2 raw13673step2Labels := by
      have ha : raw13673step2 = raw13673step1 := by apply Matrix.ext; unfold raw13673step2 raw13673step1; decide +kernel
      have hl : raw13673step1Labels = labelEmbedding10 ∘ raw13673step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13673step1 raw13673step1Labels raw13673step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw13674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13674 raw13674Labels = mixedMoment B node5408 node5408Labels := by
  calc
    mixedMoment B raw13674 raw13674Labels = mixedMoment B raw13674step0 raw13674step0Labels := by
      have ha : raw13674step0 = (fun i j => raw13674 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13674step0 raw13674; decide +kernel
      have hl : raw13674step0Labels = raw13674Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13674 raw13674Labels permutation180 permutation2
    _ = mixedMoment B node5408 node5408Labels := by rfl

def raw13675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13675step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13675step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13675step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13675step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13675step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13675 raw13675Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw13675 raw13675Labels = mixedMoment B raw13675step0 raw13675step0Labels := by
      have ha : raw13675step0 = (fun i j => raw13675 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13675step0 raw13675; decide +kernel
      have hl : raw13675step0Labels = raw13675Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13675 raw13675Labels permutation194 permutation7
    mixedMoment B raw13675step0 raw13675step0Labels = mixedMoment B raw13675step1 raw13675step1Labels := by
      have ha : raw13675step1 = -raw13675step0 := by apply Matrix.ext; change ∀ i j, raw13675step1 i j = -(raw13675step0 i j); unfold raw13675step1 raw13675step0; decide +kernel
      have hl : raw13675step1Labels = raw13675step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13675step1 raw13675step1Labels = mixedMoment B raw13675step2 raw13675step2Labels := by
      have ha : raw13675step2 = raw13675step1 := by apply Matrix.ext; unfold raw13675step2 raw13675step1; decide +kernel
      have hl : raw13675step1Labels = labelEmbedding10 ∘ raw13675step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13675step1 raw13675step1Labels raw13675step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw13676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13676step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13676step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13676step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13676step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13676step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13676 raw13676Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw13676 raw13676Labels = mixedMoment B raw13676step0 raw13676step0Labels := by
      have ha : raw13676step0 = (fun i j => raw13676 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13676step0 raw13676; decide +kernel
      have hl : raw13676step0Labels = raw13676Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13676 raw13676Labels permutation195 permutation7
    mixedMoment B raw13676step0 raw13676step0Labels = mixedMoment B raw13676step1 raw13676step1Labels := by
      have ha : raw13676step1 = -raw13676step0 := by apply Matrix.ext; change ∀ i j, raw13676step1 i j = -(raw13676step0 i j); unfold raw13676step1 raw13676step0; decide +kernel
      have hl : raw13676step1Labels = raw13676step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13676step1 raw13676step1Labels = mixedMoment B raw13676step2 raw13676step2Labels := by
      have ha : raw13676step2 = raw13676step1 := by apply Matrix.ext; unfold raw13676step2 raw13676step1; decide +kernel
      have hl : raw13676step1Labels = labelEmbedding10 ∘ raw13676step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13676step1 raw13676step1Labels raw13676step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw13677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13677step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13677step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13677step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13677step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13677 raw13677Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw13677 raw13677Labels = mixedMoment B raw13677step0 raw13677step0Labels := by
      have hz : ∀ j, raw13677 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13677step0 = (fun i j => raw13677 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13677step0 raw13677; decide +kernel
      have hl : raw13677step0Labels = raw13677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13677 raw13677Labels permutation590 hz
    mixedMoment B raw13677step0 raw13677step0Labels = mixedMoment B raw13677step1 raw13677step1Labels := by
      have ha : raw13677step1 = (fun i j => raw13677step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13677step1 raw13677step0; decide +kernel
      have hl : raw13677step1Labels = raw13677step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13677step0 raw13677step0Labels permutation38 permutation7
    mixedMoment B raw13677step1 raw13677step1Labels = mixedMoment B raw13677step2 raw13677step2Labels := by
      have ha : raw13677step2 = -raw13677step1 := by apply Matrix.ext; change ∀ i j, raw13677step2 i j = -(raw13677step1 i j); unfold raw13677step2 raw13677step1; decide +kernel
      have hl : raw13677step2Labels = raw13677step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13677step2 raw13677step2Labels = mixedMoment B raw13677step3 raw13677step3Labels := by
      have ha : raw13677step3 = raw13677step2 := by apply Matrix.ext; unfold raw13677step3 raw13677step2; decide +kernel
      have hl : raw13677step2Labels = labelEmbedding10 ∘ raw13677step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13677step2 raw13677step2Labels raw13677step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw13678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13678 raw13678Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw13678 raw13678Labels = mixedMoment B raw13678step0 raw13678step0Labels := by
      have ha : raw13678step0 = (fun i j => raw13678 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13678step0 raw13678; decide +kernel
      have hl : raw13678step0Labels = raw13678Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13678 raw13678Labels permutation194 permutation2
    _ = mixedMoment B node4601 node4601Labels := by rfl

def raw13679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13679 raw13679Labels = mixedMoment B node5100 node5100Labels := by
  calc
    mixedMoment B raw13679 raw13679Labels = mixedMoment B raw13679step0 raw13679step0Labels := by
      have ha : raw13679step0 = (fun i j => raw13679 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13679step0 raw13679; decide +kernel
      have hl : raw13679step0Labels = raw13679Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13679 raw13679Labels permutation194 permutation2
    _ = mixedMoment B node5100 node5100Labels := by rfl

def raw13680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13680step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13680 raw13680Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw13680 raw13680Labels = mixedMoment B raw13680step0 raw13680step0Labels := by
      have ha : raw13680step0 = (fun i j => raw13680 (permutation186 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13680step0 raw13680; decide +kernel
      have hl : raw13680step0Labels = raw13680Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13680 raw13680Labels permutation186 permutation2
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw13681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13681 raw13681Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw13681 raw13681Labels = mixedMoment B raw13681step0 raw13681step0Labels := by
      have ha : raw13681step0 = (fun i j => raw13681 (permutation192 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13681step0 raw13681; decide +kernel
      have hl : raw13681step0Labels = raw13681Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13681 raw13681Labels permutation192 permutation2
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw13682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13682step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13682 raw13682Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw13682 raw13682Labels = mixedMoment B raw13682step0 raw13682step0Labels := by
      have hz : ∀ j, raw13682 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13682step0 = (fun i j => raw13682 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13682step0 raw13682; decide +kernel
      have hl : raw13682step0Labels = raw13682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13682 raw13682Labels permutation590 hz
    mixedMoment B raw13682step0 raw13682step0Labels = mixedMoment B raw13682step1 raw13682step1Labels := by
      have ha : raw13682step1 = (fun i j => raw13682step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13682step1 raw13682step0; decide +kernel
      have hl : raw13682step1Labels = raw13682step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13682step0 raw13682step0Labels permutation38 permutation2
    _ = mixedMoment B node5273 node5273Labels := by rfl

def raw13683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13683step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13683step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13683 raw13683Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw13683 raw13683Labels = mixedMoment B raw13683step0 raw13683step0Labels := by
      have ha : raw13683step0 = (fun i j => raw13683 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13683step0 raw13683; decide +kernel
      have hl : raw13683step0Labels = raw13683Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13683 raw13683Labels permutation161 permutation3
    mixedMoment B raw13683step0 raw13683step0Labels = mixedMoment B raw13683step1 raw13683step1Labels := by
      have ha : raw13683step1 = raw13683step0 := by apply Matrix.ext; unfold raw13683step1 raw13683step0; decide +kernel
      have hl : raw13683step0Labels = labelEmbedding6 ∘ raw13683step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13683step0 raw13683step0Labels raw13683step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw13684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13684 raw13684Labels = mixedMoment B node5197 node5197Labels := by
  calc
    mixedMoment B raw13684 raw13684Labels = mixedMoment B raw13684step0 raw13684step0Labels := by
      have ha : raw13684step0 = (fun i j => raw13684 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13684step0 raw13684; decide +kernel
      have hl : raw13684step0Labels = raw13684Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13684 raw13684Labels permutation156 permutation2
    _ = mixedMoment B node5197 node5197Labels := by rfl

def raw13685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13685step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13685 raw13685Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw13685 raw13685Labels = mixedMoment B raw13685step0 raw13685step0Labels := by
      have ha : raw13685step0 = (fun i j => raw13685 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13685step0 raw13685; decide +kernel
      have hl : raw13685step0Labels = raw13685Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13685 raw13685Labels permutation159 permutation2
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw13686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13686 raw13686Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw13686 raw13686Labels = mixedMoment B raw13686step0 raw13686step0Labels := by
      have ha : raw13686step0 = (fun i j => raw13686 (permutation165 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13686step0 raw13686; decide +kernel
      have hl : raw13686step0Labels = raw13686Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13686 raw13686Labels permutation165 permutation2
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw13687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13687 raw13687Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw13687 raw13687Labels = mixedMoment B raw13687step0 raw13687step0Labels := by
      have hz : ∀ j, raw13687 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13687step0 = (fun i j => raw13687 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13687step0 raw13687; decide +kernel
      have hl : raw13687step0Labels = raw13687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13687 raw13687Labels permutation590 hz
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw13688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13688 raw13688Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw13688 raw13688Labels = mixedMoment B raw13688step0 raw13688step0Labels := by
      have ha : raw13688step0 = (fun i j => raw13688 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13688step0 raw13688; decide +kernel
      have hl : raw13688step0Labels = raw13688Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13688 raw13688Labels permutation181 permutation2
    _ = mixedMoment B node4590 node4590Labels := by rfl

def raw13689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13689 raw13689Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw13689 raw13689Labels = mixedMoment B raw13689step0 raw13689step0Labels := by
      have ha : raw13689step0 = (fun i j => raw13689 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13689step0 raw13689; decide +kernel
      have hl : raw13689step0Labels = raw13689Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13689 raw13689Labels permutation157 permutation2
    _ = mixedMoment B node5185 node5185Labels := by rfl

def raw13690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13690step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13690 raw13690Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw13690 raw13690Labels = mixedMoment B raw13690step0 raw13690step0Labels := by
      have ha : raw13690step0 = (fun i j => raw13690 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13690step0 raw13690; decide +kernel
      have hl : raw13690step0Labels = raw13690Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13690 raw13690Labels permutation181 permutation2
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw13691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13691 raw13691Labels = mixedMoment B node5250 node5250Labels := by
  calc
    mixedMoment B raw13691 raw13691Labels = mixedMoment B raw13691step0 raw13691step0Labels := by
      have ha : raw13691step0 = (fun i j => raw13691 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13691step0 raw13691; decide +kernel
      have hl : raw13691step0Labels = raw13691Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13691 raw13691Labels permutation179 permutation2
    _ = mixedMoment B node5250 node5250Labels := by rfl

def raw13692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw13692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13692step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13692 raw13692Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw13692 raw13692Labels = mixedMoment B raw13692step0 raw13692step0Labels := by
      have hz : ∀ j, raw13692 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13692step0 = (fun i j => raw13692 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13692step0 raw13692; decide +kernel
      have hl : raw13692step0Labels = raw13692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13692 raw13692Labels permutation590 hz
    mixedMoment B raw13692step0 raw13692step0Labels = mixedMoment B raw13692step1 raw13692step1Labels := by
      have ha : raw13692step1 = (fun i j => raw13692step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13692step1 raw13692step0; decide +kernel
      have hl : raw13692step1Labels = raw13692step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13692step0 raw13692step0Labels permutation39 permutation2
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw13693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13693 raw13693Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw13693 raw13693Labels = mixedMoment B raw13693step0 raw13693step0Labels := by
      have ha : raw13693step0 = (fun i j => raw13693 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13693step0 raw13693; decide +kernel
      have hl : raw13693step0Labels = raw13693Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13693 raw13693Labels permutation180 permutation2
    _ = mixedMoment B node4590 node4590Labels := by rfl

def raw13694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13694step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13694 raw13694Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw13694 raw13694Labels = mixedMoment B raw13694step0 raw13694step0Labels := by
      have ha : raw13694step0 = (fun i j => raw13694 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13694step0 raw13694; decide +kernel
      have hl : raw13694step0Labels = raw13694Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13694 raw13694Labels permutation156 permutation2
    _ = mixedMoment B node5185 node5185Labels := by rfl

def raw13695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13695step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13695 raw13695Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw13695 raw13695Labels = mixedMoment B raw13695step0 raw13695step0Labels := by
      have ha : raw13695step0 = (fun i j => raw13695 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13695step0 raw13695; decide +kernel
      have hl : raw13695step0Labels = raw13695Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13695 raw13695Labels permutation180 permutation2
    _ = mixedMoment B node5073 node5073Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
