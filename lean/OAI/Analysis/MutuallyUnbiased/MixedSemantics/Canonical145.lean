import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw18560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18560Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18560step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18560 raw18560Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw18560 raw18560Labels = mixedMoment B raw18560step0 raw18560step0Labels := by
      have hz : ∀ j, raw18560 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18560step0 = (fun i j => raw18560 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18560step0 raw18560; decide +kernel
      have hl : raw18560step0Labels = raw18560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18560 raw18560Labels permutation590 hz
    mixedMoment B raw18560step0 raw18560step0Labels = mixedMoment B raw18560step1 raw18560step1Labels := by
      have ha : raw18560step1 = (fun i j => raw18560step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18560step1 raw18560step0; decide +kernel
      have hl : raw18560step1Labels = raw18560step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18560step0 raw18560step0Labels permutation32 permutation3
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw18561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18561Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18561 raw18561Labels = mixedMoment B node3370 node3370Labels := by
  calc
    mixedMoment B raw18561 raw18561Labels = mixedMoment B raw18561step0 raw18561step0Labels := by
      have ha : raw18561step0 = (fun i j => raw18561 (permutation268 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18561step0 raw18561; decide +kernel
      have hl : raw18561step0Labels = raw18561Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18561 raw18561Labels permutation268 permutation3
    _ = mixedMoment B node3370 node3370Labels := by rfl

def raw18562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18562Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw18562step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18562step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw18562step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18562 raw18562Labels = mixedMoment B node3778 node3778Labels := by
  calc
    mixedMoment B raw18562 raw18562Labels = mixedMoment B raw18562step0 raw18562step0Labels := by
      have ha : raw18562step0 = (fun i j => raw18562 (permutation502 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18562step0 raw18562; decide +kernel
      have hl : raw18562step0Labels = raw18562Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18562 raw18562Labels permutation502 permutation3
    mixedMoment B raw18562step0 raw18562step0Labels = mixedMoment B raw18562step1 raw18562step1Labels := by
      have ha : raw18562step1 = -raw18562step0 := by apply Matrix.ext; change ∀ i j, raw18562step1 i j = -(raw18562step0 i j); unfold raw18562step1 raw18562step0; decide +kernel
      have hl : raw18562step1Labels = raw18562step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3778 node3778Labels := by rfl

def raw18563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18563Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw18563step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18563step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18563step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18563step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18563 raw18563Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw18563 raw18563Labels = mixedMoment B raw18563step0 raw18563step0Labels := by
      have hz : ∀ j, raw18563 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18563step0 = (fun i j => raw18563 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18563step0 raw18563; decide +kernel
      have hl : raw18563step0Labels = raw18563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18563 raw18563Labels permutation520 hz
    mixedMoment B raw18563step0 raw18563step0Labels = mixedMoment B raw18563step1 raw18563step1Labels := by
      have ha : raw18563step1 = (fun i j => raw18563step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18563step1 raw18563step0; decide +kernel
      have hl : raw18563step1Labels = raw18563step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18563step0 raw18563step0Labels permutation127 permutation3
    mixedMoment B raw18563step1 raw18563step1Labels = mixedMoment B raw18563step2 raw18563step2Labels := by
      have ha : raw18563step2 = -raw18563step1 := by apply Matrix.ext; change ∀ i j, raw18563step2 i j = -(raw18563step1 i j); unfold raw18563step2 raw18563step1; decide +kernel
      have hl : raw18563step2Labels = raw18563step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw18564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18564Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw18564step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18564step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18564step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18564 raw18564Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw18564 raw18564Labels = mixedMoment B raw18564step0 raw18564step0Labels := by
      have hz : ∀ j, raw18564 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18564step0 = (fun i j => raw18564 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18564step0 raw18564; decide +kernel
      have hl : raw18564step0Labels = raw18564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18564 raw18564Labels permutation590 hz
    mixedMoment B raw18564step0 raw18564step0Labels = mixedMoment B raw18564step1 raw18564step1Labels := by
      have ha : raw18564step1 = (fun i j => raw18564step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18564step1 raw18564step0; decide +kernel
      have hl : raw18564step1Labels = raw18564step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18564step0 raw18564step0Labels permutation127 permutation3
    mixedMoment B raw18564step1 raw18564step1Labels = mixedMoment B raw18564step2 raw18564step2Labels := by
      have ha : raw18564step2 = -raw18564step1 := by apply Matrix.ext; change ∀ i j, raw18564step2 i j = -(raw18564step1 i j); unfold raw18564step2 raw18564step1; decide +kernel
      have hl : raw18564step2Labels = raw18564step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw18565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18565Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18565step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18565 raw18565Labels = mixedMoment B node3370 node3370Labels := by
  calc
    mixedMoment B raw18565 raw18565Labels = mixedMoment B raw18565step0 raw18565step0Labels := by
      have ha : raw18565step0 = (fun i j => raw18565 (permutation266 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18565step0 raw18565; decide +kernel
      have hl : raw18565step0Labels = raw18565Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18565 raw18565Labels permutation266 permutation3
    _ = mixedMoment B node3370 node3370Labels := by rfl

def raw18566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18566Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw18566step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18566step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw18566step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18566 raw18566Labels = mixedMoment B node3778 node3778Labels := by
  calc
    mixedMoment B raw18566 raw18566Labels = mixedMoment B raw18566step0 raw18566step0Labels := by
      have ha : raw18566step0 = (fun i j => raw18566 (permutation566 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18566step0 raw18566; decide +kernel
      have hl : raw18566step0Labels = raw18566Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18566 raw18566Labels permutation566 permutation3
    mixedMoment B raw18566step0 raw18566step0Labels = mixedMoment B raw18566step1 raw18566step1Labels := by
      have ha : raw18566step1 = -raw18566step0 := by apply Matrix.ext; change ∀ i j, raw18566step1 i j = -(raw18566step0 i j); unfold raw18566step1 raw18566step0; decide +kernel
      have hl : raw18566step1Labels = raw18566step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3778 node3778Labels := by rfl

def raw18567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18567Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw18567step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18567step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18567step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18567step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18567 raw18567Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw18567 raw18567Labels = mixedMoment B raw18567step0 raw18567step0Labels := by
      have hz : ∀ j, raw18567 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18567step0 = (fun i j => raw18567 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18567step0 raw18567; decide +kernel
      have hl : raw18567step0Labels = raw18567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18567 raw18567Labels permutation434 hz
    mixedMoment B raw18567step0 raw18567step0Labels = mixedMoment B raw18567step1 raw18567step1Labels := by
      have ha : raw18567step1 = (fun i j => raw18567step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18567step1 raw18567step0; decide +kernel
      have hl : raw18567step1Labels = raw18567step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18567step0 raw18567step0Labels permutation127 permutation3
    mixedMoment B raw18567step1 raw18567step1Labels = mixedMoment B raw18567step2 raw18567step2Labels := by
      have ha : raw18567step2 = -raw18567step1 := by apply Matrix.ext; change ∀ i j, raw18567step2 i j = -(raw18567step1 i j); unfold raw18567step2 raw18567step1; decide +kernel
      have hl : raw18567step2Labels = raw18567step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw18568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw18568Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18568step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18568step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18568step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18568step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18568 raw18568Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw18568 raw18568Labels = mixedMoment B raw18568step0 raw18568step0Labels := by
      have hz : ∀ j, raw18568 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18568step0 = (fun i j => raw18568 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18568step0 raw18568; decide +kernel
      have hl : raw18568step0Labels = raw18568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18568 raw18568Labels permutation590 hz
    mixedMoment B raw18568step0 raw18568step0Labels = mixedMoment B raw18568step1 raw18568step1Labels := by
      have ha : raw18568step1 = (fun i j => raw18568step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18568step1 raw18568step0; decide +kernel
      have hl : raw18568step1Labels = raw18568step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18568step0 raw18568step0Labels permutation151 permutation3
    mixedMoment B raw18568step1 raw18568step1Labels = mixedMoment B raw18568step2 raw18568step2Labels := by
      have ha : raw18568step2 = -raw18568step1 := by apply Matrix.ext; change ∀ i j, raw18568step2 i j = -(raw18568step1 i j); unfold raw18568step2 raw18568step1; decide +kernel
      have hl : raw18568step2Labels = raw18568step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw18569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18569Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18569step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18569 raw18569Labels = mixedMoment B node3370 node3370Labels := by
  calc
    mixedMoment B raw18569 raw18569Labels = mixedMoment B raw18569step0 raw18569step0Labels := by
      have ha : raw18569step0 = (fun i j => raw18569 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18569step0 raw18569; decide +kernel
      have hl : raw18569step0Labels = raw18569Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18569 raw18569Labels permutation265 permutation3
    _ = mixedMoment B node3370 node3370Labels := by rfl

def raw18570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18570Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw18570step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18570step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw18570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18570 raw18570Labels = mixedMoment B node3778 node3778Labels := by
  calc
    mixedMoment B raw18570 raw18570Labels = mixedMoment B raw18570step0 raw18570step0Labels := by
      have ha : raw18570step0 = (fun i j => raw18570 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18570step0 raw18570; decide +kernel
      have hl : raw18570step0Labels = raw18570Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18570 raw18570Labels permutation662 permutation3
    mixedMoment B raw18570step0 raw18570step0Labels = mixedMoment B raw18570step1 raw18570step1Labels := by
      have ha : raw18570step1 = -raw18570step0 := by apply Matrix.ext; change ∀ i j, raw18570step1 i j = -(raw18570step0 i j); unfold raw18570step1 raw18570step0; decide +kernel
      have hl : raw18570step1Labels = raw18570step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3778 node3778Labels := by rfl

def raw18571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18571Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18571step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18571step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18571step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18571step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18571step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18571 raw18571Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw18571 raw18571Labels = mixedMoment B raw18571step0 raw18571step0Labels := by
      have hz : ∀ j, raw18571 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18571step0 = (fun i j => raw18571 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18571step0 raw18571; decide +kernel
      have hl : raw18571step0Labels = raw18571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18571 raw18571Labels permutation434 hz
    mixedMoment B raw18571step0 raw18571step0Labels = mixedMoment B raw18571step1 raw18571step1Labels := by
      have ha : raw18571step1 = (fun i j => raw18571step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18571step1 raw18571step0; decide +kernel
      have hl : raw18571step1Labels = raw18571step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18571step0 raw18571step0Labels permutation151 permutation3
    mixedMoment B raw18571step1 raw18571step1Labels = mixedMoment B raw18571step2 raw18571step2Labels := by
      have ha : raw18571step2 = -raw18571step1 := by apply Matrix.ext; change ∀ i j, raw18571step2 i j = -(raw18571step1 i j); unfold raw18571step2 raw18571step1; decide +kernel
      have hl : raw18571step2Labels = raw18571step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw18572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw18572Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18572step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18572step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18572step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18572 raw18572Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw18572 raw18572Labels = mixedMoment B raw18572step0 raw18572step0Labels := by
      have hz : ∀ j, raw18572 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18572step0 = (fun i j => raw18572 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18572step0 raw18572; decide +kernel
      have hl : raw18572step0Labels = raw18572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18572 raw18572Labels permutation520 hz
    mixedMoment B raw18572step0 raw18572step0Labels = mixedMoment B raw18572step1 raw18572step1Labels := by
      have ha : raw18572step1 = (fun i j => raw18572step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18572step1 raw18572step0; decide +kernel
      have hl : raw18572step1Labels = raw18572step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18572step0 raw18572step0Labels permutation151 permutation3
    mixedMoment B raw18572step1 raw18572step1Labels = mixedMoment B raw18572step2 raw18572step2Labels := by
      have ha : raw18572step2 = -raw18572step1 := by apply Matrix.ext; change ∀ i j, raw18572step2 i j = -(raw18572step1 i j); unfold raw18572step2 raw18572step1; decide +kernel
      have hl : raw18572step2Labels = raw18572step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw18573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18573step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18573 raw18573Labels = mixedMoment B node5427 node5427Labels := by
  calc
    mixedMoment B raw18573 raw18573Labels = mixedMoment B raw18573step0 raw18573step0Labels := by
      have ha : raw18573step0 = (fun i j => raw18573 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18573step0 raw18573; decide +kernel
      have hl : raw18573step0Labels = raw18573Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18573 raw18573Labels permutation265 permutation2
    _ = mixedMoment B node5427 node5427Labels := by rfl

def raw18574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18574step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18574step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18574step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18574step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18574step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18574 raw18574Labels = mixedMoment B node5479 node5479Labels := by
  calc
    mixedMoment B raw18574 raw18574Labels = mixedMoment B raw18574step0 raw18574step0Labels := by
      have ha : raw18574step0 = (fun i j => raw18574 (permutation289 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18574step0 raw18574; decide +kernel
      have hl : raw18574step0Labels = raw18574Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18574 raw18574Labels permutation289 permutation7
    mixedMoment B raw18574step0 raw18574step0Labels = mixedMoment B raw18574step1 raw18574step1Labels := by
      have ha : raw18574step1 = -raw18574step0 := by apply Matrix.ext; change ∀ i j, raw18574step1 i j = -(raw18574step0 i j); unfold raw18574step1 raw18574step0; decide +kernel
      have hl : raw18574step1Labels = raw18574step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18574step1 raw18574step1Labels = mixedMoment B raw18574step2 raw18574step2Labels := by
      have ha : raw18574step2 = raw18574step1 := by apply Matrix.ext; unfold raw18574step2 raw18574step1; decide +kernel
      have hl : raw18574step1Labels = labelEmbedding10 ∘ raw18574step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18574step1 raw18574step1Labels raw18574step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5479 node5479Labels := by rfl

def raw18575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18575step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18575step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18575step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18575step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18575step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18575 raw18575Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw18575 raw18575Labels = mixedMoment B raw18575step0 raw18575step0Labels := by
      have ha : raw18575step0 = (fun i j => raw18575 (permutation292 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18575step0 raw18575; decide +kernel
      have hl : raw18575step0Labels = raw18575Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18575 raw18575Labels permutation292 permutation6
    mixedMoment B raw18575step0 raw18575step0Labels = mixedMoment B raw18575step1 raw18575step1Labels := by
      have ha : raw18575step1 = -raw18575step0 := by apply Matrix.ext; change ∀ i j, raw18575step1 i j = -(raw18575step0 i j); unfold raw18575step1 raw18575step0; decide +kernel
      have hl : raw18575step1Labels = raw18575step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18575step1 raw18575step1Labels = mixedMoment B raw18575step2 raw18575step2Labels := by
      have ha : raw18575step2 = raw18575step1 := by apply Matrix.ext; unfold raw18575step2 raw18575step1; decide +kernel
      have hl : raw18575step1Labels = labelEmbedding9 ∘ raw18575step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18575step1 raw18575step1Labels raw18575step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw18576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw18576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18576step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18576step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18576step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18576step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18576step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18576 raw18576Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw18576 raw18576Labels = mixedMoment B raw18576step0 raw18576step0Labels := by
      have ha : raw18576step0 = (fun i j => raw18576 (permutation290 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18576step0 raw18576; decide +kernel
      have hl : raw18576step0Labels = raw18576Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18576 raw18576Labels permutation290 permutation6
    mixedMoment B raw18576step0 raw18576step0Labels = mixedMoment B raw18576step1 raw18576step1Labels := by
      have ha : raw18576step1 = -raw18576step0 := by apply Matrix.ext; change ∀ i j, raw18576step1 i j = -(raw18576step0 i j); unfold raw18576step1 raw18576step0; decide +kernel
      have hl : raw18576step1Labels = raw18576step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18576step1 raw18576step1Labels = mixedMoment B raw18576step2 raw18576step2Labels := by
      have ha : raw18576step2 = raw18576step1 := by apply Matrix.ext; unfold raw18576step2 raw18576step1; decide +kernel
      have hl : raw18576step1Labels = labelEmbedding9 ∘ raw18576step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18576step1 raw18576step1Labels raw18576step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw18577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw18577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18577step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18577step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18577step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18577step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18577step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18577 raw18577Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw18577 raw18577Labels = mixedMoment B raw18577step0 raw18577step0Labels := by
      have ha : raw18577step0 = (fun i j => raw18577 (permutation289 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18577step0 raw18577; decide +kernel
      have hl : raw18577step0Labels = raw18577Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18577 raw18577Labels permutation289 permutation6
    mixedMoment B raw18577step0 raw18577step0Labels = mixedMoment B raw18577step1 raw18577step1Labels := by
      have ha : raw18577step1 = -raw18577step0 := by apply Matrix.ext; change ∀ i j, raw18577step1 i j = -(raw18577step0 i j); unfold raw18577step1 raw18577step0; decide +kernel
      have hl : raw18577step1Labels = raw18577step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18577step1 raw18577step1Labels = mixedMoment B raw18577step2 raw18577step2Labels := by
      have ha : raw18577step2 = raw18577step1 := by apply Matrix.ext; unfold raw18577step2 raw18577step1; decide +kernel
      have hl : raw18577step1Labels = labelEmbedding9 ∘ raw18577step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18577step1 raw18577step1Labels raw18577step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw18578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw18578step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18578step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18578step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18578step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18578step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18578 raw18578Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw18578 raw18578Labels = mixedMoment B raw18578step0 raw18578step0Labels := by
      have ha : raw18578step0 = (fun i j => raw18578 (permutation217 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18578step0 raw18578; decide +kernel
      have hl : raw18578step0Labels = raw18578Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18578 raw18578Labels permutation217 permutation5
    mixedMoment B raw18578step0 raw18578step0Labels = mixedMoment B raw18578step1 raw18578step1Labels := by
      have ha : raw18578step1 = -raw18578step0 := by apply Matrix.ext; change ∀ i j, raw18578step1 i j = -(raw18578step0 i j); unfold raw18578step1 raw18578step0; decide +kernel
      have hl : raw18578step1Labels = raw18578step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18578step1 raw18578step1Labels = mixedMoment B raw18578step2 raw18578step2Labels := by
      have ha : raw18578step2 = raw18578step1 := by apply Matrix.ext; unfold raw18578step2 raw18578step1; decide +kernel
      have hl : raw18578step1Labels = labelEmbedding8 ∘ raw18578step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18578step1 raw18578step1Labels raw18578step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4885 node4885Labels := by rfl

def raw18579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18579step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18579step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18579step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18579 raw18579Labels = mixedMoment B node5437 node5437Labels := by
  calc
    mixedMoment B raw18579 raw18579Labels = mixedMoment B raw18579step0 raw18579step0Labels := by
      have ha : raw18579step0 = (fun i j => raw18579 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18579step0 raw18579; decide +kernel
      have hl : raw18579step0Labels = raw18579Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18579 raw18579Labels permutation176 permutation3
    mixedMoment B raw18579step0 raw18579step0Labels = mixedMoment B raw18579step1 raw18579step1Labels := by
      have ha : raw18579step1 = raw18579step0 := by apply Matrix.ext; unfold raw18579step1 raw18579step0; decide +kernel
      have hl : raw18579step0Labels = labelEmbedding6 ∘ raw18579step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18579step0 raw18579step0Labels raw18579step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5437 node5437Labels := by rfl

def raw18580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18580step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18580step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18580step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18580 raw18580Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw18580 raw18580Labels = mixedMoment B raw18580step0 raw18580step0Labels := by
      have ha : raw18580step0 = (fun i j => raw18580 (permutation302 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18580step0 raw18580; decide +kernel
      have hl : raw18580step0Labels = raw18580Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18580 raw18580Labels permutation302 permutation4
    mixedMoment B raw18580step0 raw18580step0Labels = mixedMoment B raw18580step1 raw18580step1Labels := by
      have ha : raw18580step1 = raw18580step0 := by apply Matrix.ext; unfold raw18580step1 raw18580step0; decide +kernel
      have hl : raw18580step0Labels = labelEmbedding7 ∘ raw18580step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18580step0 raw18580step0Labels raw18580step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw18581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw18581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18581step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18581step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18581 raw18581Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw18581 raw18581Labels = mixedMoment B raw18581step0 raw18581step0Labels := by
      have ha : raw18581step0 = (fun i j => raw18581 (permutation298 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18581step0 raw18581; decide +kernel
      have hl : raw18581step0Labels = raw18581Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18581 raw18581Labels permutation298 permutation4
    mixedMoment B raw18581step0 raw18581step0Labels = mixedMoment B raw18581step1 raw18581step1Labels := by
      have ha : raw18581step1 = raw18581step0 := by apply Matrix.ext; unfold raw18581step1 raw18581step0; decide +kernel
      have hl : raw18581step0Labels = labelEmbedding7 ∘ raw18581step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18581step0 raw18581step0Labels raw18581step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw18582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw18582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18582step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18582step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18582step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18582 raw18582Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw18582 raw18582Labels = mixedMoment B raw18582step0 raw18582step0Labels := by
      have ha : raw18582step0 = (fun i j => raw18582 (permutation297 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18582step0 raw18582; decide +kernel
      have hl : raw18582step0Labels = raw18582Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18582 raw18582Labels permutation297 permutation4
    mixedMoment B raw18582step0 raw18582step0Labels = mixedMoment B raw18582step1 raw18582step1Labels := by
      have ha : raw18582step1 = raw18582step0 := by apply Matrix.ext; unfold raw18582step1 raw18582step0; decide +kernel
      have hl : raw18582step0Labels = labelEmbedding7 ∘ raw18582step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18582step0 raw18582step0Labels raw18582step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw18583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18583step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18583step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18583 raw18583Labels = mixedMoment B node4863 node4863Labels := by
  calc
    mixedMoment B raw18583 raw18583Labels = mixedMoment B raw18583step0 raw18583step0Labels := by
      have ha : raw18583step0 = (fun i j => raw18583 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18583step0 raw18583; decide +kernel
      have hl : raw18583step0Labels = raw18583Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18583 raw18583Labels permutation161 permutation3
    mixedMoment B raw18583step0 raw18583step0Labels = mixedMoment B raw18583step1 raw18583step1Labels := by
      have ha : raw18583step1 = raw18583step0 := by apply Matrix.ext; unfold raw18583step1 raw18583step0; decide +kernel
      have hl : raw18583step0Labels = labelEmbedding6 ∘ raw18583step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18583step0 raw18583step0Labels raw18583step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4863 node4863Labels := by rfl

def raw18584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18584step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18584 raw18584Labels = mixedMoment B node5383 node5383Labels := by
  calc
    mixedMoment B raw18584 raw18584Labels = mixedMoment B raw18584step0 raw18584step0Labels := by
      have ha : raw18584step0 = (fun i j => raw18584 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18584step0 raw18584; decide +kernel
      have hl : raw18584step0Labels = raw18584Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18584 raw18584Labels permutation265 permutation2
    _ = mixedMoment B node5383 node5383Labels := by rfl

def raw18585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18585step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18585step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18585step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18585step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18585step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18585 raw18585Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw18585 raw18585Labels = mixedMoment B raw18585step0 raw18585step0Labels := by
      have ha : raw18585step0 = (fun i j => raw18585 (permutation216 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18585step0 raw18585; decide +kernel
      have hl : raw18585step0Labels = raw18585Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18585 raw18585Labels permutation216 permutation5
    mixedMoment B raw18585step0 raw18585step0Labels = mixedMoment B raw18585step1 raw18585step1Labels := by
      have ha : raw18585step1 = -raw18585step0 := by apply Matrix.ext; change ∀ i j, raw18585step1 i j = -(raw18585step0 i j); unfold raw18585step1 raw18585step0; decide +kernel
      have hl : raw18585step1Labels = raw18585step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18585step1 raw18585step1Labels = mixedMoment B raw18585step2 raw18585step2Labels := by
      have ha : raw18585step2 = raw18585step1 := by apply Matrix.ext; unfold raw18585step2 raw18585step1; decide +kernel
      have hl : raw18585step1Labels = labelEmbedding8 ∘ raw18585step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18585step1 raw18585step1Labels raw18585step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw18586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw18586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18586step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18586step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18586step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18586step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18586step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18586step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18586 raw18586Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw18586 raw18586Labels = mixedMoment B raw18586step0 raw18586step0Labels := by
      have ha : raw18586step0 = (fun i j => raw18586 (permutation238 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18586step0 raw18586; decide +kernel
      have hl : raw18586step0Labels = raw18586Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18586 raw18586Labels permutation238 permutation5
    mixedMoment B raw18586step0 raw18586step0Labels = mixedMoment B raw18586step1 raw18586step1Labels := by
      have ha : raw18586step1 = -raw18586step0 := by apply Matrix.ext; change ∀ i j, raw18586step1 i j = -(raw18586step0 i j); unfold raw18586step1 raw18586step0; decide +kernel
      have hl : raw18586step1Labels = raw18586step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18586step1 raw18586step1Labels = mixedMoment B raw18586step2 raw18586step2Labels := by
      have ha : raw18586step2 = raw18586step1 := by apply Matrix.ext; unfold raw18586step2 raw18586step1; decide +kernel
      have hl : raw18586step1Labels = labelEmbedding8 ∘ raw18586step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18586step1 raw18586step1Labels raw18586step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw18587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw18587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18587step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18587step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18587step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18587step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18587step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18587step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18587 raw18587Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw18587 raw18587Labels = mixedMoment B raw18587step0 raw18587step0Labels := by
      have ha : raw18587step0 = (fun i j => raw18587 (permutation258 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18587step0 raw18587; decide +kernel
      have hl : raw18587step0Labels = raw18587Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18587 raw18587Labels permutation258 permutation5
    mixedMoment B raw18587step0 raw18587step0Labels = mixedMoment B raw18587step1 raw18587step1Labels := by
      have ha : raw18587step1 = -raw18587step0 := by apply Matrix.ext; change ∀ i j, raw18587step1 i j = -(raw18587step0 i j); unfold raw18587step1 raw18587step0; decide +kernel
      have hl : raw18587step1Labels = raw18587step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18587step1 raw18587step1Labels = mixedMoment B raw18587step2 raw18587step2Labels := by
      have ha : raw18587step2 = raw18587step1 := by apply Matrix.ext; unfold raw18587step2 raw18587step1; decide +kernel
      have hl : raw18587step1Labels = labelEmbedding8 ∘ raw18587step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18587step1 raw18587step1Labels raw18587step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw18588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18588step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18588step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18588step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18588 raw18588Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw18588 raw18588Labels = mixedMoment B raw18588step0 raw18588step0Labels := by
      have ha : raw18588step0 = (fun i j => raw18588 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18588step0 raw18588; decide +kernel
      have hl : raw18588step0Labels = raw18588Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18588 raw18588Labels permutation155 permutation3
    mixedMoment B raw18588step0 raw18588step0Labels = mixedMoment B raw18588step1 raw18588step1Labels := by
      have ha : raw18588step1 = raw18588step0 := by apply Matrix.ext; unfold raw18588step1 raw18588step0; decide +kernel
      have hl : raw18588step0Labels = labelEmbedding6 ∘ raw18588step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18588step0 raw18588step0Labels raw18588step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4851 node4851Labels := by rfl

def raw18589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18589step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18589 raw18589Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw18589 raw18589Labels = mixedMoment B raw18589step0 raw18589step0Labels := by
      have ha : raw18589step0 = (fun i j => raw18589 (permutation268 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18589step0 raw18589; decide +kernel
      have hl : raw18589step0Labels = raw18589Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18589 raw18589Labels permutation268 permutation2
    _ = mixedMoment B node5380 node5380Labels := by rfl

def raw18590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18590step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18590step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18590step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18590 raw18590Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw18590 raw18590Labels = mixedMoment B raw18590step0 raw18590step0Labels := by
      have ha : raw18590step0 = (fun i j => raw18590 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18590step0 raw18590; decide +kernel
      have hl : raw18590step0Labels = raw18590Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18590 raw18590Labels permutation179 permutation3
    mixedMoment B raw18590step0 raw18590step0Labels = mixedMoment B raw18590step1 raw18590step1Labels := by
      have ha : raw18590step1 = raw18590step0 := by apply Matrix.ext; unfold raw18590step1 raw18590step0; decide +kernel
      have hl : raw18590step0Labels = labelEmbedding6 ∘ raw18590step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18590step0 raw18590step0Labels raw18590step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

def raw18591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1]]
def raw18591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18591step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18591step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18591step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18591step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18591step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18591 raw18591Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw18591 raw18591Labels = mixedMoment B raw18591step0 raw18591step0Labels := by
      have ha : raw18591step0 = (fun i j => raw18591 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18591step0 raw18591; decide +kernel
      have hl : raw18591step0Labels = raw18591Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18591 raw18591Labels permutation240 permutation5
    mixedMoment B raw18591step0 raw18591step0Labels = mixedMoment B raw18591step1 raw18591step1Labels := by
      have ha : raw18591step1 = -raw18591step0 := by apply Matrix.ext; change ∀ i j, raw18591step1 i j = -(raw18591step0 i j); unfold raw18591step1 raw18591step0; decide +kernel
      have hl : raw18591step1Labels = raw18591step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18591step1 raw18591step1Labels = mixedMoment B raw18591step2 raw18591step2Labels := by
      have ha : raw18591step2 = raw18591step1 := by apply Matrix.ext; unfold raw18591step2 raw18591step1; decide +kernel
      have hl : raw18591step1Labels = labelEmbedding8 ∘ raw18591step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18591step1 raw18591step1Labels raw18591step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw18592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1]]
def raw18592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18592step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18592step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18592step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18592step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18592step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18592step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18592 raw18592Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw18592 raw18592Labels = mixedMoment B raw18592step0 raw18592step0Labels := by
      have ha : raw18592step0 = (fun i j => raw18592 (permutation260 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18592step0 raw18592; decide +kernel
      have hl : raw18592step0Labels = raw18592Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18592 raw18592Labels permutation260 permutation5
    mixedMoment B raw18592step0 raw18592step0Labels = mixedMoment B raw18592step1 raw18592step1Labels := by
      have ha : raw18592step1 = -raw18592step0 := by apply Matrix.ext; change ∀ i j, raw18592step1 i j = -(raw18592step0 i j); unfold raw18592step1 raw18592step0; decide +kernel
      have hl : raw18592step1Labels = raw18592step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18592step1 raw18592step1Labels = mixedMoment B raw18592step2 raw18592step2Labels := by
      have ha : raw18592step2 = raw18592step1 := by apply Matrix.ext; unfold raw18592step2 raw18592step1; decide +kernel
      have hl : raw18592step1Labels = labelEmbedding8 ∘ raw18592step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18592step1 raw18592step1Labels raw18592step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw18593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw18593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18593step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18593step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18593step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18593 raw18593Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw18593 raw18593Labels = mixedMoment B raw18593step0 raw18593step0Labels := by
      have ha : raw18593step0 = (fun i j => raw18593 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18593step0 raw18593; decide +kernel
      have hl : raw18593step0Labels = raw18593Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18593 raw18593Labels permutation153 permutation3
    mixedMoment B raw18593step0 raw18593step0Labels = mixedMoment B raw18593step1 raw18593step1Labels := by
      have ha : raw18593step1 = raw18593step0 := by apply Matrix.ext; unfold raw18593step1 raw18593step0; decide +kernel
      have hl : raw18593step0Labels = labelEmbedding6 ∘ raw18593step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18593step0 raw18593step0Labels raw18593step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4851 node4851Labels := by rfl

def raw18594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw18594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18594step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18594 raw18594Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw18594 raw18594Labels = mixedMoment B raw18594step0 raw18594step0Labels := by
      have ha : raw18594step0 = (fun i j => raw18594 (permutation266 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18594step0 raw18594; decide +kernel
      have hl : raw18594step0Labels = raw18594Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18594 raw18594Labels permutation266 permutation2
    _ = mixedMoment B node5380 node5380Labels := by rfl

def raw18595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw18595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18595step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18595step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18595step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18595 raw18595Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw18595 raw18595Labels = mixedMoment B raw18595step0 raw18595step0Labels := by
      have ha : raw18595step0 = (fun i j => raw18595 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18595step0 raw18595; decide +kernel
      have hl : raw18595step0Labels = raw18595Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18595 raw18595Labels permutation177 permutation3
    mixedMoment B raw18595step0 raw18595step0Labels = mixedMoment B raw18595step1 raw18595step1Labels := by
      have ha : raw18595step1 = raw18595step0 := by apply Matrix.ext; unfold raw18595step1 raw18595step0; decide +kernel
      have hl : raw18595step0Labels = labelEmbedding6 ∘ raw18595step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18595step0 raw18595step0Labels raw18595step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

def raw18596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw18596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18596step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18596step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18596step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18596step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18596step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18596 raw18596Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw18596 raw18596Labels = mixedMoment B raw18596step0 raw18596step0Labels := by
      have ha : raw18596step0 = (fun i j => raw18596 (permutation218 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18596step0 raw18596; decide +kernel
      have hl : raw18596step0Labels = raw18596Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18596 raw18596Labels permutation218 permutation5
    mixedMoment B raw18596step0 raw18596step0Labels = mixedMoment B raw18596step1 raw18596step1Labels := by
      have ha : raw18596step1 = -raw18596step0 := by apply Matrix.ext; change ∀ i j, raw18596step1 i j = -(raw18596step0 i j); unfold raw18596step1 raw18596step0; decide +kernel
      have hl : raw18596step1Labels = raw18596step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18596step1 raw18596step1Labels = mixedMoment B raw18596step2 raw18596step2Labels := by
      have ha : raw18596step2 = raw18596step1 := by apply Matrix.ext; unfold raw18596step2 raw18596step1; decide +kernel
      have hl : raw18596step1Labels = labelEmbedding8 ∘ raw18596step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18596step1 raw18596step1Labels raw18596step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw18597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1]]
def raw18597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18597step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18597step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18597step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18597step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18597step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18597 raw18597Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw18597 raw18597Labels = mixedMoment B raw18597step0 raw18597step0Labels := by
      have ha : raw18597step0 = (fun i j => raw18597 (permutation257 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18597step0 raw18597; decide +kernel
      have hl : raw18597step0Labels = raw18597Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18597 raw18597Labels permutation257 permutation5
    mixedMoment B raw18597step0 raw18597step0Labels = mixedMoment B raw18597step1 raw18597step1Labels := by
      have ha : raw18597step1 = -raw18597step0 := by apply Matrix.ext; change ∀ i j, raw18597step1 i j = -(raw18597step0 i j); unfold raw18597step1 raw18597step0; decide +kernel
      have hl : raw18597step1Labels = raw18597step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18597step1 raw18597step1Labels = mixedMoment B raw18597step2 raw18597step2Labels := by
      have ha : raw18597step2 = raw18597step1 := by apply Matrix.ext; unfold raw18597step2 raw18597step1; decide +kernel
      have hl : raw18597step1Labels = labelEmbedding8 ∘ raw18597step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18597step1 raw18597step1Labels raw18597step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw18598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18598step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18598step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18598step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18598 raw18598Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw18598 raw18598Labels = mixedMoment B raw18598step0 raw18598step0Labels := by
      have ha : raw18598step0 = (fun i j => raw18598 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18598step0 raw18598; decide +kernel
      have hl : raw18598step0Labels = raw18598Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18598 raw18598Labels permutation152 permutation3
    mixedMoment B raw18598step0 raw18598step0Labels = mixedMoment B raw18598step1 raw18598step1Labels := by
      have ha : raw18598step1 = raw18598step0 := by apply Matrix.ext; unfold raw18598step1 raw18598step0; decide +kernel
      have hl : raw18598step0Labels = labelEmbedding6 ∘ raw18598step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18598step0 raw18598step0Labels raw18598step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4851 node4851Labels := by rfl

def raw18599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18599step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18599 raw18599Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw18599 raw18599Labels = mixedMoment B raw18599step0 raw18599step0Labels := by
      have ha : raw18599step0 = (fun i j => raw18599 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18599step0 raw18599; decide +kernel
      have hl : raw18599step0Labels = raw18599Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18599 raw18599Labels permutation265 permutation2
    _ = mixedMoment B node5380 node5380Labels := by rfl

def raw18600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18600step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18600step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18600step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18600 raw18600Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw18600 raw18600Labels = mixedMoment B raw18600step0 raw18600step0Labels := by
      have ha : raw18600step0 = (fun i j => raw18600 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18600step0 raw18600; decide +kernel
      have hl : raw18600step0Labels = raw18600Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18600 raw18600Labels permutation176 permutation3
    mixedMoment B raw18600step0 raw18600step0Labels = mixedMoment B raw18600step1 raw18600step1Labels := by
      have ha : raw18600step1 = raw18600step0 := by apply Matrix.ext; unfold raw18600step1 raw18600step0; decide +kernel
      have hl : raw18600step0Labels = labelEmbedding6 ∘ raw18600step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18600step0 raw18600step0Labels raw18600step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

def raw18601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18601step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18601step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18601step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18601step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18601step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18601 raw18601Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw18601 raw18601Labels = mixedMoment B raw18601step0 raw18601step0Labels := by
      have ha : raw18601step0 = (fun i j => raw18601 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18601step0 raw18601; decide +kernel
      have hl : raw18601step0Labels = raw18601Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18601 raw18601Labels permutation212 permutation5
    mixedMoment B raw18601step0 raw18601step0Labels = mixedMoment B raw18601step1 raw18601step1Labels := by
      have ha : raw18601step1 = -raw18601step0 := by apply Matrix.ext; change ∀ i j, raw18601step1 i j = -(raw18601step0 i j); unfold raw18601step1 raw18601step0; decide +kernel
      have hl : raw18601step1Labels = raw18601step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18601step1 raw18601step1Labels = mixedMoment B raw18601step2 raw18601step2Labels := by
      have ha : raw18601step2 = raw18601step1 := by apply Matrix.ext; unfold raw18601step2 raw18601step1; decide +kernel
      have hl : raw18601step1Labels = labelEmbedding8 ∘ raw18601step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18601step1 raw18601step1Labels raw18601step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw18602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw18602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18602step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18602step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18602step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18602step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18602step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18602 raw18602Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw18602 raw18602Labels = mixedMoment B raw18602step0 raw18602step0Labels := by
      have ha : raw18602step0 = (fun i j => raw18602 (permutation234 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18602step0 raw18602; decide +kernel
      have hl : raw18602step0Labels = raw18602Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18602 raw18602Labels permutation234 permutation5
    mixedMoment B raw18602step0 raw18602step0Labels = mixedMoment B raw18602step1 raw18602step1Labels := by
      have ha : raw18602step1 = -raw18602step0 := by apply Matrix.ext; change ∀ i j, raw18602step1 i j = -(raw18602step0 i j); unfold raw18602step1 raw18602step0; decide +kernel
      have hl : raw18602step1Labels = raw18602step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18602step1 raw18602step1Labels = mixedMoment B raw18602step2 raw18602step2Labels := by
      have ha : raw18602step2 = raw18602step1 := by apply Matrix.ext; unfold raw18602step2 raw18602step1; decide +kernel
      have hl : raw18602step1Labels = labelEmbedding8 ∘ raw18602step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18602step1 raw18602step1Labels raw18602step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw18603 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18603step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18603step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18603 raw18603Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw18603 raw18603Labels = mixedMoment B raw18603step0 raw18603step0Labels := by
      have ha : raw18603step0 = (fun i j => raw18603 (permutation268 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18603step0 raw18603; decide +kernel
      have hl : raw18603step0Labels = raw18603Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18603 raw18603Labels permutation268 permutation2
    mixedMoment B raw18603step0 raw18603step0Labels = mixedMoment B raw18603step1 raw18603step1Labels := by
      have ha : raw18603step1 = -raw18603step0 := by apply Matrix.ext; change ∀ i j, raw18603step1 i j = -(raw18603step0 i j); unfold raw18603step1 raw18603step0; decide +kernel
      have hl : raw18603step1Labels = raw18603step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5469 node5469Labels := by rfl

def raw18604 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw18604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18604step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18604 raw18604Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw18604 raw18604Labels = mixedMoment B raw18604step0 raw18604step0Labels := by
      have ha : raw18604step0 = (fun i j => raw18604 (permutation266 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18604step0 raw18604; decide +kernel
      have hl : raw18604step0Labels = raw18604Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18604 raw18604Labels permutation266 permutation2
    mixedMoment B raw18604step0 raw18604step0Labels = mixedMoment B raw18604step1 raw18604step1Labels := by
      have ha : raw18604step1 = -raw18604step0 := by apply Matrix.ext; change ∀ i j, raw18604step1 i j = -(raw18604step0 i j); unfold raw18604step1 raw18604step0; decide +kernel
      have hl : raw18604step1Labels = raw18604step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5469 node5469Labels := by rfl

def raw18605 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18605step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18605step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18605 raw18605Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw18605 raw18605Labels = mixedMoment B raw18605step0 raw18605step0Labels := by
      have ha : raw18605step0 = (fun i j => raw18605 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18605step0 raw18605; decide +kernel
      have hl : raw18605step0Labels = raw18605Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18605 raw18605Labels permutation265 permutation2
    mixedMoment B raw18605step0 raw18605step0Labels = mixedMoment B raw18605step1 raw18605step1Labels := by
      have ha : raw18605step1 = -raw18605step0 := by apply Matrix.ext; change ∀ i j, raw18605step1 i j = -(raw18605step0 i j); unfold raw18605step1 raw18605step0; decide +kernel
      have hl : raw18605step1Labels = raw18605step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5469 node5469Labels := by rfl

def raw18606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw18606step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18606step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw18606step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18606step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw18606step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18606 raw18606Labels = mixedMoment B node5097 node5097Labels := by
  calc
    mixedMoment B raw18606 raw18606Labels = mixedMoment B raw18606step0 raw18606step0Labels := by
      have ha : raw18606step0 = (fun i j => raw18606 (permutation297 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18606step0 raw18606; decide +kernel
      have hl : raw18606step0Labels = raw18606Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18606 raw18606Labels permutation297 permutation3
    mixedMoment B raw18606step0 raw18606step0Labels = mixedMoment B raw18606step1 raw18606step1Labels := by
      have ha : raw18606step1 = -raw18606step0 := by apply Matrix.ext; change ∀ i j, raw18606step1 i j = -(raw18606step0 i j); unfold raw18606step1 raw18606step0; decide +kernel
      have hl : raw18606step1Labels = raw18606step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18606step1 raw18606step1Labels = mixedMoment B raw18606step2 raw18606step2Labels := by
      have ha : raw18606step2 = raw18606step1 := by apply Matrix.ext; unfold raw18606step2 raw18606step1; decide +kernel
      have hl : raw18606step1Labels = labelEmbedding6 ∘ raw18606step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18606step1 raw18606step1Labels raw18606step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5097 node5097Labels := by rfl

def raw18607 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw18607step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18607step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18607step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18607step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18607step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18607 raw18607Labels = mixedMoment B node5085 node5085Labels := by
  calc
    mixedMoment B raw18607 raw18607Labels = mixedMoment B raw18607step0 raw18607step0Labels := by
      have ha : raw18607step0 = (fun i j => raw18607 (permutation292 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18607step0 raw18607; decide +kernel
      have hl : raw18607step0Labels = raw18607Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18607 raw18607Labels permutation292 permutation3
    mixedMoment B raw18607step0 raw18607step0Labels = mixedMoment B raw18607step1 raw18607step1Labels := by
      have ha : raw18607step1 = -raw18607step0 := by apply Matrix.ext; change ∀ i j, raw18607step1 i j = -(raw18607step0 i j); unfold raw18607step1 raw18607step0; decide +kernel
      have hl : raw18607step1Labels = raw18607step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18607step1 raw18607step1Labels = mixedMoment B raw18607step2 raw18607step2Labels := by
      have ha : raw18607step2 = raw18607step1 := by apply Matrix.ext; unfold raw18607step2 raw18607step1; decide +kernel
      have hl : raw18607step1Labels = labelEmbedding6 ∘ raw18607step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18607step1 raw18607step1Labels raw18607step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5085 node5085Labels := by rfl

def raw18608 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw18608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw18608step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18608step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18608step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18608step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18608step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18608 raw18608Labels = mixedMoment B node5085 node5085Labels := by
  calc
    mixedMoment B raw18608 raw18608Labels = mixedMoment B raw18608step0 raw18608step0Labels := by
      have ha : raw18608step0 = (fun i j => raw18608 (permutation290 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18608step0 raw18608; decide +kernel
      have hl : raw18608step0Labels = raw18608Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18608 raw18608Labels permutation290 permutation3
    mixedMoment B raw18608step0 raw18608step0Labels = mixedMoment B raw18608step1 raw18608step1Labels := by
      have ha : raw18608step1 = -raw18608step0 := by apply Matrix.ext; change ∀ i j, raw18608step1 i j = -(raw18608step0 i j); unfold raw18608step1 raw18608step0; decide +kernel
      have hl : raw18608step1Labels = raw18608step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18608step1 raw18608step1Labels = mixedMoment B raw18608step2 raw18608step2Labels := by
      have ha : raw18608step2 = raw18608step1 := by apply Matrix.ext; unfold raw18608step2 raw18608step1; decide +kernel
      have hl : raw18608step1Labels = labelEmbedding6 ∘ raw18608step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18608step1 raw18608step1Labels raw18608step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5085 node5085Labels := by rfl

def raw18609 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw18609step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18609step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18609step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18609step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18609 raw18609Labels = mixedMoment B node5085 node5085Labels := by
  calc
    mixedMoment B raw18609 raw18609Labels = mixedMoment B raw18609step0 raw18609step0Labels := by
      have ha : raw18609step0 = (fun i j => raw18609 (permutation289 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18609step0 raw18609; decide +kernel
      have hl : raw18609step0Labels = raw18609Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18609 raw18609Labels permutation289 permutation3
    mixedMoment B raw18609step0 raw18609step0Labels = mixedMoment B raw18609step1 raw18609step1Labels := by
      have ha : raw18609step1 = -raw18609step0 := by apply Matrix.ext; change ∀ i j, raw18609step1 i j = -(raw18609step0 i j); unfold raw18609step1 raw18609step0; decide +kernel
      have hl : raw18609step1Labels = raw18609step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18609step1 raw18609step1Labels = mixedMoment B raw18609step2 raw18609step2Labels := by
      have ha : raw18609step2 = raw18609step1 := by apply Matrix.ext; unfold raw18609step2 raw18609step1; decide +kernel
      have hl : raw18609step1Labels = labelEmbedding6 ∘ raw18609step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18609step1 raw18609step1Labels raw18609step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5085 node5085Labels := by rfl

def raw18610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 2, 0]]
def raw18610step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18610step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw18610step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18610step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw18610step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18610 raw18610Labels = mixedMoment B node5277 node5277Labels := by
  calc
    mixedMoment B raw18610 raw18610Labels = mixedMoment B raw18610step0 raw18610step0Labels := by
      have ha : raw18610step0 = (fun i j => raw18610 (permutation216 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18610step0 raw18610; decide +kernel
      have hl : raw18610step0Labels = raw18610Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18610 raw18610Labels permutation216 permutation4
    mixedMoment B raw18610step0 raw18610step0Labels = mixedMoment B raw18610step1 raw18610step1Labels := by
      have ha : raw18610step1 = -raw18610step0 := by apply Matrix.ext; change ∀ i j, raw18610step1 i j = -(raw18610step0 i j); unfold raw18610step1 raw18610step0; decide +kernel
      have hl : raw18610step1Labels = raw18610step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18610step1 raw18610step1Labels = mixedMoment B raw18610step2 raw18610step2Labels := by
      have ha : raw18610step2 = raw18610step1 := by apply Matrix.ext; unfold raw18610step2 raw18610step1; decide +kernel
      have hl : raw18610step1Labels = labelEmbedding7 ∘ raw18610step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18610step1 raw18610step1Labels raw18610step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5277 node5277Labels := by rfl

def raw18611 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18611step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw18611step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18611step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18611step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18611step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18611step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18611 raw18611Labels = mixedMoment B node5359 node5359Labels := by
  calc
    mixedMoment B raw18611 raw18611Labels = mixedMoment B raw18611step0 raw18611step0Labels := by
      have ha : raw18611step0 = (fun i j => raw18611 (permutation369 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18611step0 raw18611; decide +kernel
      have hl : raw18611step0Labels = raw18611Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18611 raw18611Labels permutation369 permutation3
    mixedMoment B raw18611step0 raw18611step0Labels = mixedMoment B raw18611step1 raw18611step1Labels := by
      have ha : raw18611step1 = -raw18611step0 := by apply Matrix.ext; change ∀ i j, raw18611step1 i j = -(raw18611step0 i j); unfold raw18611step1 raw18611step0; decide +kernel
      have hl : raw18611step1Labels = raw18611step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18611step1 raw18611step1Labels = mixedMoment B raw18611step2 raw18611step2Labels := by
      have ha : raw18611step2 = raw18611step1 := by apply Matrix.ext; unfold raw18611step2 raw18611step1; decide +kernel
      have hl : raw18611step1Labels = labelEmbedding6 ∘ raw18611step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18611step1 raw18611step1Labels raw18611step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5359 node5359Labels := by rfl

def raw18612 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw18612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw18612step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18612step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18612step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18612step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18612step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18612 raw18612Labels = mixedMoment B node5359 node5359Labels := by
  calc
    mixedMoment B raw18612 raw18612Labels = mixedMoment B raw18612step0 raw18612step0Labels := by
      have ha : raw18612step0 = (fun i j => raw18612 (permutation368 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18612step0 raw18612; decide +kernel
      have hl : raw18612step0Labels = raw18612Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18612 raw18612Labels permutation368 permutation3
    mixedMoment B raw18612step0 raw18612step0Labels = mixedMoment B raw18612step1 raw18612step1Labels := by
      have ha : raw18612step1 = -raw18612step0 := by apply Matrix.ext; change ∀ i j, raw18612step1 i j = -(raw18612step0 i j); unfold raw18612step1 raw18612step0; decide +kernel
      have hl : raw18612step1Labels = raw18612step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18612step1 raw18612step1Labels = mixedMoment B raw18612step2 raw18612step2Labels := by
      have ha : raw18612step2 = raw18612step1 := by apply Matrix.ext; unfold raw18612step2 raw18612step1; decide +kernel
      have hl : raw18612step1Labels = labelEmbedding6 ∘ raw18612step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18612step1 raw18612step1Labels raw18612step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5359 node5359Labels := by rfl

def raw18613 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18613step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw18613step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18613step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18613step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18613step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18613step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18613 raw18613Labels = mixedMoment B node5359 node5359Labels := by
  calc
    mixedMoment B raw18613 raw18613Labels = mixedMoment B raw18613step0 raw18613step0Labels := by
      have ha : raw18613step0 = (fun i j => raw18613 (permutation367 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18613step0 raw18613; decide +kernel
      have hl : raw18613step0Labels = raw18613Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18613 raw18613Labels permutation367 permutation3
    mixedMoment B raw18613step0 raw18613step0Labels = mixedMoment B raw18613step1 raw18613step1Labels := by
      have ha : raw18613step1 = -raw18613step0 := by apply Matrix.ext; change ∀ i j, raw18613step1 i j = -(raw18613step0 i j); unfold raw18613step1 raw18613step0; decide +kernel
      have hl : raw18613step1Labels = raw18613step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18613step1 raw18613step1Labels = mixedMoment B raw18613step2 raw18613step2Labels := by
      have ha : raw18613step2 = raw18613step1 := by apply Matrix.ext; unfold raw18613step2 raw18613step1; decide +kernel
      have hl : raw18613step1Labels = labelEmbedding6 ∘ raw18613step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18613step1 raw18613step1Labels raw18613step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5359 node5359Labels := by rfl

def raw18614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18614step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18614step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18614step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18614step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18614step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18614 raw18614Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw18614 raw18614Labels = mixedMoment B raw18614step0 raw18614step0Labels := by
      have ha : raw18614step0 = (fun i j => raw18614 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18614step0 raw18614; decide +kernel
      have hl : raw18614step0Labels = raw18614Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18614 raw18614Labels permutation240 permutation4
    mixedMoment B raw18614step0 raw18614step0Labels = mixedMoment B raw18614step1 raw18614step1Labels := by
      have ha : raw18614step1 = -raw18614step0 := by apply Matrix.ext; change ∀ i j, raw18614step1 i j = -(raw18614step0 i j); unfold raw18614step1 raw18614step0; decide +kernel
      have hl : raw18614step1Labels = raw18614step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18614step1 raw18614step1Labels = mixedMoment B raw18614step2 raw18614step2Labels := by
      have ha : raw18614step2 = raw18614step1 := by apply Matrix.ext; unfold raw18614step2 raw18614step1; decide +kernel
      have hl : raw18614step1Labels = labelEmbedding7 ∘ raw18614step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18614step1 raw18614step1Labels raw18614step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw18615 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw18615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18615step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18615step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18615step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18615step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18615step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18615 raw18615Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw18615 raw18615Labels = mixedMoment B raw18615step0 raw18615step0Labels := by
      have ha : raw18615step0 = (fun i j => raw18615 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18615step0 raw18615; decide +kernel
      have hl : raw18615step0Labels = raw18615Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18615 raw18615Labels permutation240 permutation4
    mixedMoment B raw18615step0 raw18615step0Labels = mixedMoment B raw18615step1 raw18615step1Labels := by
      have ha : raw18615step1 = -raw18615step0 := by apply Matrix.ext; change ∀ i j, raw18615step1 i j = -(raw18615step0 i j); unfold raw18615step1 raw18615step0; decide +kernel
      have hl : raw18615step1Labels = raw18615step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18615step1 raw18615step1Labels = mixedMoment B raw18615step2 raw18615step2Labels := by
      have ha : raw18615step2 = raw18615step1 := by apply Matrix.ext; unfold raw18615step2 raw18615step1; decide +kernel
      have hl : raw18615step1Labels = labelEmbedding7 ∘ raw18615step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18615step1 raw18615step1Labels raw18615step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw18616 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18616step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18616step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18616step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18616step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18616step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18616 raw18616Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw18616 raw18616Labels = mixedMoment B raw18616step0 raw18616step0Labels := by
      have ha : raw18616step0 = (fun i j => raw18616 (permutation260 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18616step0 raw18616; decide +kernel
      have hl : raw18616step0Labels = raw18616Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18616 raw18616Labels permutation260 permutation4
    mixedMoment B raw18616step0 raw18616step0Labels = mixedMoment B raw18616step1 raw18616step1Labels := by
      have ha : raw18616step1 = -raw18616step0 := by apply Matrix.ext; change ∀ i j, raw18616step1 i j = -(raw18616step0 i j); unfold raw18616step1 raw18616step0; decide +kernel
      have hl : raw18616step1Labels = raw18616step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18616step1 raw18616step1Labels = mixedMoment B raw18616step2 raw18616step2Labels := by
      have ha : raw18616step2 = raw18616step1 := by apply Matrix.ext; unfold raw18616step2 raw18616step1; decide +kernel
      have hl : raw18616step1Labels = labelEmbedding7 ∘ raw18616step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18616step1 raw18616step1Labels raw18616step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw18617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18617step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18617step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18617step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18617step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18617step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18617step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18617 raw18617Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw18617 raw18617Labels = mixedMoment B raw18617step0 raw18617step0Labels := by
      have ha : raw18617step0 = (fun i j => raw18617 (permutation218 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18617step0 raw18617; decide +kernel
      have hl : raw18617step0Labels = raw18617Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18617 raw18617Labels permutation218 permutation4
    mixedMoment B raw18617step0 raw18617step0Labels = mixedMoment B raw18617step1 raw18617step1Labels := by
      have ha : raw18617step1 = -raw18617step0 := by apply Matrix.ext; change ∀ i j, raw18617step1 i j = -(raw18617step0 i j); unfold raw18617step1 raw18617step0; decide +kernel
      have hl : raw18617step1Labels = raw18617step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18617step1 raw18617step1Labels = mixedMoment B raw18617step2 raw18617step2Labels := by
      have ha : raw18617step2 = raw18617step1 := by apply Matrix.ext; unfold raw18617step2 raw18617step1; decide +kernel
      have hl : raw18617step1Labels = labelEmbedding7 ∘ raw18617step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18617step1 raw18617step1Labels raw18617step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw18618 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18618step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18618step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18618step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18618step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18618 raw18618Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw18618 raw18618Labels = mixedMoment B raw18618step0 raw18618step0Labels := by
      have ha : raw18618step0 = (fun i j => raw18618 (permutation218 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18618step0 raw18618; decide +kernel
      have hl : raw18618step0Labels = raw18618Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18618 raw18618Labels permutation218 permutation4
    mixedMoment B raw18618step0 raw18618step0Labels = mixedMoment B raw18618step1 raw18618step1Labels := by
      have ha : raw18618step1 = -raw18618step0 := by apply Matrix.ext; change ∀ i j, raw18618step1 i j = -(raw18618step0 i j); unfold raw18618step1 raw18618step0; decide +kernel
      have hl : raw18618step1Labels = raw18618step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18618step1 raw18618step1Labels = mixedMoment B raw18618step2 raw18618step2Labels := by
      have ha : raw18618step2 = raw18618step1 := by apply Matrix.ext; unfold raw18618step2 raw18618step1; decide +kernel
      have hl : raw18618step1Labels = labelEmbedding7 ∘ raw18618step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18618step1 raw18618step1Labels raw18618step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw18619 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18619step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18619step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18619step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18619step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18619step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18619 raw18619Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw18619 raw18619Labels = mixedMoment B raw18619step0 raw18619step0Labels := by
      have ha : raw18619step0 = (fun i j => raw18619 (permutation257 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18619step0 raw18619; decide +kernel
      have hl : raw18619step0Labels = raw18619Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18619 raw18619Labels permutation257 permutation4
    mixedMoment B raw18619step0 raw18619step0Labels = mixedMoment B raw18619step1 raw18619step1Labels := by
      have ha : raw18619step1 = -raw18619step0 := by apply Matrix.ext; change ∀ i j, raw18619step1 i j = -(raw18619step0 i j); unfold raw18619step1 raw18619step0; decide +kernel
      have hl : raw18619step1Labels = raw18619step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18619step1 raw18619step1Labels = mixedMoment B raw18619step2 raw18619step2Labels := by
      have ha : raw18619step2 = raw18619step1 := by apply Matrix.ext; unfold raw18619step2 raw18619step1; decide +kernel
      have hl : raw18619step1Labels = labelEmbedding7 ∘ raw18619step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18619step1 raw18619step1Labels raw18619step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw18620 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18620step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18620step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18620step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18620 raw18620Labels = mixedMoment B node3975 node3975Labels := by
  calc
    mixedMoment B raw18620 raw18620Labels = mixedMoment B raw18620step0 raw18620step0Labels := by
      have ha : raw18620step0 = (fun i j => raw18620 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18620step0 raw18620; decide +kernel
      have hl : raw18620step0Labels = raw18620Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18620 raw18620Labels permutation152 permutation7
    mixedMoment B raw18620step0 raw18620step0Labels = mixedMoment B raw18620step1 raw18620step1Labels := by
      have ha : raw18620step1 = raw18620step0 := by apply Matrix.ext; unfold raw18620step1 raw18620step0; decide +kernel
      have hl : raw18620step0Labels = labelEmbedding1 ∘ raw18620step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18620step0 raw18620step0Labels raw18620step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3975 node3975Labels := by rfl

def raw18621 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18621step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18621step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18621step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18621 raw18621Labels = mixedMoment B node3962 node3962Labels := by
  calc
    mixedMoment B raw18621 raw18621Labels = mixedMoment B raw18621step0 raw18621step0Labels := by
      have hz : ∀ j, raw18621 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18621step0 = (fun i j => raw18621 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18621step0 raw18621; decide +kernel
      have hl : raw18621step0Labels = raw18621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18621 raw18621Labels permutation346 hz
    mixedMoment B raw18621step0 raw18621step0Labels = mixedMoment B raw18621step1 raw18621step1Labels := by
      have ha : raw18621step1 = (fun i j => raw18621step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18621step1 raw18621step0; decide +kernel
      have hl : raw18621step1Labels = raw18621step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18621step0 raw18621step0Labels permutation32 permutation7
    mixedMoment B raw18621step1 raw18621step1Labels = mixedMoment B raw18621step2 raw18621step2Labels := by
      have ha : raw18621step2 = raw18621step1 := by apply Matrix.ext; unfold raw18621step2 raw18621step1; decide +kernel
      have hl : raw18621step1Labels = labelEmbedding1 ∘ raw18621step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18621step1 raw18621step1Labels raw18621step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3962 node3962Labels := by rfl

def raw18622 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18622Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18622step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18622step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18622step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18622 raw18622Labels = mixedMoment B node3952 node3952Labels := by
  calc
    mixedMoment B raw18622 raw18622Labels = mixedMoment B raw18622step0 raw18622step0Labels := by
      have ha : raw18622step0 = (fun i j => raw18622 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18622step0 raw18622; decide +kernel
      have hl : raw18622step0Labels = raw18622Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18622 raw18622Labels permutation155 permutation7
    mixedMoment B raw18622step0 raw18622step0Labels = mixedMoment B raw18622step1 raw18622step1Labels := by
      have ha : raw18622step1 = raw18622step0 := by apply Matrix.ext; unfold raw18622step1 raw18622step0; decide +kernel
      have hl : raw18622step0Labels = labelEmbedding1 ∘ raw18622step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18622step0 raw18622step0Labels raw18622step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3952 node3952Labels := by rfl

def raw18623 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw18623Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18623step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18623step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18623step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18623 raw18623Labels = mixedMoment B node3952 node3952Labels := by
  calc
    mixedMoment B raw18623 raw18623Labels = mixedMoment B raw18623step0 raw18623step0Labels := by
      have ha : raw18623step0 = (fun i j => raw18623 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18623step0 raw18623; decide +kernel
      have hl : raw18623step0Labels = raw18623Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18623 raw18623Labels permutation153 permutation7
    mixedMoment B raw18623step0 raw18623step0Labels = mixedMoment B raw18623step1 raw18623step1Labels := by
      have ha : raw18623step1 = raw18623step0 := by apply Matrix.ext; unfold raw18623step1 raw18623step0; decide +kernel
      have hl : raw18623step0Labels = labelEmbedding1 ∘ raw18623step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18623step0 raw18623step0Labels raw18623step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3952 node3952Labels := by rfl

def raw18624 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18624step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18624step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18624 raw18624Labels = mixedMoment B node3952 node3952Labels := by
  calc
    mixedMoment B raw18624 raw18624Labels = mixedMoment B raw18624step0 raw18624step0Labels := by
      have ha : raw18624step0 = (fun i j => raw18624 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18624step0 raw18624; decide +kernel
      have hl : raw18624step0Labels = raw18624Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18624 raw18624Labels permutation152 permutation7
    mixedMoment B raw18624step0 raw18624step0Labels = mixedMoment B raw18624step1 raw18624step1Labels := by
      have ha : raw18624step1 = raw18624step0 := by apply Matrix.ext; unfold raw18624step1 raw18624step0; decide +kernel
      have hl : raw18624step0Labels = labelEmbedding1 ∘ raw18624step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18624step0 raw18624step0Labels raw18624step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3952 node3952Labels := by rfl

def raw18625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18625Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw18625step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18625step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw18625step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18625step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw18625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18625 raw18625Labels = mixedMoment B node3058 node3058Labels := by
  calc
    mixedMoment B raw18625 raw18625Labels = mixedMoment B raw18625step0 raw18625step0Labels := by
      have ha : raw18625step0 = (fun i j => raw18625 (permutation217 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18625step0 raw18625; decide +kernel
      have hl : raw18625step0Labels = raw18625Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18625 raw18625Labels permutation217 permutation5
    mixedMoment B raw18625step0 raw18625step0Labels = mixedMoment B raw18625step1 raw18625step1Labels := by
      have ha : raw18625step1 = -raw18625step0 := by apply Matrix.ext; change ∀ i j, raw18625step1 i j = -(raw18625step0 i j); unfold raw18625step1 raw18625step0; decide +kernel
      have hl : raw18625step1Labels = raw18625step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18625step1 raw18625step1Labels = mixedMoment B raw18625step2 raw18625step2Labels := by
      have ha : raw18625step2 = raw18625step1 := by apply Matrix.ext; unfold raw18625step2 raw18625step1; decide +kernel
      have hl : raw18625step1Labels = labelEmbedding1 ∘ raw18625step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18625step1 raw18625step1Labels raw18625step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3058 node3058Labels := by rfl

def raw18626 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18626step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18626step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18626step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18626step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18626 raw18626Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw18626 raw18626Labels = mixedMoment B raw18626step0 raw18626step0Labels := by
      have hz : ∀ j, raw18626 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18626step0 = (fun i j => raw18626 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18626step0 raw18626; decide +kernel
      have hl : raw18626step0Labels = raw18626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18626 raw18626Labels permutation346 hz
    mixedMoment B raw18626step0 raw18626step0Labels = mixedMoment B raw18626step1 raw18626step1Labels := by
      have ha : raw18626step1 = (fun i j => raw18626step0 (permutation65 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18626step1 raw18626step0; decide +kernel
      have hl : raw18626step1Labels = raw18626step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18626step0 raw18626step0Labels permutation65 permutation5
    mixedMoment B raw18626step1 raw18626step1Labels = mixedMoment B raw18626step2 raw18626step2Labels := by
      have ha : raw18626step2 = raw18626step1 := by apply Matrix.ext; unfold raw18626step2 raw18626step1; decide +kernel
      have hl : raw18626step1Labels = labelEmbedding1 ∘ raw18626step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18626step1 raw18626step1Labels raw18626step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3619 node3619Labels := by rfl

def raw18627 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18627Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18627step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18627step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18627step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18627 raw18627Labels = mixedMoment B node3461 node3461Labels := by
  calc
    mixedMoment B raw18627 raw18627Labels = mixedMoment B raw18627step0 raw18627step0Labels := by
      have ha : raw18627step0 = (fun i j => raw18627 (permutation302 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18627step0 raw18627; decide +kernel
      have hl : raw18627step0Labels = raw18627Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18627 raw18627Labels permutation302 permutation5
    mixedMoment B raw18627step0 raw18627step0Labels = mixedMoment B raw18627step1 raw18627step1Labels := by
      have ha : raw18627step1 = raw18627step0 := by apply Matrix.ext; unfold raw18627step1 raw18627step0; decide +kernel
      have hl : raw18627step0Labels = labelEmbedding1 ∘ raw18627step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18627step0 raw18627step0Labels raw18627step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3461 node3461Labels := by rfl

def raw18628 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw18628Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18628step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18628step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18628 raw18628Labels = mixedMoment B node3461 node3461Labels := by
  calc
    mixedMoment B raw18628 raw18628Labels = mixedMoment B raw18628step0 raw18628step0Labels := by
      have ha : raw18628step0 = (fun i j => raw18628 (permutation298 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18628step0 raw18628; decide +kernel
      have hl : raw18628step0Labels = raw18628Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18628 raw18628Labels permutation298 permutation5
    mixedMoment B raw18628step0 raw18628step0Labels = mixedMoment B raw18628step1 raw18628step1Labels := by
      have ha : raw18628step1 = raw18628step0 := by apply Matrix.ext; unfold raw18628step1 raw18628step0; decide +kernel
      have hl : raw18628step0Labels = labelEmbedding1 ∘ raw18628step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18628step0 raw18628step0Labels raw18628step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3461 node3461Labels := by rfl

def raw18629 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18629Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18629step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18629step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18629step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18629 raw18629Labels = mixedMoment B node3461 node3461Labels := by
  calc
    mixedMoment B raw18629 raw18629Labels = mixedMoment B raw18629step0 raw18629step0Labels := by
      have ha : raw18629step0 = (fun i j => raw18629 (permutation297 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18629step0 raw18629; decide +kernel
      have hl : raw18629step0Labels = raw18629Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18629 raw18629Labels permutation297 permutation5
    mixedMoment B raw18629step0 raw18629step0Labels = mixedMoment B raw18629step1 raw18629step1Labels := by
      have ha : raw18629step1 = raw18629step0 := by apply Matrix.ext; unfold raw18629step1 raw18629step0; decide +kernel
      have hl : raw18629step0Labels = labelEmbedding1 ∘ raw18629step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18629step0 raw18629step0Labels raw18629step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3461 node3461Labels := by rfl

def raw18630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18630Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw18630step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18630step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18630step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18630step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18630step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18630 raw18630Labels = mixedMoment B node3059 node3059Labels := by
  calc
    mixedMoment B raw18630 raw18630Labels = mixedMoment B raw18630step0 raw18630step0Labels := by
      have ha : raw18630step0 = (fun i j => raw18630 (permutation216 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18630step0 raw18630; decide +kernel
      have hl : raw18630step0Labels = raw18630Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18630 raw18630Labels permutation216 permutation5
    mixedMoment B raw18630step0 raw18630step0Labels = mixedMoment B raw18630step1 raw18630step1Labels := by
      have ha : raw18630step1 = -raw18630step0 := by apply Matrix.ext; change ∀ i j, raw18630step1 i j = -(raw18630step0 i j); unfold raw18630step1 raw18630step0; decide +kernel
      have hl : raw18630step1Labels = raw18630step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18630step1 raw18630step1Labels = mixedMoment B raw18630step2 raw18630step2Labels := by
      have ha : raw18630step2 = raw18630step1 := by apply Matrix.ext; unfold raw18630step2 raw18630step1; decide +kernel
      have hl : raw18630step1Labels = labelEmbedding1 ∘ raw18630step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18630step1 raw18630step1Labels raw18630step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3059 node3059Labels := by rfl

def raw18631 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18631Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18631step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18631step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18631 raw18631Labels = mixedMoment B node3899 node3899Labels := by
  calc
    mixedMoment B raw18631 raw18631Labels = mixedMoment B raw18631step0 raw18631step0Labels := by
      have ha : raw18631step0 = (fun i j => raw18631 (permutation373 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18631step0 raw18631; decide +kernel
      have hl : raw18631step0Labels = raw18631Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18631 raw18631Labels permutation373 permutation5
    mixedMoment B raw18631step0 raw18631step0Labels = mixedMoment B raw18631step1 raw18631step1Labels := by
      have ha : raw18631step1 = raw18631step0 := by apply Matrix.ext; unfold raw18631step1 raw18631step0; decide +kernel
      have hl : raw18631step0Labels = labelEmbedding1 ∘ raw18631step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18631step0 raw18631step0Labels raw18631step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3899 node3899Labels := by rfl

def raw18632 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18632Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18632step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18632 raw18632Labels = mixedMoment B node3759 node3759Labels := by
  calc
    mixedMoment B raw18632 raw18632Labels = mixedMoment B raw18632step0 raw18632step0Labels := by
      have ha : raw18632step0 = (fun i j => raw18632 (permutation378 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18632step0 raw18632; decide +kernel
      have hl : raw18632step0Labels = raw18632Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18632 raw18632Labels permutation378 permutation5
    mixedMoment B raw18632step0 raw18632step0Labels = mixedMoment B raw18632step1 raw18632step1Labels := by
      have ha : raw18632step1 = raw18632step0 := by apply Matrix.ext; unfold raw18632step1 raw18632step0; decide +kernel
      have hl : raw18632step0Labels = labelEmbedding1 ∘ raw18632step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18632step0 raw18632step0Labels raw18632step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3759 node3759Labels := by rfl

def raw18633 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw18633Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18633step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18633step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18633 raw18633Labels = mixedMoment B node3759 node3759Labels := by
  calc
    mixedMoment B raw18633 raw18633Labels = mixedMoment B raw18633step0 raw18633step0Labels := by
      have ha : raw18633step0 = (fun i j => raw18633 (permutation374 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18633step0 raw18633; decide +kernel
      have hl : raw18633step0Labels = raw18633Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18633 raw18633Labels permutation374 permutation5
    mixedMoment B raw18633step0 raw18633step0Labels = mixedMoment B raw18633step1 raw18633step1Labels := by
      have ha : raw18633step1 = raw18633step0 := by apply Matrix.ext; unfold raw18633step1 raw18633step0; decide +kernel
      have hl : raw18633step0Labels = labelEmbedding1 ∘ raw18633step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18633step0 raw18633step0Labels raw18633step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3759 node3759Labels := by rfl

def raw18634 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18634Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18634step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18634step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18634 raw18634Labels = mixedMoment B node3759 node3759Labels := by
  calc
    mixedMoment B raw18634 raw18634Labels = mixedMoment B raw18634step0 raw18634step0Labels := by
      have ha : raw18634step0 = (fun i j => raw18634 (permutation373 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18634step0 raw18634; decide +kernel
      have hl : raw18634step0Labels = raw18634Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18634 raw18634Labels permutation373 permutation5
    mixedMoment B raw18634step0 raw18634step0Labels = mixedMoment B raw18634step1 raw18634step1Labels := by
      have ha : raw18634step1 = raw18634step0 := by apply Matrix.ext; unfold raw18634step1 raw18634step0; decide +kernel
      have hl : raw18634step0Labels = labelEmbedding1 ∘ raw18634step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18634step0 raw18634step0Labels raw18634step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3759 node3759Labels := by rfl

def raw18635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18635Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18635step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18635step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18635step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18635step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18635step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18635 raw18635Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw18635 raw18635Labels = mixedMoment B raw18635step0 raw18635step0Labels := by
      have ha : raw18635step0 = (fun i j => raw18635 (permutation245 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18635step0 raw18635; decide +kernel
      have hl : raw18635step0Labels = raw18635Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18635 raw18635Labels permutation245 permutation5
    mixedMoment B raw18635step0 raw18635step0Labels = mixedMoment B raw18635step1 raw18635step1Labels := by
      have ha : raw18635step1 = -raw18635step0 := by apply Matrix.ext; change ∀ i j, raw18635step1 i j = -(raw18635step0 i j); unfold raw18635step1 raw18635step0; decide +kernel
      have hl : raw18635step1Labels = raw18635step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18635step1 raw18635step1Labels = mixedMoment B raw18635step2 raw18635step2Labels := by
      have ha : raw18635step2 = raw18635step1 := by apply Matrix.ext; unfold raw18635step2 raw18635step1; decide +kernel
      have hl : raw18635step1Labels = labelEmbedding1 ∘ raw18635step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18635step1 raw18635step1Labels raw18635step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw18636 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18636Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18636step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18636step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18636 raw18636Labels = mixedMoment B node4033 node4033Labels := by
  calc
    mixedMoment B raw18636 raw18636Labels = mixedMoment B raw18636step0 raw18636step0Labels := by
      have ha : raw18636step0 = (fun i j => raw18636 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18636step0 raw18636; decide +kernel
      have hl : raw18636step0Labels = raw18636Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18636 raw18636Labels permutation152 permutation7
    mixedMoment B raw18636step0 raw18636step0Labels = mixedMoment B raw18636step1 raw18636step1Labels := by
      have ha : raw18636step1 = raw18636step0 := by apply Matrix.ext; unfold raw18636step1 raw18636step0; decide +kernel
      have hl : raw18636step0Labels = labelEmbedding1 ∘ raw18636step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18636step0 raw18636step0Labels raw18636step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4033 node4033Labels := by rfl

def raw18637 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18637Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18637step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18637step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18637 raw18637Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw18637 raw18637Labels = mixedMoment B raw18637step0 raw18637step0Labels := by
      have hz : ∀ j, raw18637 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18637step0 = (fun i j => raw18637 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18637step0 raw18637; decide +kernel
      have hl : raw18637step0Labels = raw18637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18637 raw18637Labels permutation346 hz
    mixedMoment B raw18637step0 raw18637step0Labels = mixedMoment B raw18637step1 raw18637step1Labels := by
      have ha : raw18637step1 = (fun i j => raw18637step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18637step1 raw18637step0; decide +kernel
      have hl : raw18637step1Labels = raw18637step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18637step0 raw18637step0Labels permutation32 permutation7
    mixedMoment B raw18637step1 raw18637step1Labels = mixedMoment B raw18637step2 raw18637step2Labels := by
      have ha : raw18637step2 = raw18637step1 := by apply Matrix.ext; unfold raw18637step2 raw18637step1; decide +kernel
      have hl : raw18637step1Labels = labelEmbedding1 ∘ raw18637step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18637step1 raw18637step1Labels raw18637step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw18638 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw18638Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18638step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18638step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18638step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18638step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18638step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18638step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18638 raw18638Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw18638 raw18638Labels = mixedMoment B raw18638step0 raw18638step0Labels := by
      have ha : raw18638step0 = (fun i j => raw18638 (permutation245 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18638step0 raw18638; decide +kernel
      have hl : raw18638step0Labels = raw18638Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18638 raw18638Labels permutation245 permutation5
    mixedMoment B raw18638step0 raw18638step0Labels = mixedMoment B raw18638step1 raw18638step1Labels := by
      have ha : raw18638step1 = -raw18638step0 := by apply Matrix.ext; change ∀ i j, raw18638step1 i j = -(raw18638step0 i j); unfold raw18638step1 raw18638step0; decide +kernel
      have hl : raw18638step1Labels = raw18638step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18638step1 raw18638step1Labels = mixedMoment B raw18638step2 raw18638step2Labels := by
      have ha : raw18638step2 = raw18638step1 := by apply Matrix.ext; unfold raw18638step2 raw18638step1; decide +kernel
      have hl : raw18638step1Labels = labelEmbedding1 ∘ raw18638step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18638step1 raw18638step1Labels raw18638step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4024 node4024Labels := by rfl

def raw18639 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18639Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18639step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18639step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18639step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18639step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18639step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18639 raw18639Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw18639 raw18639Labels = mixedMoment B raw18639step0 raw18639step0Labels := by
      have ha : raw18639step0 = (fun i j => raw18639 (permutation264 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18639step0 raw18639; decide +kernel
      have hl : raw18639step0Labels = raw18639Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18639 raw18639Labels permutation264 permutation5
    mixedMoment B raw18639step0 raw18639step0Labels = mixedMoment B raw18639step1 raw18639step1Labels := by
      have ha : raw18639step1 = -raw18639step0 := by apply Matrix.ext; change ∀ i j, raw18639step1 i j = -(raw18639step0 i j); unfold raw18639step1 raw18639step0; decide +kernel
      have hl : raw18639step1Labels = raw18639step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18639step1 raw18639step1Labels = mixedMoment B raw18639step2 raw18639step2Labels := by
      have ha : raw18639step2 = raw18639step1 := by apply Matrix.ext; unfold raw18639step2 raw18639step1; decide +kernel
      have hl : raw18639step1Labels = labelEmbedding1 ∘ raw18639step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18639step1 raw18639step1Labels raw18639step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4024 node4024Labels := by rfl

def raw18640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18640Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18640step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18640step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18640step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18640step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18640step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18640 raw18640Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw18640 raw18640Labels = mixedMoment B raw18640step0 raw18640step0Labels := by
      have ha : raw18640step0 = (fun i j => raw18640 (permutation223 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18640step0 raw18640; decide +kernel
      have hl : raw18640step0Labels = raw18640Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18640 raw18640Labels permutation223 permutation5
    mixedMoment B raw18640step0 raw18640step0Labels = mixedMoment B raw18640step1 raw18640step1Labels := by
      have ha : raw18640step1 = -raw18640step0 := by apply Matrix.ext; change ∀ i j, raw18640step1 i j = -(raw18640step0 i j); unfold raw18640step1 raw18640step0; decide +kernel
      have hl : raw18640step1Labels = raw18640step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18640step1 raw18640step1Labels = mixedMoment B raw18640step2 raw18640step2Labels := by
      have ha : raw18640step2 = raw18640step1 := by apply Matrix.ext; unfold raw18640step2 raw18640step1; decide +kernel
      have hl : raw18640step1Labels = labelEmbedding1 ∘ raw18640step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18640step1 raw18640step1Labels raw18640step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw18641 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18641Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18641step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18641step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18641step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18641 raw18641Labels = mixedMoment B node4033 node4033Labels := by
  calc
    mixedMoment B raw18641 raw18641Labels = mixedMoment B raw18641step0 raw18641step0Labels := by
      have ha : raw18641step0 = (fun i j => raw18641 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18641step0 raw18641; decide +kernel
      have hl : raw18641step0Labels = raw18641Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18641 raw18641Labels permutation154 permutation7
    mixedMoment B raw18641step0 raw18641step0Labels = mixedMoment B raw18641step1 raw18641step1Labels := by
      have ha : raw18641step1 = raw18641step0 := by apply Matrix.ext; unfold raw18641step1 raw18641step0; decide +kernel
      have hl : raw18641step0Labels = labelEmbedding1 ∘ raw18641step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18641step0 raw18641step0Labels raw18641step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4033 node4033Labels := by rfl

def raw18642 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18642Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18642step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18642step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18642step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18642step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18642 raw18642Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw18642 raw18642Labels = mixedMoment B raw18642step0 raw18642step0Labels := by
      have hz : ∀ j, raw18642 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18642step0 = (fun i j => raw18642 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18642step0 raw18642; decide +kernel
      have hl : raw18642step0Labels = raw18642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18642 raw18642Labels permutation346 hz
    mixedMoment B raw18642step0 raw18642step0Labels = mixedMoment B raw18642step1 raw18642step1Labels := by
      have ha : raw18642step1 = (fun i j => raw18642step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18642step1 raw18642step0; decide +kernel
      have hl : raw18642step1Labels = raw18642step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18642step0 raw18642step0Labels permutation34 permutation7
    mixedMoment B raw18642step1 raw18642step1Labels = mixedMoment B raw18642step2 raw18642step2Labels := by
      have ha : raw18642step2 = raw18642step1 := by apply Matrix.ext; unfold raw18642step2 raw18642step1; decide +kernel
      have hl : raw18642step1Labels = labelEmbedding1 ∘ raw18642step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18642step1 raw18642step1Labels raw18642step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw18643 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18643Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18643step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18643step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18643step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18643step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18643step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18643 raw18643Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw18643 raw18643Labels = mixedMoment B raw18643step0 raw18643step0Labels := by
      have ha : raw18643step0 = (fun i j => raw18643 (permutation223 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18643step0 raw18643; decide +kernel
      have hl : raw18643step0Labels = raw18643Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18643 raw18643Labels permutation223 permutation5
    mixedMoment B raw18643step0 raw18643step0Labels = mixedMoment B raw18643step1 raw18643step1Labels := by
      have ha : raw18643step1 = -raw18643step0 := by apply Matrix.ext; change ∀ i j, raw18643step1 i j = -(raw18643step0 i j); unfold raw18643step1 raw18643step0; decide +kernel
      have hl : raw18643step1Labels = raw18643step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18643step1 raw18643step1Labels = mixedMoment B raw18643step2 raw18643step2Labels := by
      have ha : raw18643step2 = raw18643step1 := by apply Matrix.ext; unfold raw18643step2 raw18643step1; decide +kernel
      have hl : raw18643step1Labels = labelEmbedding1 ∘ raw18643step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18643step1 raw18643step1Labels raw18643step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4024 node4024Labels := by rfl

def raw18644 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw18644Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18644step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18644step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18644step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18644step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18644 raw18644Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw18644 raw18644Labels = mixedMoment B raw18644step0 raw18644step0Labels := by
      have ha : raw18644step0 = (fun i j => raw18644 (permutation259 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18644step0 raw18644; decide +kernel
      have hl : raw18644step0Labels = raw18644Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18644 raw18644Labels permutation259 permutation5
    mixedMoment B raw18644step0 raw18644step0Labels = mixedMoment B raw18644step1 raw18644step1Labels := by
      have ha : raw18644step1 = -raw18644step0 := by apply Matrix.ext; change ∀ i j, raw18644step1 i j = -(raw18644step0 i j); unfold raw18644step1 raw18644step0; decide +kernel
      have hl : raw18644step1Labels = raw18644step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18644step1 raw18644step1Labels = mixedMoment B raw18644step2 raw18644step2Labels := by
      have ha : raw18644step2 = raw18644step1 := by apply Matrix.ext; unfold raw18644step2 raw18644step1; decide +kernel
      have hl : raw18644step1Labels = labelEmbedding1 ∘ raw18644step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18644step1 raw18644step1Labels raw18644step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4024 node4024Labels := by rfl

def raw18645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18645Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18645step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18645step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18645step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18645step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18645step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18645 raw18645Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw18645 raw18645Labels = mixedMoment B raw18645step0 raw18645step0Labels := by
      have ha : raw18645step0 = (fun i j => raw18645 (permutation217 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18645step0 raw18645; decide +kernel
      have hl : raw18645step0Labels = raw18645Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18645 raw18645Labels permutation217 permutation5
    mixedMoment B raw18645step0 raw18645step0Labels = mixedMoment B raw18645step1 raw18645step1Labels := by
      have ha : raw18645step1 = -raw18645step0 := by apply Matrix.ext; change ∀ i j, raw18645step1 i j = -(raw18645step0 i j); unfold raw18645step1 raw18645step0; decide +kernel
      have hl : raw18645step1Labels = raw18645step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18645step1 raw18645step1Labels = mixedMoment B raw18645step2 raw18645step2Labels := by
      have ha : raw18645step2 = raw18645step1 := by apply Matrix.ext; unfold raw18645step2 raw18645step1; decide +kernel
      have hl : raw18645step1Labels = labelEmbedding1 ∘ raw18645step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18645step1 raw18645step1Labels raw18645step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw18646 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18646Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18646step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18646step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18646 raw18646Labels = mixedMoment B node4033 node4033Labels := by
  calc
    mixedMoment B raw18646 raw18646Labels = mixedMoment B raw18646step0 raw18646step0Labels := by
      have ha : raw18646step0 = (fun i j => raw18646 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18646step0 raw18646; decide +kernel
      have hl : raw18646step0Labels = raw18646Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18646 raw18646Labels permutation156 permutation7
    mixedMoment B raw18646step0 raw18646step0Labels = mixedMoment B raw18646step1 raw18646step1Labels := by
      have ha : raw18646step1 = raw18646step0 := by apply Matrix.ext; unfold raw18646step1 raw18646step0; decide +kernel
      have hl : raw18646step0Labels = labelEmbedding1 ∘ raw18646step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18646step0 raw18646step0Labels raw18646step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4033 node4033Labels := by rfl

def raw18647 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18647Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18647step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18647step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18647step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18647 raw18647Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw18647 raw18647Labels = mixedMoment B raw18647step0 raw18647step0Labels := by
      have hz : ∀ j, raw18647 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18647step0 = (fun i j => raw18647 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18647step0 raw18647; decide +kernel
      have hl : raw18647step0Labels = raw18647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18647 raw18647Labels permutation346 hz
    mixedMoment B raw18647step0 raw18647step0Labels = mixedMoment B raw18647step1 raw18647step1Labels := by
      have ha : raw18647step1 = (fun i j => raw18647step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18647step1 raw18647step0; decide +kernel
      have hl : raw18647step1Labels = raw18647step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18647step0 raw18647step0Labels permutation36 permutation7
    mixedMoment B raw18647step1 raw18647step1Labels = mixedMoment B raw18647step2 raw18647step2Labels := by
      have ha : raw18647step2 = raw18647step1 := by apply Matrix.ext; unfold raw18647step2 raw18647step1; decide +kernel
      have hl : raw18647step1Labels = labelEmbedding1 ∘ raw18647step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18647step1 raw18647step1Labels raw18647step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw18648 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18648Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18648step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18648step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18648step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18648 raw18648Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw18648 raw18648Labels = mixedMoment B raw18648step0 raw18648step0Labels := by
      have ha : raw18648step0 = (fun i j => raw18648 (permutation217 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18648step0 raw18648; decide +kernel
      have hl : raw18648step0Labels = raw18648Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18648 raw18648Labels permutation217 permutation5
    mixedMoment B raw18648step0 raw18648step0Labels = mixedMoment B raw18648step1 raw18648step1Labels := by
      have ha : raw18648step1 = -raw18648step0 := by apply Matrix.ext; change ∀ i j, raw18648step1 i j = -(raw18648step0 i j); unfold raw18648step1 raw18648step0; decide +kernel
      have hl : raw18648step1Labels = raw18648step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18648step1 raw18648step1Labels = mixedMoment B raw18648step2 raw18648step2Labels := by
      have ha : raw18648step2 = raw18648step1 := by apply Matrix.ext; unfold raw18648step2 raw18648step1; decide +kernel
      have hl : raw18648step1Labels = labelEmbedding1 ∘ raw18648step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18648step1 raw18648step1Labels raw18648step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4024 node4024Labels := by rfl

def raw18649 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18649Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw18649step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18649step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18649step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18649step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18649 raw18649Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw18649 raw18649Labels = mixedMoment B raw18649step0 raw18649step0Labels := by
      have ha : raw18649step0 = (fun i j => raw18649 (permutation239 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18649step0 raw18649; decide +kernel
      have hl : raw18649step0Labels = raw18649Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18649 raw18649Labels permutation239 permutation5
    mixedMoment B raw18649step0 raw18649step0Labels = mixedMoment B raw18649step1 raw18649step1Labels := by
      have ha : raw18649step1 = -raw18649step0 := by apply Matrix.ext; change ∀ i j, raw18649step1 i j = -(raw18649step0 i j); unfold raw18649step1 raw18649step0; decide +kernel
      have hl : raw18649step1Labels = raw18649step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18649step1 raw18649step1Labels = mixedMoment B raw18649step2 raw18649step2Labels := by
      have ha : raw18649step2 = raw18649step1 := by apply Matrix.ext; unfold raw18649step2 raw18649step1; decide +kernel
      have hl : raw18649step1Labels = labelEmbedding1 ∘ raw18649step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18649step1 raw18649step1Labels raw18649step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4024 node4024Labels := by rfl

def raw18650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18650step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18650step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18650 raw18650Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw18650 raw18650Labels = mixedMoment B raw18650step0 raw18650step0Labels := by
      have hz : ∀ j, raw18650 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18650step0 = (fun i j => raw18650 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18650step0 raw18650; decide +kernel
      have hl : raw18650step0Labels = raw18650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18650 raw18650Labels permutation346 hz
    mixedMoment B raw18650step0 raw18650step0Labels = mixedMoment B raw18650step1 raw18650step1Labels := by
      have ha : raw18650step1 = (fun i j => raw18650step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18650step1 raw18650step0; decide +kernel
      have hl : raw18650step1Labels = raw18650step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18650step0 raw18650step0Labels permutation56 permutation2
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw18651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18651step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18651step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18651step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18651 raw18651Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw18651 raw18651Labels = mixedMoment B raw18651step0 raw18651step0Labels := by
      have ha : raw18651step0 = (fun i j => raw18651 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18651step0 raw18651; decide +kernel
      have hl : raw18651step0Labels = raw18651Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18651 raw18651Labels permutation663 permutation7
    mixedMoment B raw18651step0 raw18651step0Labels = mixedMoment B raw18651step1 raw18651step1Labels := by
      have ha : raw18651step1 = raw18651step0 := by apply Matrix.ext; unfold raw18651step1 raw18651step0; decide +kernel
      have hl : raw18651step0Labels = labelEmbedding10 ∘ raw18651step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18651step0 raw18651step0Labels raw18651step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

def raw18652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18652step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18652step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18652step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18652step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18652step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18652step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18652 raw18652Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw18652 raw18652Labels = mixedMoment B raw18652step0 raw18652step0Labels := by
      have hz : ∀ j, raw18652 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18652step0 = (fun i j => raw18652 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18652step0 raw18652; decide +kernel
      have hl : raw18652step0Labels = raw18652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18652 raw18652Labels permutation520 hz
    mixedMoment B raw18652step0 raw18652step0Labels = mixedMoment B raw18652step1 raw18652step1Labels := by
      have hz : ∀ j, raw18652step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18652step1 = (fun i j => raw18652step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18652step1 raw18652step0; decide +kernel
      have hl : raw18652step1Labels = raw18652step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18652step0 raw18652step0Labels permutation80 hz
    mixedMoment B raw18652step1 raw18652step1Labels = mixedMoment B raw18652step2 raw18652step2Labels := by
      have ha : raw18652step2 = (fun i j => raw18652step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18652step2 raw18652step1; decide +kernel
      have hl : raw18652step2Labels = raw18652step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18652step1 raw18652step1Labels permutation30 permutation7
    mixedMoment B raw18652step2 raw18652step2Labels = mixedMoment B raw18652step3 raw18652step3Labels := by
      have ha : raw18652step3 = raw18652step2 := by apply Matrix.ext; unfold raw18652step3 raw18652step2; decide +kernel
      have hl : raw18652step2Labels = labelEmbedding10 ∘ raw18652step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18652step2 raw18652step2Labels raw18652step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5493 node5493Labels := by rfl

def raw18653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw18653step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18653step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18653step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18653step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18653step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18653 raw18653Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw18653 raw18653Labels = mixedMoment B raw18653step0 raw18653step0Labels := by
      have hz : ∀ j, raw18653 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18653step0 = (fun i j => raw18653 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18653step0 raw18653; decide +kernel
      have hl : raw18653step0Labels = raw18653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18653 raw18653Labels permutation346 hz
    mixedMoment B raw18653step0 raw18653step0Labels = mixedMoment B raw18653step1 raw18653step1Labels := by
      have ha : raw18653step1 = (fun i j => raw18653step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18653step1 raw18653step0; decide +kernel
      have hl : raw18653step1Labels = raw18653step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18653step0 raw18653step0Labels permutation128 permutation4
    mixedMoment B raw18653step1 raw18653step1Labels = mixedMoment B raw18653step2 raw18653step2Labels := by
      have ha : raw18653step2 = -raw18653step1 := by apply Matrix.ext; change ∀ i j, raw18653step2 i j = -(raw18653step1 i j); unfold raw18653step2 raw18653step1; decide +kernel
      have hl : raw18653step2Labels = raw18653step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18653step2 raw18653step2Labels = mixedMoment B raw18653step3 raw18653step3Labels := by
      have ha : raw18653step3 = raw18653step2 := by apply Matrix.ext; unfold raw18653step3 raw18653step2; decide +kernel
      have hl : raw18653step2Labels = labelEmbedding7 ∘ raw18653step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18653step2 raw18653step2Labels raw18653step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5452 node5452Labels := by rfl

def raw18654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18654step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18654step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18654 raw18654Labels = mixedMoment B node5462 node5462Labels := by
  calc
    mixedMoment B raw18654 raw18654Labels = mixedMoment B raw18654step0 raw18654step0Labels := by
      have ha : raw18654step0 = (fun i j => raw18654 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18654step0 raw18654; decide +kernel
      have hl : raw18654step0Labels = raw18654Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18654 raw18654Labels permutation170 permutation3
    mixedMoment B raw18654step0 raw18654step0Labels = mixedMoment B raw18654step1 raw18654step1Labels := by
      have ha : raw18654step1 = raw18654step0 := by apply Matrix.ext; unfold raw18654step1 raw18654step0; decide +kernel
      have hl : raw18654step0Labels = labelEmbedding6 ∘ raw18654step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18654step0 raw18654step0Labels raw18654step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5462 node5462Labels := by rfl

def raw18655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18655 raw18655Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw18655 raw18655Labels = mixedMoment B raw18655step0 raw18655step0Labels := by
      have hz : ∀ j, raw18655 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18655step0 = (fun i j => raw18655 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18655step0 raw18655; decide +kernel
      have hl : raw18655step0Labels = raw18655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18655 raw18655Labels permutation520 hz
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw18656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw18656step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18656step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18656step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18656step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18656 raw18656Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw18656 raw18656Labels = mixedMoment B raw18656step0 raw18656step0Labels := by
      have ha : raw18656step0 = (fun i j => raw18656 (permutation590 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18656step0 raw18656; decide +kernel
      have hl : raw18656step0Labels = raw18656Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18656 raw18656Labels permutation590 permutation4
    mixedMoment B raw18656step0 raw18656step0Labels = mixedMoment B raw18656step1 raw18656step1Labels := by
      have ha : raw18656step1 = -raw18656step0 := by apply Matrix.ext; change ∀ i j, raw18656step1 i j = -(raw18656step0 i j); unfold raw18656step1 raw18656step0; decide +kernel
      have hl : raw18656step1Labels = raw18656step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18656step1 raw18656step1Labels = mixedMoment B raw18656step2 raw18656step2Labels := by
      have ha : raw18656step2 = raw18656step1 := by apply Matrix.ext; unfold raw18656step2 raw18656step1; decide +kernel
      have hl : raw18656step1Labels = labelEmbedding7 ∘ raw18656step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18656step1 raw18656step1Labels raw18656step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

def raw18657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw18657step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18657step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18657step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18657step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18657 raw18657Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw18657 raw18657Labels = mixedMoment B raw18657step0 raw18657step0Labels := by
      have hz : ∀ j, raw18657 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18657step0 = (fun i j => raw18657 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18657step0 raw18657; decide +kernel
      have hl : raw18657step0Labels = raw18657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18657 raw18657Labels permutation346 hz
    mixedMoment B raw18657step0 raw18657step0Labels = mixedMoment B raw18657step1 raw18657step1Labels := by
      have ha : raw18657step1 = (fun i j => raw18657step0 (permutation96 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18657step1 raw18657step0; decide +kernel
      have hl : raw18657step1Labels = raw18657step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18657step0 raw18657step0Labels permutation96 permutation3
    mixedMoment B raw18657step1 raw18657step1Labels = mixedMoment B raw18657step2 raw18657step2Labels := by
      have ha : raw18657step2 = -raw18657step1 := by apply Matrix.ext; change ∀ i j, raw18657step2 i j = -(raw18657step1 i j); unfold raw18657step2 raw18657step1; decide +kernel
      have hl : raw18657step2Labels = raw18657step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18657step2 raw18657step2Labels = mixedMoment B raw18657step3 raw18657step3Labels := by
      have ha : raw18657step3 = raw18657step2 := by apply Matrix.ext; unfold raw18657step3 raw18657step2; decide +kernel
      have hl : raw18657step2Labels = labelEmbedding6 ∘ raw18657step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18657step2 raw18657step2Labels raw18657step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5404 node5404Labels := by rfl

def raw18658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18658step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18658step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18658step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18658step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18658step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18658 raw18658Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw18658 raw18658Labels = mixedMoment B raw18658step0 raw18658step0Labels := by
      have ha : raw18658step0 = (fun i j => raw18658 (permutation502 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18658step0 raw18658; decide +kernel
      have hl : raw18658step0Labels = raw18658Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18658 raw18658Labels permutation502 permutation3
    mixedMoment B raw18658step0 raw18658step0Labels = mixedMoment B raw18658step1 raw18658step1Labels := by
      have ha : raw18658step1 = -raw18658step0 := by apply Matrix.ext; change ∀ i j, raw18658step1 i j = -(raw18658step0 i j); unfold raw18658step1 raw18658step0; decide +kernel
      have hl : raw18658step1Labels = raw18658step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18658step1 raw18658step1Labels = mixedMoment B raw18658step2 raw18658step2Labels := by
      have ha : raw18658step2 = raw18658step1 := by apply Matrix.ext; unfold raw18658step2 raw18658step1; decide +kernel
      have hl : raw18658step1Labels = labelEmbedding6 ∘ raw18658step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18658step1 raw18658step1Labels raw18658step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw18659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18659step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18659step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18659step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18659step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18659step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18659step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18659 raw18659Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw18659 raw18659Labels = mixedMoment B raw18659step0 raw18659step0Labels := by
      have hz : ∀ j, raw18659 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18659step0 = (fun i j => raw18659 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18659step0 raw18659; decide +kernel
      have hl : raw18659step0Labels = raw18659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18659 raw18659Labels permutation520 hz
    mixedMoment B raw18659step0 raw18659step0Labels = mixedMoment B raw18659step1 raw18659step1Labels := by
      have hz : ∀ j, raw18659step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18659step1 = (fun i j => raw18659step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18659step1 raw18659step0; decide +kernel
      have hl : raw18659step1Labels = raw18659step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18659step0 raw18659step0Labels permutation80 hz
    mixedMoment B raw18659step1 raw18659step1Labels = mixedMoment B raw18659step2 raw18659step2Labels := by
      have ha : raw18659step2 = (fun i j => raw18659step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18659step2 raw18659step1; decide +kernel
      have hl : raw18659step2Labels = raw18659step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18659step1 raw18659step1Labels permutation25 permutation3
    mixedMoment B raw18659step2 raw18659step2Labels = mixedMoment B raw18659step3 raw18659step3Labels := by
      have ha : raw18659step3 = -raw18659step2 := by apply Matrix.ext; change ∀ i j, raw18659step3 i j = -(raw18659step2 i j); unfold raw18659step3 raw18659step2; decide +kernel
      have hl : raw18659step3Labels = raw18659step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18659step3 raw18659step3Labels = mixedMoment B raw18659step4 raw18659step4Labels := by
      have ha : raw18659step4 = raw18659step3 := by apply Matrix.ext; unfold raw18659step4 raw18659step3; decide +kernel
      have hl : raw18659step3Labels = labelEmbedding6 ∘ raw18659step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18659step3 raw18659step3Labels raw18659step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw18660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18660step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18660step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18660step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18660step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18660 raw18660Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw18660 raw18660Labels = mixedMoment B raw18660step0 raw18660step0Labels := by
      have hz : ∀ j, raw18660 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18660step0 = (fun i j => raw18660 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18660step0 raw18660; decide +kernel
      have hl : raw18660step0Labels = raw18660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18660 raw18660Labels permutation346 hz
    mixedMoment B raw18660step0 raw18660step0Labels = mixedMoment B raw18660step1 raw18660step1Labels := by
      have ha : raw18660step1 = (fun i j => raw18660step0 (permutation94 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18660step1 raw18660step0; decide +kernel
      have hl : raw18660step1Labels = raw18660step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18660step0 raw18660step0Labels permutation94 permutation5
    mixedMoment B raw18660step1 raw18660step1Labels = mixedMoment B raw18660step2 raw18660step2Labels := by
      have ha : raw18660step2 = raw18660step1 := by apply Matrix.ext; unfold raw18660step2 raw18660step1; decide +kernel
      have hl : raw18660step1Labels = labelEmbedding8 ∘ raw18660step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18660step1 raw18660step1Labels raw18660step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw18661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18661step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw18661step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18661step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18661step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18661step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18661 raw18661Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw18661 raw18661Labels = mixedMoment B raw18661step0 raw18661step0Labels := by
      have hz : ∀ j, raw18661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18661step0 = (fun i j => raw18661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18661step0 raw18661; decide +kernel
      have hl : raw18661step0Labels = raw18661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18661 raw18661Labels permutation346 hz
    mixedMoment B raw18661step0 raw18661step0Labels = mixedMoment B raw18661step1 raw18661step1Labels := by
      have ha : raw18661step1 = (fun i j => raw18661step0 (permutation120 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18661step1 raw18661step0; decide +kernel
      have hl : raw18661step1Labels = raw18661step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18661step0 raw18661step0Labels permutation120 permutation3
    mixedMoment B raw18661step1 raw18661step1Labels = mixedMoment B raw18661step2 raw18661step2Labels := by
      have ha : raw18661step2 = -raw18661step1 := by apply Matrix.ext; change ∀ i j, raw18661step2 i j = -(raw18661step1 i j); unfold raw18661step2 raw18661step1; decide +kernel
      have hl : raw18661step2Labels = raw18661step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18661step2 raw18661step2Labels = mixedMoment B raw18661step3 raw18661step3Labels := by
      have ha : raw18661step3 = raw18661step2 := by apply Matrix.ext; unfold raw18661step3 raw18661step2; decide +kernel
      have hl : raw18661step2Labels = labelEmbedding6 ∘ raw18661step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18661step2 raw18661step2Labels raw18661step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5404 node5404Labels := by rfl

def raw18662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw18662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18662step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18662step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18662step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18662step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18662step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18662 raw18662Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw18662 raw18662Labels = mixedMoment B raw18662step0 raw18662step0Labels := by
      have ha : raw18662step0 = (fun i j => raw18662 (permutation566 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18662step0 raw18662; decide +kernel
      have hl : raw18662step0Labels = raw18662Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18662 raw18662Labels permutation566 permutation3
    mixedMoment B raw18662step0 raw18662step0Labels = mixedMoment B raw18662step1 raw18662step1Labels := by
      have ha : raw18662step1 = -raw18662step0 := by apply Matrix.ext; change ∀ i j, raw18662step1 i j = -(raw18662step0 i j); unfold raw18662step1 raw18662step0; decide +kernel
      have hl : raw18662step1Labels = raw18662step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18662step1 raw18662step1Labels = mixedMoment B raw18662step2 raw18662step2Labels := by
      have ha : raw18662step2 = raw18662step1 := by apply Matrix.ext; unfold raw18662step2 raw18662step1; decide +kernel
      have hl : raw18662step1Labels = labelEmbedding6 ∘ raw18662step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18662step1 raw18662step1Labels raw18662step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw18663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw18663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw18663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18663step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18663step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18663step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18663 raw18663Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw18663 raw18663Labels = mixedMoment B raw18663step0 raw18663step0Labels := by
      have hz : ∀ j, raw18663 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18663step0 = (fun i j => raw18663 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18663step0 raw18663; decide +kernel
      have hl : raw18663step0Labels = raw18663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18663 raw18663Labels permutation346 hz
    mixedMoment B raw18663step0 raw18663step0Labels = mixedMoment B raw18663step1 raw18663step1Labels := by
      have ha : raw18663step1 = (fun i j => raw18663step0 (permutation118 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18663step1 raw18663step0; decide +kernel
      have hl : raw18663step1Labels = raw18663step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18663step0 raw18663step0Labels permutation118 permutation5
    mixedMoment B raw18663step1 raw18663step1Labels = mixedMoment B raw18663step2 raw18663step2Labels := by
      have ha : raw18663step2 = raw18663step1 := by apply Matrix.ext; unfold raw18663step2 raw18663step1; decide +kernel
      have hl : raw18663step1Labels = labelEmbedding8 ∘ raw18663step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18663step1 raw18663step1Labels raw18663step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw18664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18664step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18664step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18664step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18664 raw18664Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18664 raw18664Labels = mixedMoment B raw18664step0 raw18664step0Labels := by
      have hz : ∀ j, raw18664 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18664step0 = (fun i j => raw18664 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18664step0 raw18664; decide +kernel
      have hl : raw18664step0Labels = raw18664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18664 raw18664Labels permutation346 hz
    mixedMoment B raw18664step0 raw18664step0Labels = mixedMoment B raw18664step1 raw18664step1Labels := by
      have ha : raw18664step1 = (fun i j => raw18664step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18664step1 raw18664step0; decide +kernel
      have hl : raw18664step1Labels = raw18664step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18664step0 raw18664step0Labels permutation56 permutation3
    mixedMoment B raw18664step1 raw18664step1Labels = mixedMoment B raw18664step2 raw18664step2Labels := by
      have ha : raw18664step2 = raw18664step1 := by apply Matrix.ext; unfold raw18664step2 raw18664step1; decide +kernel
      have hl : raw18664step1Labels = labelEmbedding6 ∘ raw18664step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18664step1 raw18664step1Labels raw18664step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw18665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18665step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18665step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18665step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18665step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18665 raw18665Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw18665 raw18665Labels = mixedMoment B raw18665step0 raw18665step0Labels := by
      have ha : raw18665step0 = (fun i j => raw18665 (permutation659 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18665step0 raw18665; decide +kernel
      have hl : raw18665step0Labels = raw18665Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18665 raw18665Labels permutation659 permutation5
    mixedMoment B raw18665step0 raw18665step0Labels = mixedMoment B raw18665step1 raw18665step1Labels := by
      have ha : raw18665step1 = raw18665step0 := by apply Matrix.ext; unfold raw18665step1 raw18665step0; decide +kernel
      have hl : raw18665step0Labels = labelEmbedding8 ∘ raw18665step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18665step0 raw18665step0Labels raw18665step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

def raw18666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18666step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18666step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18666step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18666 raw18666Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw18666 raw18666Labels = mixedMoment B raw18666step0 raw18666step0Labels := by
      have hz : ∀ j, raw18666 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18666step0 = (fun i j => raw18666 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18666step0 raw18666; decide +kernel
      have hl : raw18666step0Labels = raw18666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18666 raw18666Labels permutation346 hz
    mixedMoment B raw18666step0 raw18666step0Labels = mixedMoment B raw18666step1 raw18666step1Labels := by
      have ha : raw18666step1 = (fun i j => raw18666step0 (permutation132 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18666step1 raw18666step0; decide +kernel
      have hl : raw18666step1Labels = raw18666step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18666step0 raw18666step0Labels permutation132 permutation4
    mixedMoment B raw18666step1 raw18666step1Labels = mixedMoment B raw18666step2 raw18666step2Labels := by
      have ha : raw18666step2 = raw18666step1 := by apply Matrix.ext; unfold raw18666step2 raw18666step1; decide +kernel
      have hl : raw18666step1Labels = labelEmbedding7 ∘ raw18666step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18666step1 raw18666step1Labels raw18666step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw18667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw18667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw18667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18667step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18667step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18667step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18667 raw18667Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw18667 raw18667Labels = mixedMoment B raw18667step0 raw18667step0Labels := by
      have hz : ∀ j, raw18667 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18667step0 = (fun i j => raw18667 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18667step0 raw18667; decide +kernel
      have hl : raw18667step0Labels = raw18667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18667 raw18667Labels permutation346 hz
    mixedMoment B raw18667step0 raw18667step0Labels = mixedMoment B raw18667step1 raw18667step1Labels := by
      have ha : raw18667step1 = (fun i j => raw18667step0 (permutation130 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18667step1 raw18667step0; decide +kernel
      have hl : raw18667step1Labels = raw18667step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18667step0 raw18667step0Labels permutation130 permutation4
    mixedMoment B raw18667step1 raw18667step1Labels = mixedMoment B raw18667step2 raw18667step2Labels := by
      have ha : raw18667step2 = raw18667step1 := by apply Matrix.ext; unfold raw18667step2 raw18667step1; decide +kernel
      have hl : raw18667step1Labels = labelEmbedding7 ∘ raw18667step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18667step1 raw18667step1Labels raw18667step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw18668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw18668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw18668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18668step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18668step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18668 raw18668Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw18668 raw18668Labels = mixedMoment B raw18668step0 raw18668step0Labels := by
      have hz : ∀ j, raw18668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18668step0 = (fun i j => raw18668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18668step0 raw18668; decide +kernel
      have hl : raw18668step0Labels = raw18668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18668 raw18668Labels permutation346 hz
    mixedMoment B raw18668step0 raw18668step0Labels = mixedMoment B raw18668step1 raw18668step1Labels := by
      have ha : raw18668step1 = (fun i j => raw18668step0 (permutation97 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18668step1 raw18668step0; decide +kernel
      have hl : raw18668step1Labels = raw18668step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18668step0 raw18668step0Labels permutation97 permutation2
    mixedMoment B raw18668step1 raw18668step1Labels = mixedMoment B raw18668step2 raw18668step2Labels := by
      have ha : raw18668step2 = -raw18668step1 := by apply Matrix.ext; change ∀ i j, raw18668step2 i j = -(raw18668step1 i j); unfold raw18668step2 raw18668step1; decide +kernel
      have hl : raw18668step2Labels = raw18668step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw18669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18669step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18669step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18669step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18669step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18669 raw18669Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw18669 raw18669Labels = mixedMoment B raw18669step0 raw18669step0Labels := by
      have ha : raw18669step0 = (fun i j => raw18669 (permutation273 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18669step0 raw18669; decide +kernel
      have hl : raw18669step0Labels = raw18669Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18669 raw18669Labels permutation273 permutation3
    mixedMoment B raw18669step0 raw18669step0Labels = mixedMoment B raw18669step1 raw18669step1Labels := by
      have ha : raw18669step1 = raw18669step0 := by apply Matrix.ext; unfold raw18669step1 raw18669step0; decide +kernel
      have hl : raw18669step0Labels = labelEmbedding6 ∘ raw18669step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18669step0 raw18669step0Labels raw18669step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5365 node5365Labels := by rfl

def raw18670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18670step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18670step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18670step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18670 raw18670Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw18670 raw18670Labels = mixedMoment B raw18670step0 raw18670step0Labels := by
      have ha : raw18670step0 = (fun i j => raw18670 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18670step0 raw18670; decide +kernel
      have hl : raw18670step0Labels = raw18670Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18670 raw18670Labels permutation160 permutation3
    mixedMoment B raw18670step0 raw18670step0Labels = mixedMoment B raw18670step1 raw18670step1Labels := by
      have ha : raw18670step1 = raw18670step0 := by apply Matrix.ext; unfold raw18670step1 raw18670step0; decide +kernel
      have hl : raw18670step0Labels = labelEmbedding6 ∘ raw18670step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18670step0 raw18670step0Labels raw18670step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw18671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw18671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18671step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18671step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18671 raw18671Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw18671 raw18671Labels = mixedMoment B raw18671step0 raw18671step0Labels := by
      have ha : raw18671step0 = (fun i j => raw18671 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18671step0 raw18671; decide +kernel
      have hl : raw18671step0Labels = raw18671Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18671 raw18671Labels permutation166 permutation3
    mixedMoment B raw18671step0 raw18671step0Labels = mixedMoment B raw18671step1 raw18671step1Labels := by
      have ha : raw18671step1 = raw18671step0 := by apply Matrix.ext; unfold raw18671step1 raw18671step0; decide +kernel
      have hl : raw18671step0Labels = labelEmbedding6 ∘ raw18671step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18671step0 raw18671step0Labels raw18671step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw18672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw18672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18672step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18672 raw18672Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw18672 raw18672Labels = mixedMoment B raw18672step0 raw18672step0Labels := by
      have ha : raw18672step0 = (fun i j => raw18672 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18672step0 raw18672; decide +kernel
      have hl : raw18672step0Labels = raw18672Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18672 raw18672Labels permutation173 permutation3
    mixedMoment B raw18672step0 raw18672step0Labels = mixedMoment B raw18672step1 raw18672step1Labels := by
      have ha : raw18672step1 = raw18672step0 := by apply Matrix.ext; unfold raw18672step1 raw18672step0; decide +kernel
      have hl : raw18672step0Labels = labelEmbedding6 ∘ raw18672step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18672step0 raw18672step0Labels raw18672step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw18673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18673step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18673step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18673step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18673 raw18673Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw18673 raw18673Labels = mixedMoment B raw18673step0 raw18673step0Labels := by
      have hz : ∀ j, raw18673 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18673step0 = (fun i j => raw18673 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18673step0 raw18673; decide +kernel
      have hl : raw18673step0Labels = raw18673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18673 raw18673Labels permutation346 hz
    mixedMoment B raw18673step0 raw18673step0Labels = mixedMoment B raw18673step1 raw18673step1Labels := by
      have ha : raw18673step1 = (fun i j => raw18673step0 (permutation59 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18673step1 raw18673step0; decide +kernel
      have hl : raw18673step1Labels = raw18673step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18673step0 raw18673step0Labels permutation59 permutation3
    mixedMoment B raw18673step1 raw18673step1Labels = mixedMoment B raw18673step2 raw18673step2Labels := by
      have ha : raw18673step2 = raw18673step1 := by apply Matrix.ext; unfold raw18673step2 raw18673step1; decide +kernel
      have hl : raw18673step1Labels = labelEmbedding6 ∘ raw18673step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18673step1 raw18673step1Labels raw18673step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw18674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw18674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18674step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18674step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18674step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18674step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18674step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18674 raw18674Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw18674 raw18674Labels = mixedMoment B raw18674step0 raw18674step0Labels := by
      have ha : raw18674step0 = (fun i j => raw18674 (permutation517 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18674step0 raw18674; decide +kernel
      have hl : raw18674step0Labels = raw18674Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18674 raw18674Labels permutation517 permutation3
    mixedMoment B raw18674step0 raw18674step0Labels = mixedMoment B raw18674step1 raw18674step1Labels := by
      have ha : raw18674step1 = -raw18674step0 := by apply Matrix.ext; change ∀ i j, raw18674step1 i j = -(raw18674step0 i j); unfold raw18674step1 raw18674step0; decide +kernel
      have hl : raw18674step1Labels = raw18674step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18674step1 raw18674step1Labels = mixedMoment B raw18674step2 raw18674step2Labels := by
      have ha : raw18674step2 = raw18674step1 := by apply Matrix.ext; unfold raw18674step2 raw18674step1; decide +kernel
      have hl : raw18674step1Labels = labelEmbedding6 ∘ raw18674step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18674step1 raw18674step1Labels raw18674step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

def raw18675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw18675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw18675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18675step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18675step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18675step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18675step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18675step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18675 raw18675Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw18675 raw18675Labels = mixedMoment B raw18675step0 raw18675step0Labels := by
      have hz : ∀ j, raw18675 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18675step0 = (fun i j => raw18675 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18675step0 raw18675; decide +kernel
      have hl : raw18675step0Labels = raw18675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18675 raw18675Labels permutation346 hz
    mixedMoment B raw18675step0 raw18675step0Labels = mixedMoment B raw18675step1 raw18675step1Labels := by
      have ha : raw18675step1 = (fun i j => raw18675step0 (permutation103 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18675step1 raw18675step0; decide +kernel
      have hl : raw18675step1Labels = raw18675step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18675step0 raw18675step0Labels permutation103 permutation3
    mixedMoment B raw18675step1 raw18675step1Labels = mixedMoment B raw18675step2 raw18675step2Labels := by
      have ha : raw18675step2 = -raw18675step1 := by apply Matrix.ext; change ∀ i j, raw18675step2 i j = -(raw18675step1 i j); unfold raw18675step2 raw18675step1; decide +kernel
      have hl : raw18675step2Labels = raw18675step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18675step2 raw18675step2Labels = mixedMoment B raw18675step3 raw18675step3Labels := by
      have ha : raw18675step3 = raw18675step2 := by apply Matrix.ext; unfold raw18675step3 raw18675step2; decide +kernel
      have hl : raw18675step2Labels = labelEmbedding6 ∘ raw18675step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18675step2 raw18675step2Labels raw18675step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw18676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw18676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw18676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18676step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18676step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18676 raw18676Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw18676 raw18676Labels = mixedMoment B raw18676step0 raw18676step0Labels := by
      have hz : ∀ j, raw18676 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18676step0 = (fun i j => raw18676 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18676step0 raw18676; decide +kernel
      have hl : raw18676step0Labels = raw18676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18676 raw18676Labels permutation346 hz
    mixedMoment B raw18676step0 raw18676step0Labels = mixedMoment B raw18676step1 raw18676step1Labels := by
      have ha : raw18676step1 = (fun i j => raw18676step0 (permutation97 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18676step1 raw18676step0; decide +kernel
      have hl : raw18676step1Labels = raw18676step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18676step0 raw18676step0Labels permutation97 permutation2
    mixedMoment B raw18676step1 raw18676step1Labels = mixedMoment B raw18676step2 raw18676step2Labels := by
      have ha : raw18676step2 = -raw18676step1 := by apply Matrix.ext; change ∀ i j, raw18676step2 i j = -(raw18676step1 i j); unfold raw18676step2 raw18676step1; decide +kernel
      have hl : raw18676step2Labels = raw18676step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw18677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw18677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw18677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18677step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18677step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18677step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18677 raw18677Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw18677 raw18677Labels = mixedMoment B raw18677step0 raw18677step0Labels := by
      have hz : ∀ j, raw18677 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18677step0 = (fun i j => raw18677 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18677step0 raw18677; decide +kernel
      have hl : raw18677step0Labels = raw18677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18677 raw18677Labels permutation346 hz
    mixedMoment B raw18677step0 raw18677step0Labels = mixedMoment B raw18677step1 raw18677step1Labels := by
      have ha : raw18677step1 = (fun i j => raw18677step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18677step1 raw18677step0; decide +kernel
      have hl : raw18677step1Labels = raw18677step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18677step0 raw18677step0Labels permutation57 permutation3
    mixedMoment B raw18677step1 raw18677step1Labels = mixedMoment B raw18677step2 raw18677step2Labels := by
      have ha : raw18677step2 = raw18677step1 := by apply Matrix.ext; unfold raw18677step2 raw18677step1; decide +kernel
      have hl : raw18677step1Labels = labelEmbedding6 ∘ raw18677step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18677step1 raw18677step1Labels raw18677step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw18678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw18678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18678step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18678step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18678step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18678step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18678step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18678 raw18678Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw18678 raw18678Labels = mixedMoment B raw18678step0 raw18678step0Labels := by
      have ha : raw18678step0 = (fun i j => raw18678 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18678step0 raw18678; decide +kernel
      have hl : raw18678step0Labels = raw18678Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18678 raw18678Labels permutation587 permutation3
    mixedMoment B raw18678step0 raw18678step0Labels = mixedMoment B raw18678step1 raw18678step1Labels := by
      have ha : raw18678step1 = -raw18678step0 := by apply Matrix.ext; change ∀ i j, raw18678step1 i j = -(raw18678step0 i j); unfold raw18678step1 raw18678step0; decide +kernel
      have hl : raw18678step1Labels = raw18678step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18678step1 raw18678step1Labels = mixedMoment B raw18678step2 raw18678step2Labels := by
      have ha : raw18678step2 = raw18678step1 := by apply Matrix.ext; unfold raw18678step2 raw18678step1; decide +kernel
      have hl : raw18678step1Labels = labelEmbedding6 ∘ raw18678step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18678step1 raw18678step1Labels raw18678step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

def raw18679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw18679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw18679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18679step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18679step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18679step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18679step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18679step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18679 raw18679Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw18679 raw18679Labels = mixedMoment B raw18679step0 raw18679step0Labels := by
      have hz : ∀ j, raw18679 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18679step0 = (fun i j => raw18679 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18679step0 raw18679; decide +kernel
      have hl : raw18679step0Labels = raw18679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18679 raw18679Labels permutation346 hz
    mixedMoment B raw18679step0 raw18679step0Labels = mixedMoment B raw18679step1 raw18679step1Labels := by
      have ha : raw18679step1 = (fun i j => raw18679step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18679step1 raw18679step0; decide +kernel
      have hl : raw18679step1Labels = raw18679step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18679step0 raw18679step0Labels permutation127 permutation3
    mixedMoment B raw18679step1 raw18679step1Labels = mixedMoment B raw18679step2 raw18679step2Labels := by
      have ha : raw18679step2 = -raw18679step1 := by apply Matrix.ext; change ∀ i j, raw18679step2 i j = -(raw18679step1 i j); unfold raw18679step2 raw18679step1; decide +kernel
      have hl : raw18679step2Labels = raw18679step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18679step2 raw18679step2Labels = mixedMoment B raw18679step3 raw18679step3Labels := by
      have ha : raw18679step3 = raw18679step2 := by apply Matrix.ext; unfold raw18679step3 raw18679step2; decide +kernel
      have hl : raw18679step2Labels = labelEmbedding6 ∘ raw18679step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18679step2 raw18679step2Labels raw18679step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw18680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw18680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw18680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18680step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18680step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18680 raw18680Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw18680 raw18680Labels = mixedMoment B raw18680step0 raw18680step0Labels := by
      have hz : ∀ j, raw18680 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18680step0 = (fun i j => raw18680 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18680step0 raw18680; decide +kernel
      have hl : raw18680step0Labels = raw18680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18680 raw18680Labels permutation346 hz
    mixedMoment B raw18680step0 raw18680step0Labels = mixedMoment B raw18680step1 raw18680step1Labels := by
      have ha : raw18680step1 = (fun i j => raw18680step0 (permutation121 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18680step1 raw18680step0; decide +kernel
      have hl : raw18680step1Labels = raw18680step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18680step0 raw18680step0Labels permutation121 permutation2
    mixedMoment B raw18680step1 raw18680step1Labels = mixedMoment B raw18680step2 raw18680step2Labels := by
      have ha : raw18680step2 = -raw18680step1 := by apply Matrix.ext; change ∀ i j, raw18680step2 i j = -(raw18680step1 i j); unfold raw18680step2 raw18680step1; decide +kernel
      have hl : raw18680step2Labels = raw18680step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw18681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw18681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw18681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18681step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18681step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18681step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18681step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18681 raw18681Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw18681 raw18681Labels = mixedMoment B raw18681step0 raw18681step0Labels := by
      have hz : ∀ j, raw18681 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18681step0 = (fun i j => raw18681 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18681step0 raw18681; decide +kernel
      have hl : raw18681step0Labels = raw18681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18681 raw18681Labels permutation346 hz
    mixedMoment B raw18681step0 raw18681step0Labels = mixedMoment B raw18681step1 raw18681step1Labels := by
      have ha : raw18681step1 = (fun i j => raw18681step0 (permutation144 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18681step1 raw18681step0; decide +kernel
      have hl : raw18681step1Labels = raw18681step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18681step0 raw18681step0Labels permutation144 permutation5
    mixedMoment B raw18681step1 raw18681step1Labels = mixedMoment B raw18681step2 raw18681step2Labels := by
      have ha : raw18681step2 = raw18681step1 := by apply Matrix.ext; unfold raw18681step2 raw18681step1; decide +kernel
      have hl : raw18681step1Labels = labelEmbedding8 ∘ raw18681step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18681step1 raw18681step1Labels raw18681step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

def raw18682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw18682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18682step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18682step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18682step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18682step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18682 raw18682Labels = mixedMoment B node5247 node5247Labels := by
  calc
    mixedMoment B raw18682 raw18682Labels = mixedMoment B raw18682step0 raw18682step0Labels := by
      have ha : raw18682step0 = (fun i j => raw18682 (permutation662 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18682step0 raw18682; decide +kernel
      have hl : raw18682step0Labels = raw18682Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18682 raw18682Labels permutation662 permutation5
    mixedMoment B raw18682step0 raw18682step0Labels = mixedMoment B raw18682step1 raw18682step1Labels := by
      have ha : raw18682step1 = raw18682step0 := by apply Matrix.ext; unfold raw18682step1 raw18682step0; decide +kernel
      have hl : raw18682step0Labels = labelEmbedding8 ∘ raw18682step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18682step0 raw18682step0Labels raw18682step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5247 node5247Labels := by rfl

def raw18683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw18683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw18683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18683step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18683step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18683step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18683 raw18683Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw18683 raw18683Labels = mixedMoment B raw18683step0 raw18683step0Labels := by
      have hz : ∀ j, raw18683 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18683step0 = (fun i j => raw18683 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18683step0 raw18683; decide +kernel
      have hl : raw18683step0Labels = raw18683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18683 raw18683Labels permutation346 hz
    mixedMoment B raw18683step0 raw18683step0Labels = mixedMoment B raw18683step1 raw18683step1Labels := by
      have ha : raw18683step1 = (fun i j => raw18683step0 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18683step1 raw18683step0; decide +kernel
      have hl : raw18683step1Labels = raw18683step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18683step0 raw18683step0Labels permutation145 permutation5
    mixedMoment B raw18683step1 raw18683step1Labels = mixedMoment B raw18683step2 raw18683step2Labels := by
      have ha : raw18683step2 = raw18683step1 := by apply Matrix.ext; unfold raw18683step2 raw18683step1; decide +kernel
      have hl : raw18683step1Labels = labelEmbedding8 ∘ raw18683step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18683step1 raw18683step1Labels raw18683step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw18684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18684 raw18684Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw18684 raw18684Labels = mixedMoment B raw18684step0 raw18684step0Labels := by
      have ha : raw18684step0 = (fun i j => raw18684 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18684step0 raw18684; decide +kernel
      have hl : raw18684step0Labels = raw18684Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18684 raw18684Labels permutation265 permutation2
    _ = mixedMoment B node5480 node5480Labels := by rfl

def raw18685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18685step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18685step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18685step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18685step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18685step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18685 raw18685Labels = mixedMoment B node5471 node5471Labels := by
  calc
    mixedMoment B raw18685 raw18685Labels = mixedMoment B raw18685step0 raw18685step0Labels := by
      have ha : raw18685step0 = (fun i j => raw18685 (permutation415 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18685step0 raw18685; decide +kernel
      have hl : raw18685step0Labels = raw18685Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18685 raw18685Labels permutation415 permutation4
    mixedMoment B raw18685step0 raw18685step0Labels = mixedMoment B raw18685step1 raw18685step1Labels := by
      have ha : raw18685step1 = -raw18685step0 := by apply Matrix.ext; change ∀ i j, raw18685step1 i j = -(raw18685step0 i j); unfold raw18685step1 raw18685step0; decide +kernel
      have hl : raw18685step1Labels = raw18685step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18685step1 raw18685step1Labels = mixedMoment B raw18685step2 raw18685step2Labels := by
      have ha : raw18685step2 = raw18685step1 := by apply Matrix.ext; unfold raw18685step2 raw18685step1; decide +kernel
      have hl : raw18685step1Labels = labelEmbedding7 ∘ raw18685step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18685step1 raw18685step1Labels raw18685step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5471 node5471Labels := by rfl

def raw18686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18686step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18686step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18686step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18686 raw18686Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw18686 raw18686Labels = mixedMoment B raw18686step0 raw18686step0Labels := by
      have hz : ∀ j, raw18686 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18686step0 = (fun i j => raw18686 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18686step0 raw18686; decide +kernel
      have hl : raw18686step0Labels = raw18686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18686 raw18686Labels permutation520 hz
    mixedMoment B raw18686step0 raw18686step0Labels = mixedMoment B raw18686step1 raw18686step1Labels := by
      have ha : raw18686step1 = (fun i j => raw18686step0 (permutation140 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18686step1 raw18686step0; decide +kernel
      have hl : raw18686step1Labels = raw18686step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18686step0 raw18686step0Labels permutation140 permutation6
    mixedMoment B raw18686step1 raw18686step1Labels = mixedMoment B raw18686step2 raw18686step2Labels := by
      have ha : raw18686step2 = raw18686step1 := by apply Matrix.ext; unfold raw18686step2 raw18686step1; decide +kernel
      have hl : raw18686step1Labels = labelEmbedding9 ∘ raw18686step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18686step1 raw18686step1Labels raw18686step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw18687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18687step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18687step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18687step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18687step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18687step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18687step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18687 raw18687Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw18687 raw18687Labels = mixedMoment B raw18687step0 raw18687step0Labels := by
      have ha : raw18687step0 = (fun i j => raw18687 (permutation624 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18687step0 raw18687; decide +kernel
      have hl : raw18687step0Labels = raw18687Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18687 raw18687Labels permutation624 permutation4
    mixedMoment B raw18687step0 raw18687step0Labels = mixedMoment B raw18687step1 raw18687step1Labels := by
      have ha : raw18687step1 = -raw18687step0 := by apply Matrix.ext; change ∀ i j, raw18687step1 i j = -(raw18687step0 i j); unfold raw18687step1 raw18687step0; decide +kernel
      have hl : raw18687step1Labels = raw18687step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18687step1 raw18687step1Labels = mixedMoment B raw18687step2 raw18687step2Labels := by
      have ha : raw18687step2 = raw18687step1 := by apply Matrix.ext; unfold raw18687step2 raw18687step1; decide +kernel
      have hl : raw18687step1Labels = labelEmbedding7 ∘ raw18687step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18687step1 raw18687step1Labels raw18687step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
