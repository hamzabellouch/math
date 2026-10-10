import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw12672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12672step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12672step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12672step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12672step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12672step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12672 raw12672Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw12672 raw12672Labels = mixedMoment B raw12672step0 raw12672step0Labels := by
      have hz : ∀ j, raw12672 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12672step0 = (fun i j => raw12672 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12672step0 raw12672; decide +kernel
      have hl : raw12672step0Labels = raw12672Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12672 raw12672Labels permutation265 hz
    mixedMoment B raw12672step0 raw12672step0Labels = mixedMoment B raw12672step1 raw12672step1Labels := by
      have ha : raw12672step1 = (fun i j => raw12672step0 (permutation79 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12672step1 raw12672step0; decide +kernel
      have hl : raw12672step1Labels = raw12672step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12672step0 raw12672step0Labels permutation79 permutation6
    mixedMoment B raw12672step1 raw12672step1Labels = mixedMoment B raw12672step2 raw12672step2Labels := by
      have ha : raw12672step2 = raw12672step1 := by apply Matrix.ext; unfold raw12672step2 raw12672step1; decide +kernel
      have hl : raw12672step1Labels = labelEmbedding9 ∘ raw12672step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12672step1 raw12672step1Labels raw12672step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw12673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12673step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12673step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12673step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12673 raw12673Labels = mixedMoment B node4566 node4566Labels := by
  calc
    mixedMoment B raw12673 raw12673Labels = mixedMoment B raw12673step0 raw12673step0Labels := by
      have ha : raw12673step0 = (fun i j => raw12673 (permutation195 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12673step0 raw12673; decide +kernel
      have hl : raw12673step0Labels = raw12673Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12673 raw12673Labels permutation195 permutation3
    mixedMoment B raw12673step0 raw12673step0Labels = mixedMoment B raw12673step1 raw12673step1Labels := by
      have ha : raw12673step1 = raw12673step0 := by apply Matrix.ext; unfold raw12673step1 raw12673step0; decide +kernel
      have hl : raw12673step0Labels = labelEmbedding6 ∘ raw12673step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12673step0 raw12673step0Labels raw12673step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4566 node4566Labels := by rfl

def raw12674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -3, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw12674step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12674step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12674step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12674step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw12674step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12674 raw12674Labels = mixedMoment B node5208 node5208Labels := by
  calc
    mixedMoment B raw12674 raw12674Labels = mixedMoment B raw12674step0 raw12674step0Labels := by
      have ha : raw12674step0 = (fun i j => raw12674 (permutation362 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12674step0 raw12674; decide +kernel
      have hl : raw12674step0Labels = raw12674Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12674 raw12674Labels permutation362 permutation4
    mixedMoment B raw12674step0 raw12674step0Labels = mixedMoment B raw12674step1 raw12674step1Labels := by
      have ha : raw12674step1 = -raw12674step0 := by apply Matrix.ext; change ∀ i j, raw12674step1 i j = -(raw12674step0 i j); unfold raw12674step1 raw12674step0; decide +kernel
      have hl : raw12674step1Labels = raw12674step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12674step1 raw12674step1Labels = mixedMoment B raw12674step2 raw12674step2Labels := by
      have ha : raw12674step2 = raw12674step1 := by apply Matrix.ext; unfold raw12674step2 raw12674step1; decide +kernel
      have hl : raw12674step1Labels = labelEmbedding7 ∘ raw12674step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12674step1 raw12674step1Labels raw12674step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5208 node5208Labels := by rfl

def raw12675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12675 raw12675Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw12675 raw12675Labels = mixedMoment B raw12675step0 raw12675step0Labels := by
      have ha : raw12675step0 = (fun i j => raw12675 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12675step0 raw12675; decide +kernel
      have hl : raw12675step0Labels = raw12675Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12675 raw12675Labels permutation206 permutation2
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw12676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw12676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12676 raw12676Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw12676 raw12676Labels = mixedMoment B raw12676step0 raw12676step0Labels := by
      have hz : ∀ j, raw12676 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12676step0 = (fun i j => raw12676 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12676step0 raw12676; decide +kernel
      have hl : raw12676step0Labels = raw12676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12676 raw12676Labels permutation520 hz
    mixedMoment B raw12676step0 raw12676step0Labels = mixedMoment B raw12676step1 raw12676step1Labels := by
      have ha : raw12676step1 = (fun i j => raw12676step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12676step1 raw12676step0; decide +kernel
      have hl : raw12676step1Labels = raw12676step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12676step0 raw12676step0Labels permutation40 permutation2
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw12677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12677step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw12677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12677 raw12677Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw12677 raw12677Labels = mixedMoment B raw12677step0 raw12677step0Labels := by
      have ha : raw12677step0 = (fun i j => raw12677 (permutation254 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12677step0 raw12677; decide +kernel
      have hl : raw12677step0Labels = raw12677Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12677 raw12677Labels permutation254 permutation2
    _ = mixedMoment B node5286 node5286Labels := by rfl

def raw12678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12678step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12678 raw12678Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw12678 raw12678Labels = mixedMoment B raw12678step0 raw12678step0Labels := by
      have hz : ∀ j, raw12678 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12678step0 = (fun i j => raw12678 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12678step0 raw12678; decide +kernel
      have hl : raw12678step0Labels = raw12678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12678 raw12678Labels permutation265 hz
    mixedMoment B raw12678step0 raw12678step0Labels = mixedMoment B raw12678step1 raw12678step1Labels := by
      have ha : raw12678step1 = (fun i j => raw12678step0 (permutation41 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12678step1 raw12678step0; decide +kernel
      have hl : raw12678step1Labels = raw12678step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12678step0 raw12678step0Labels permutation41 permutation2
    _ = mixedMoment B node4616 node4616Labels := by rfl

def raw12679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12679 raw12679Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw12679 raw12679Labels = mixedMoment B raw12679step0 raw12679step0Labels := by
      have ha : raw12679step0 = (fun i j => raw12679 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12679step0 raw12679; decide +kernel
      have hl : raw12679step0Labels = raw12679Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12679 raw12679Labels permutation161 permutation2
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw12680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12680step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12680 raw12680Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw12680 raw12680Labels = mixedMoment B raw12680step0 raw12680step0Labels := by
      have hz : ∀ j, raw12680 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12680step0 = (fun i j => raw12680 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12680step0 raw12680; decide +kernel
      have hl : raw12680step0Labels = raw12680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12680 raw12680Labels permutation265 hz
    mixedMoment B raw12680step0 raw12680step0Labels = mixedMoment B raw12680step1 raw12680step1Labels := by
      have ha : raw12680step1 = (fun i j => raw12680step0 (permutation41 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12680step1 raw12680step0; decide +kernel
      have hl : raw12680step1Labels = raw12680step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12680step0 raw12680step0Labels permutation41 permutation2
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw12681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw12681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12681step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12681step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12681step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12681step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12681 raw12681Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw12681 raw12681Labels = mixedMoment B raw12681step0 raw12681step0Labels := by
      have hz : ∀ j, raw12681 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12681step0 = (fun i j => raw12681 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12681step0 raw12681; decide +kernel
      have hl : raw12681step0Labels = raw12681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12681 raw12681Labels permutation520 hz
    mixedMoment B raw12681step0 raw12681step0Labels = mixedMoment B raw12681step1 raw12681step1Labels := by
      have hz : ∀ j, raw12681step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12681step1 = (fun i j => raw12681step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12681step1 raw12681step0; decide +kernel
      have hl : raw12681step1Labels = raw12681step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12681step0 raw12681step0Labels permutation56 hz
    mixedMoment B raw12681step1 raw12681step1Labels = mixedMoment B raw12681step2 raw12681step2Labels := by
      have ha : raw12681step2 = (fun i j => raw12681step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12681step2 raw12681step1; decide +kernel
      have hl : raw12681step2Labels = raw12681step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12681step1 raw12681step1Labels permutation11 permutation2
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw12682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12682step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12682step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12682 raw12682Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw12682 raw12682Labels = mixedMoment B raw12682step0 raw12682step0Labels := by
      have hz : ∀ j, raw12682 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12682step0 = (fun i j => raw12682 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12682step0 raw12682; decide +kernel
      have hl : raw12682step0Labels = raw12682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12682 raw12682Labels permutation265 hz
    mixedMoment B raw12682step0 raw12682step0Labels = mixedMoment B raw12682step1 raw12682step1Labels := by
      have ha : raw12682step1 = (fun i j => raw12682step0 (permutation53 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12682step1 raw12682step0; decide +kernel
      have hl : raw12682step1Labels = raw12682step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12682step0 raw12682step0Labels permutation53 permutation2
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw12683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw12683step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12683step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw12683step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12683 raw12683Labels = mixedMoment B node4567 node4567Labels := by
  calc
    mixedMoment B raw12683 raw12683Labels = mixedMoment B raw12683step0 raw12683step0Labels := by
      have hz : ∀ j, raw12683 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12683step0 = (fun i j => raw12683 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12683step0 raw12683; decide +kernel
      have hl : raw12683step0Labels = raw12683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12683 raw12683Labels permutation265 hz
    mixedMoment B raw12683step0 raw12683step0Labels = mixedMoment B raw12683step1 raw12683step1Labels := by
      have ha : raw12683step1 = (fun i j => raw12683step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12683step1 raw12683step0; decide +kernel
      have hl : raw12683step1Labels = raw12683step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12683step0 raw12683step0Labels permutation37 permutation3
    mixedMoment B raw12683step1 raw12683step1Labels = mixedMoment B raw12683step2 raw12683step2Labels := by
      have ha : raw12683step2 = raw12683step1 := by apply Matrix.ext; unfold raw12683step2 raw12683step1; decide +kernel
      have hl : raw12683step1Labels = labelEmbedding6 ∘ raw12683step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12683step1 raw12683step1Labels raw12683step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4567 node4567Labels := by rfl

def raw12684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw12684step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12684step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw12684step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12684 raw12684Labels = mixedMoment B node5060 node5060Labels := by
  calc
    mixedMoment B raw12684 raw12684Labels = mixedMoment B raw12684step0 raw12684step0Labels := by
      have ha : raw12684step0 = (fun i j => raw12684 (permutation501 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12684step0 raw12684; decide +kernel
      have hl : raw12684step0Labels = raw12684Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12684 raw12684Labels permutation501 permutation5
    mixedMoment B raw12684step0 raw12684step0Labels = mixedMoment B raw12684step1 raw12684step1Labels := by
      have ha : raw12684step1 = raw12684step0 := by apply Matrix.ext; unfold raw12684step1 raw12684step0; decide +kernel
      have hl : raw12684step0Labels = labelEmbedding8 ∘ raw12684step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12684step0 raw12684step0Labels raw12684step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5060 node5060Labels := by rfl

def raw12685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12685step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw12685step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12685step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw12685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12685 raw12685Labels = mixedMoment B node5062 node5062Labels := by
  calc
    mixedMoment B raw12685 raw12685Labels = mixedMoment B raw12685step0 raw12685step0Labels := by
      have hz : ∀ j, raw12685 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12685step0 = (fun i j => raw12685 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12685step0 raw12685; decide +kernel
      have hl : raw12685step0Labels = raw12685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12685 raw12685Labels permutation265 hz
    mixedMoment B raw12685step0 raw12685step0Labels = mixedMoment B raw12685step1 raw12685step1Labels := by
      have ha : raw12685step1 = (fun i j => raw12685step0 (permutation96 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12685step1 raw12685step0; decide +kernel
      have hl : raw12685step1Labels = raw12685step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12685step0 raw12685step0Labels permutation96 permutation5
    mixedMoment B raw12685step1 raw12685step1Labels = mixedMoment B raw12685step2 raw12685step2Labels := by
      have ha : raw12685step2 = raw12685step1 := by apply Matrix.ext; unfold raw12685step2 raw12685step1; decide +kernel
      have hl : raw12685step1Labels = labelEmbedding8 ∘ raw12685step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12685step1 raw12685step1Labels raw12685step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5062 node5062Labels := by rfl

def raw12686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![0, 0, 0], ![1, 0, -1]]
def raw12686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw12686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw12686step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12686step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw12686step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12686step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw12686step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12686 raw12686Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw12686 raw12686Labels = mixedMoment B raw12686step0 raw12686step0Labels := by
      have hz : ∀ j, raw12686 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12686step0 = (fun i j => raw12686 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12686step0 raw12686; decide +kernel
      have hl : raw12686step0Labels = raw12686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12686 raw12686Labels permutation520 hz
    mixedMoment B raw12686step0 raw12686step0Labels = mixedMoment B raw12686step1 raw12686step1Labels := by
      have hz : ∀ j, raw12686step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12686step1 = (fun i j => raw12686step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12686step1 raw12686step0; decide +kernel
      have hl : raw12686step1Labels = raw12686step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12686step0 raw12686step0Labels permutation56 hz
    mixedMoment B raw12686step1 raw12686step1Labels = mixedMoment B raw12686step2 raw12686step2Labels := by
      have ha : raw12686step2 = (fun i j => raw12686step1 (permutation24 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12686step2 raw12686step1; decide +kernel
      have hl : raw12686step2Labels = raw12686step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12686step1 raw12686step1Labels permutation24 permutation5
    mixedMoment B raw12686step2 raw12686step2Labels = mixedMoment B raw12686step3 raw12686step3Labels := by
      have ha : raw12686step3 = raw12686step2 := by apply Matrix.ext; unfold raw12686step3 raw12686step2; decide +kernel
      have hl : raw12686step2Labels = labelEmbedding8 ∘ raw12686step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12686step2 raw12686step2Labels raw12686step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw12687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw12687step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw12687step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12687 raw12687Labels = mixedMoment B node5103 node5103Labels := by
  calc
    mixedMoment B raw12687 raw12687Labels = mixedMoment B raw12687step0 raw12687step0Labels := by
      have hz : ∀ j, raw12687 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12687step0 = (fun i j => raw12687 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12687step0 raw12687; decide +kernel
      have hl : raw12687step0Labels = raw12687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12687 raw12687Labels permutation265 hz
    mixedMoment B raw12687step0 raw12687step0Labels = mixedMoment B raw12687step1 raw12687step1Labels := by
      have ha : raw12687step1 = (fun i j => raw12687step0 (permutation96 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12687step1 raw12687step0; decide +kernel
      have hl : raw12687step1Labels = raw12687step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12687step0 raw12687step0Labels permutation96 permutation5
    mixedMoment B raw12687step1 raw12687step1Labels = mixedMoment B raw12687step2 raw12687step2Labels := by
      have ha : raw12687step2 = raw12687step1 := by apply Matrix.ext; unfold raw12687step2 raw12687step1; decide +kernel
      have hl : raw12687step1Labels = labelEmbedding8 ∘ raw12687step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12687step1 raw12687step1Labels raw12687step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5103 node5103Labels := by rfl

def raw12688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw12688step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12688step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw12688step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12688 raw12688Labels = mixedMoment B node4568 node4568Labels := by
  calc
    mixedMoment B raw12688 raw12688Labels = mixedMoment B raw12688step0 raw12688step0Labels := by
      have hz : ∀ j, raw12688 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12688step0 = (fun i j => raw12688 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12688step0 raw12688; decide +kernel
      have hl : raw12688step0Labels = raw12688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12688 raw12688Labels permutation265 hz
    mixedMoment B raw12688step0 raw12688step0Labels = mixedMoment B raw12688step1 raw12688step1Labels := by
      have ha : raw12688step1 = (fun i j => raw12688step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12688step1 raw12688step0; decide +kernel
      have hl : raw12688step1Labels = raw12688step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12688step0 raw12688step0Labels permutation36 permutation3
    mixedMoment B raw12688step1 raw12688step1Labels = mixedMoment B raw12688step2 raw12688step2Labels := by
      have ha : raw12688step2 = raw12688step1 := by apply Matrix.ext; unfold raw12688step2 raw12688step1; decide +kernel
      have hl : raw12688step1Labels = labelEmbedding6 ∘ raw12688step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12688step1 raw12688step1Labels raw12688step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4568 node4568Labels := by rfl

def raw12689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw12689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12689 raw12689Labels = mixedMoment B node5154 node5154Labels := by
  calc
    mixedMoment B raw12689 raw12689Labels = mixedMoment B raw12689step0 raw12689step0Labels := by
      have ha : raw12689step0 = (fun i j => raw12689 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12689step0 raw12689; decide +kernel
      have hl : raw12689step0Labels = raw12689Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12689 raw12689Labels permutation153 permutation2
    _ = mixedMoment B node5154 node5154Labels := by rfl

def raw12690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -3, 2], ![0, 1, -1], ![-2, 2, 0], ![-2, 1, 1]]
def raw12690step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12690step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw12690step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12690step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw12690step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12690 raw12690Labels = mixedMoment B node5210 node5210Labels := by
  calc
    mixedMoment B raw12690 raw12690Labels = mixedMoment B raw12690step0 raw12690step0Labels := by
      have hz : ∀ j, raw12690 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12690step0 = (fun i j => raw12690 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12690step0 raw12690; decide +kernel
      have hl : raw12690step0Labels = raw12690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12690 raw12690Labels permutation265 hz
    mixedMoment B raw12690step0 raw12690step0Labels = mixedMoment B raw12690step1 raw12690step1Labels := by
      have ha : raw12690step1 = (fun i j => raw12690step0 (permutation61 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12690step1 raw12690step0; decide +kernel
      have hl : raw12690step1Labels = raw12690step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12690step0 raw12690step0Labels permutation61 permutation4
    mixedMoment B raw12690step1 raw12690step1Labels = mixedMoment B raw12690step2 raw12690step2Labels := by
      have ha : raw12690step2 = -raw12690step1 := by apply Matrix.ext; change ∀ i j, raw12690step2 i j = -(raw12690step1 i j); unfold raw12690step2 raw12690step1; decide +kernel
      have hl : raw12690step2Labels = raw12690step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12690step2 raw12690step2Labels = mixedMoment B raw12690step3 raw12690step3Labels := by
      have ha : raw12690step3 = raw12690step2 := by apply Matrix.ext; unfold raw12690step3 raw12690step2; decide +kernel
      have hl : raw12690step2Labels = labelEmbedding7 ∘ raw12690step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12690step2 raw12690step2Labels raw12690step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5210 node5210Labels := by rfl

def raw12691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12691step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12691 raw12691Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw12691 raw12691Labels = mixedMoment B raw12691step0 raw12691step0Labels := by
      have hz : ∀ j, raw12691 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12691step0 = (fun i j => raw12691 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12691step0 raw12691; decide +kernel
      have hl : raw12691step0Labels = raw12691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12691 raw12691Labels permutation265 hz
    mixedMoment B raw12691step0 raw12691step0Labels = mixedMoment B raw12691step1 raw12691step1Labels := by
      have ha : raw12691step1 = (fun i j => raw12691step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12691step1 raw12691step0; decide +kernel
      have hl : raw12691step1Labels = raw12691step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12691step0 raw12691step0Labels permutation39 permutation2
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw12692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1]]
def raw12692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1]]
def raw12692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw12692step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12692 raw12692Labels = mixedMoment B node5287 node5287Labels := by
  calc
    mixedMoment B raw12692 raw12692Labels = mixedMoment B raw12692step0 raw12692step0Labels := by
      have hz : ∀ j, raw12692 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12692step0 = (fun i j => raw12692 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12692step0 raw12692; decide +kernel
      have hl : raw12692step0Labels = raw12692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12692 raw12692Labels permutation265 hz
    mixedMoment B raw12692step0 raw12692step0Labels = mixedMoment B raw12692step1 raw12692step1Labels := by
      have ha : raw12692step1 = (fun i j => raw12692step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12692step1 raw12692step0; decide +kernel
      have hl : raw12692step1Labels = raw12692step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12692step0 raw12692step0Labels permutation50 permutation2
    _ = mixedMoment B node5287 node5287Labels := by rfl

def raw12693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12693step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw12693step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12693step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw12693step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12693 raw12693Labels = mixedMoment B node4571 node4571Labels := by
  calc
    mixedMoment B raw12693 raw12693Labels = mixedMoment B raw12693step0 raw12693step0Labels := by
      have hz : ∀ j, raw12693 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12693step0 = (fun i j => raw12693 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12693step0 raw12693; decide +kernel
      have hl : raw12693step0Labels = raw12693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12693 raw12693Labels permutation265 hz
    mixedMoment B raw12693step0 raw12693step0Labels = mixedMoment B raw12693step1 raw12693step1Labels := by
      have ha : raw12693step1 = (fun i j => raw12693step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12693step1 raw12693step0; decide +kernel
      have hl : raw12693step1Labels = raw12693step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12693step0 raw12693step0Labels permutation34 permutation3
    mixedMoment B raw12693step1 raw12693step1Labels = mixedMoment B raw12693step2 raw12693step2Labels := by
      have ha : raw12693step2 = raw12693step1 := by apply Matrix.ext; unfold raw12693step2 raw12693step1; decide +kernel
      have hl : raw12693step1Labels = labelEmbedding6 ∘ raw12693step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12693step1 raw12693step1Labels raw12693step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4571 node4571Labels := by rfl

def raw12694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12694 raw12694Labels = mixedMoment B node5153 node5153Labels := by
  calc
    _ = mixedMoment B node5153 node5153Labels := by rfl

def raw12695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12695 raw12695Labels = mixedMoment B node5211 node5211Labels := by
  calc
    mixedMoment B raw12695 raw12695Labels = mixedMoment B raw12695step0 raw12695step0Labels := by
      have hz : ∀ j, raw12695 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12695step0 = (fun i j => raw12695 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12695step0 raw12695; decide +kernel
      have hl : raw12695step0Labels = raw12695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12695 raw12695Labels permutation265 hz
    _ = mixedMoment B node5211 node5211Labels := by rfl

def raw12696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12696step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12696step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12696 raw12696Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw12696 raw12696Labels = mixedMoment B raw12696step0 raw12696step0Labels := by
      have hz : ∀ j, raw12696 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12696step0 = (fun i j => raw12696 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12696step0 raw12696; decide +kernel
      have hl : raw12696step0Labels = raw12696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12696 raw12696Labels permutation265 hz
    mixedMoment B raw12696step0 raw12696step0Labels = mixedMoment B raw12696step1 raw12696step1Labels := by
      have ha : raw12696step1 = (fun i j => raw12696step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12696step1 raw12696step0; decide +kernel
      have hl : raw12696step1Labels = raw12696step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12696step0 raw12696step0Labels permutation38 permutation2
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw12697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1]]
def raw12697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw12697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12697step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw12697step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12697 raw12697Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw12697 raw12697Labels = mixedMoment B raw12697step0 raw12697step0Labels := by
      have hz : ∀ j, raw12697 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12697step0 = (fun i j => raw12697 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12697step0 raw12697; decide +kernel
      have hl : raw12697step0Labels = raw12697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12697 raw12697Labels permutation520 hz
    mixedMoment B raw12697step0 raw12697step0Labels = mixedMoment B raw12697step1 raw12697step1Labels := by
      have hz : ∀ j, raw12697step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12697step1 = (fun i j => raw12697step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12697step1 raw12697step0; decide +kernel
      have hl : raw12697step1Labels = raw12697step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12697step0 raw12697step0Labels permutation56 hz
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw12698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12698step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12698 raw12698Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw12698 raw12698Labels = mixedMoment B raw12698step0 raw12698step0Labels := by
      have ha : raw12698step0 = (fun i j => raw12698 (permutation423 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12698step0 raw12698; decide +kernel
      have hl : raw12698step0Labels = raw12698Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12698 raw12698Labels permutation423 permutation6
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw12699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12699Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12699step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12699 raw12699Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw12699 raw12699Labels = mixedMoment B raw12699step0 raw12699step0Labels := by
      have hz : ∀ j, raw12699 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12699step0 = (fun i j => raw12699 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12699step0 raw12699; decide +kernel
      have hl : raw12699step0Labels = raw12699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12699 raw12699Labels permutation265 hz
    mixedMoment B raw12699step0 raw12699step0Labels = mixedMoment B raw12699step1 raw12699step1Labels := by
      have ha : raw12699step1 = (fun i j => raw12699step0 (permutation79 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12699step1 raw12699step0; decide +kernel
      have hl : raw12699step1Labels = raw12699step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12699step0 raw12699step0Labels permutation79 permutation6
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw12700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12700Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12700step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12700step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12700 raw12700Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw12700 raw12700Labels = mixedMoment B raw12700step0 raw12700step0Labels := by
      have hz : ∀ j, raw12700 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12700step0 = (fun i j => raw12700 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12700step0 raw12700; decide +kernel
      have hl : raw12700step0Labels = raw12700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12700 raw12700Labels permutation265 hz
    mixedMoment B raw12700step0 raw12700step0Labels = mixedMoment B raw12700step1 raw12700step1Labels := by
      have ha : raw12700step1 = (fun i j => raw12700step0 (permutation79 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12700step1 raw12700step0; decide +kernel
      have hl : raw12700step1Labels = raw12700step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12700step0 raw12700step0Labels permutation79 permutation6
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw12701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw12701Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12701step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12701step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12701step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12701step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12701step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12701 raw12701Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw12701 raw12701Labels = mixedMoment B raw12701step0 raw12701step0Labels := by
      have hz : ∀ j, raw12701 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12701step0 = (fun i j => raw12701 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12701step0 raw12701; decide +kernel
      have hl : raw12701step0Labels = raw12701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12701 raw12701Labels permutation520 hz
    mixedMoment B raw12701step0 raw12701step0Labels = mixedMoment B raw12701step1 raw12701step1Labels := by
      have hz : ∀ j, raw12701step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12701step1 = (fun i j => raw12701step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12701step1 raw12701step0; decide +kernel
      have hl : raw12701step1Labels = raw12701step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12701step0 raw12701step0Labels permutation56 hz
    mixedMoment B raw12701step1 raw12701step1Labels = mixedMoment B raw12701step2 raw12701step2Labels := by
      have ha : raw12701step2 = (fun i j => raw12701step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12701step2 raw12701step1; decide +kernel
      have hl : raw12701step2Labels = raw12701step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12701step1 raw12701step1Labels permutation19 permutation6
    _ = mixedMoment B node3862 node3862Labels := by rfl

def raw12702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12702Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12702step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12702step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12702 raw12702Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw12702 raw12702Labels = mixedMoment B raw12702step0 raw12702step0Labels := by
      have hz : ∀ j, raw12702 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12702step0 = (fun i j => raw12702 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12702step0 raw12702; decide +kernel
      have hl : raw12702step0Labels = raw12702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12702 raw12702Labels permutation265 hz
    mixedMoment B raw12702step0 raw12702step0Labels = mixedMoment B raw12702step1 raw12702step1Labels := by
      have ha : raw12702step1 = (fun i j => raw12702step0 (permutation79 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12702step1 raw12702step0; decide +kernel
      have hl : raw12702step1Labels = raw12702step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12702step0 raw12702step0Labels permutation79 permutation6
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw12703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12703Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12703step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12703 raw12703Labels = mixedMoment B node1183 node1183Labels := by
  calc
    mixedMoment B raw12703 raw12703Labels = mixedMoment B raw12703step0 raw12703step0Labels := by
      have ha : raw12703step0 = (fun i j => raw12703 (permutation195 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12703step0 raw12703; decide +kernel
      have hl : raw12703step0Labels = raw12703Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12703 raw12703Labels permutation195 permutation3
    _ = mixedMoment B node1183 node1183Labels := by rfl

def raw12704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12704Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12704step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12704 raw12704Labels = mixedMoment B node2836 node2836Labels := by
  calc
    mixedMoment B raw12704 raw12704Labels = mixedMoment B raw12704step0 raw12704step0Labels := by
      have ha : raw12704step0 = (fun i j => raw12704 (permutation195 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12704step0 raw12704; decide +kernel
      have hl : raw12704step0Labels = raw12704Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12704 raw12704Labels permutation195 permutation3
    _ = mixedMoment B node2836 node2836Labels := by rfl

def raw12705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12705Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12705step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12705 raw12705Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw12705 raw12705Labels = mixedMoment B raw12705step0 raw12705step0Labels := by
      have ha : raw12705step0 = (fun i j => raw12705 (permutation186 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12705step0 raw12705; decide +kernel
      have hl : raw12705step0Labels = raw12705Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12705 raw12705Labels permutation186 permutation3
    _ = mixedMoment B node3037 node3037Labels := by rfl

def raw12706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw12706Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12706step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12706step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12706 raw12706Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw12706 raw12706Labels = mixedMoment B raw12706step0 raw12706step0Labels := by
      have hz : ∀ j, raw12706 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12706step0 = (fun i j => raw12706 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12706step0 raw12706; decide +kernel
      have hl : raw12706step0Labels = raw12706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12706 raw12706Labels permutation520 hz
    mixedMoment B raw12706step0 raw12706step0Labels = mixedMoment B raw12706step1 raw12706step1Labels := by
      have ha : raw12706step1 = (fun i j => raw12706step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12706step1 raw12706step0; decide +kernel
      have hl : raw12706step1Labels = raw12706step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12706step0 raw12706step0Labels permutation42 permutation3
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw12707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12707Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12707step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw12707step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12707 raw12707Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw12707 raw12707Labels = mixedMoment B raw12707step0 raw12707step0Labels := by
      have ha : raw12707step0 = (fun i j => raw12707 (permutation195 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12707step0 raw12707; decide +kernel
      have hl : raw12707step0Labels = raw12707Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12707 raw12707Labels permutation195 permutation3
    _ = mixedMoment B node3023 node3023Labels := by rfl

def raw12708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12708Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12708step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12708step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12708 raw12708Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw12708 raw12708Labels = mixedMoment B raw12708step0 raw12708step0Labels := by
      have hz : ∀ j, raw12708 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12708step0 = (fun i j => raw12708 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12708step0 raw12708; decide +kernel
      have hl : raw12708step0Labels = raw12708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12708 raw12708Labels permutation265 hz
    mixedMoment B raw12708step0 raw12708step0Labels = mixedMoment B raw12708step1 raw12708step1Labels := by
      have ha : raw12708step1 = (fun i j => raw12708step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12708step1 raw12708step0; decide +kernel
      have hl : raw12708step1Labels = raw12708step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12708step0 raw12708step0Labels permutation37 permutation3
    _ = mixedMoment B node1291 node1291Labels := by rfl

def raw12709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12709Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12709step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12709 raw12709Labels = mixedMoment B node2951 node2951Labels := by
  calc
    mixedMoment B raw12709 raw12709Labels = mixedMoment B raw12709step0 raw12709step0Labels := by
      have ha : raw12709step0 = (fun i j => raw12709 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12709step0 raw12709; decide +kernel
      have hl : raw12709step0Labels = raw12709Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12709 raw12709Labels permutation157 permutation3
    _ = mixedMoment B node2951 node2951Labels := by rfl

def raw12710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12710Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12710step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12710step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12710 raw12710Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw12710 raw12710Labels = mixedMoment B raw12710step0 raw12710step0Labels := by
      have hz : ∀ j, raw12710 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12710step0 = (fun i j => raw12710 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12710step0 raw12710; decide +kernel
      have hl : raw12710step0Labels = raw12710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12710 raw12710Labels permutation265 hz
    mixedMoment B raw12710step0 raw12710step0Labels = mixedMoment B raw12710step1 raw12710step1Labels := by
      have ha : raw12710step1 = (fun i j => raw12710step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12710step1 raw12710step0; decide +kernel
      have hl : raw12710step1Labels = raw12710step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12710step0 raw12710step0Labels permutation39 permutation3
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw12711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw12711Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12711step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12711step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12711step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12711step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12711step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12711 raw12711Labels = mixedMoment B node3119 node3119Labels := by
  calc
    mixedMoment B raw12711 raw12711Labels = mixedMoment B raw12711step0 raw12711step0Labels := by
      have hz : ∀ j, raw12711 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12711step0 = (fun i j => raw12711 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12711step0 raw12711; decide +kernel
      have hl : raw12711step0Labels = raw12711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12711 raw12711Labels permutation520 hz
    mixedMoment B raw12711step0 raw12711step0Labels = mixedMoment B raw12711step1 raw12711step1Labels := by
      have hz : ∀ j, raw12711step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12711step1 = (fun i j => raw12711step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12711step1 raw12711step0; decide +kernel
      have hl : raw12711step1Labels = raw12711step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12711step0 raw12711step0Labels permutation56 hz
    mixedMoment B raw12711step1 raw12711step1Labels = mixedMoment B raw12711step2 raw12711step2Labels := by
      have ha : raw12711step2 = (fun i j => raw12711step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12711step2 raw12711step1; decide +kernel
      have hl : raw12711step2Labels = raw12711step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12711step1 raw12711step1Labels permutation9 permutation3
    _ = mixedMoment B node3119 node3119Labels := by rfl

def raw12712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12712Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12712step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12712step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12712 raw12712Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw12712 raw12712Labels = mixedMoment B raw12712step0 raw12712step0Labels := by
      have hz : ∀ j, raw12712 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12712step0 = (fun i j => raw12712 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12712step0 raw12712; decide +kernel
      have hl : raw12712step0Labels = raw12712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12712 raw12712Labels permutation265 hz
    mixedMoment B raw12712step0 raw12712step0Labels = mixedMoment B raw12712step1 raw12712step1Labels := by
      have ha : raw12712step1 = (fun i j => raw12712step0 (permutation51 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12712step1 raw12712step0; decide +kernel
      have hl : raw12712step1Labels = raw12712step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12712step0 raw12712step0Labels permutation51 permutation3
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw12713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12713Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12713step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw12713step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12713 raw12713Labels = mixedMoment B node1184 node1184Labels := by
  calc
    mixedMoment B raw12713 raw12713Labels = mixedMoment B raw12713step0 raw12713step0Labels := by
      have hz : ∀ j, raw12713 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12713step0 = (fun i j => raw12713 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12713step0 raw12713; decide +kernel
      have hl : raw12713step0Labels = raw12713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12713 raw12713Labels permutation265 hz
    mixedMoment B raw12713step0 raw12713step0Labels = mixedMoment B raw12713step1 raw12713step1Labels := by
      have ha : raw12713step1 = (fun i j => raw12713step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12713step1 raw12713step0; decide +kernel
      have hl : raw12713step1Labels = raw12713step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12713step0 raw12713step0Labels permutation37 permutation3
    _ = mixedMoment B node1184 node1184Labels := by rfl

def raw12714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12714Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw12714step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12714 raw12714Labels = mixedMoment B node2906 node2906Labels := by
  calc
    mixedMoment B raw12714 raw12714Labels = mixedMoment B raw12714step0 raw12714step0Labels := by
      have ha : raw12714step0 = (fun i j => raw12714 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12714step0 raw12714; decide +kernel
      have hl : raw12714step0Labels = raw12714Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12714 raw12714Labels permutation157 permutation3
    _ = mixedMoment B node2906 node2906Labels := by rfl

def raw12715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12715Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12715step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw12715step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12715 raw12715Labels = mixedMoment B node2837 node2837Labels := by
  calc
    mixedMoment B raw12715 raw12715Labels = mixedMoment B raw12715step0 raw12715step0Labels := by
      have hz : ∀ j, raw12715 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12715step0 = (fun i j => raw12715 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12715step0 raw12715; decide +kernel
      have hl : raw12715step0Labels = raw12715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12715 raw12715Labels permutation265 hz
    mixedMoment B raw12715step0 raw12715step0Labels = mixedMoment B raw12715step1 raw12715step1Labels := by
      have ha : raw12715step1 = (fun i j => raw12715step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12715step1 raw12715step0; decide +kernel
      have hl : raw12715step1Labels = raw12715step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12715step0 raw12715step0Labels permutation37 permutation3
    _ = mixedMoment B node2837 node2837Labels := by rfl

def raw12716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![0, 0, 0], ![1, 0, -1]]
def raw12716Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw12716step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12716step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw12716step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12716step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw12716step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12716 raw12716Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw12716 raw12716Labels = mixedMoment B raw12716step0 raw12716step0Labels := by
      have hz : ∀ j, raw12716 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12716step0 = (fun i j => raw12716 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12716step0 raw12716; decide +kernel
      have hl : raw12716step0Labels = raw12716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12716 raw12716Labels permutation520 hz
    mixedMoment B raw12716step0 raw12716step0Labels = mixedMoment B raw12716step1 raw12716step1Labels := by
      have hz : ∀ j, raw12716step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12716step1 = (fun i j => raw12716step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12716step1 raw12716step0; decide +kernel
      have hl : raw12716step1Labels = raw12716step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12716step0 raw12716step0Labels permutation56 hz
    mixedMoment B raw12716step1 raw12716step1Labels = mixedMoment B raw12716step2 raw12716step2Labels := by
      have ha : raw12716step2 = (fun i j => raw12716step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12716step2 raw12716step1; decide +kernel
      have hl : raw12716step2Labels = raw12716step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12716step1 raw12716step1Labels permutation9 permutation3
    _ = mixedMoment B node3052 node3052Labels := by rfl

def raw12717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12717Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12717step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw12717step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12717 raw12717Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw12717 raw12717Labels = mixedMoment B raw12717step0 raw12717step0Labels := by
      have hz : ∀ j, raw12717 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12717step0 = (fun i j => raw12717 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12717step0 raw12717; decide +kernel
      have hl : raw12717step0Labels = raw12717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12717 raw12717Labels permutation265 hz
    mixedMoment B raw12717step0 raw12717step0Labels = mixedMoment B raw12717step1 raw12717step1Labels := by
      have ha : raw12717step1 = (fun i j => raw12717step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12717step1 raw12717step0; decide +kernel
      have hl : raw12717step1Labels = raw12717step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12717step0 raw12717step0Labels permutation37 permutation3
    _ = mixedMoment B node3024 node3024Labels := by rfl

def raw12718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12718Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12718step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw12718step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12718 raw12718Labels = mixedMoment B node1185 node1185Labels := by
  calc
    mixedMoment B raw12718 raw12718Labels = mixedMoment B raw12718step0 raw12718step0Labels := by
      have hz : ∀ j, raw12718 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12718step0 = (fun i j => raw12718 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12718step0 raw12718; decide +kernel
      have hl : raw12718step0Labels = raw12718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12718 raw12718Labels permutation265 hz
    mixedMoment B raw12718step0 raw12718step0Labels = mixedMoment B raw12718step1 raw12718step1Labels := by
      have ha : raw12718step1 = (fun i j => raw12718step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12718step1 raw12718step0; decide +kernel
      have hl : raw12718step1Labels = raw12718step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12718step0 raw12718step0Labels permutation36 permutation3
    _ = mixedMoment B node1185 node1185Labels := by rfl

def raw12719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12719Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw12719step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12719 raw12719Labels = mixedMoment B node2907 node2907Labels := by
  calc
    mixedMoment B raw12719 raw12719Labels = mixedMoment B raw12719step0 raw12719step0Labels := by
      have ha : raw12719step0 = (fun i j => raw12719 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12719step0 raw12719; decide +kernel
      have hl : raw12719step0Labels = raw12719Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12719 raw12719Labels permutation156 permutation3
    _ = mixedMoment B node2907 node2907Labels := by rfl

def raw12720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12720Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12720step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw12720step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12720 raw12720Labels = mixedMoment B node2838 node2838Labels := by
  calc
    mixedMoment B raw12720 raw12720Labels = mixedMoment B raw12720step0 raw12720step0Labels := by
      have hz : ∀ j, raw12720 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12720step0 = (fun i j => raw12720 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12720step0 raw12720; decide +kernel
      have hl : raw12720step0Labels = raw12720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12720 raw12720Labels permutation265 hz
    mixedMoment B raw12720step0 raw12720step0Labels = mixedMoment B raw12720step1 raw12720step1Labels := by
      have ha : raw12720step1 = (fun i j => raw12720step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12720step1 raw12720step0; decide +kernel
      have hl : raw12720step1Labels = raw12720step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12720step0 raw12720step0Labels permutation36 permutation3
    _ = mixedMoment B node2838 node2838Labels := by rfl

def raw12721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12721Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12721step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12721step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12721 raw12721Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw12721 raw12721Labels = mixedMoment B raw12721step0 raw12721step0Labels := by
      have hz : ∀ j, raw12721 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12721step0 = (fun i j => raw12721 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12721step0 raw12721; decide +kernel
      have hl : raw12721step0Labels = raw12721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12721 raw12721Labels permutation265 hz
    mixedMoment B raw12721step0 raw12721step0Labels = mixedMoment B raw12721step1 raw12721step1Labels := by
      have ha : raw12721step1 = (fun i j => raw12721step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12721step1 raw12721step0; decide +kernel
      have hl : raw12721step1Labels = raw12721step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12721step0 raw12721step0Labels permutation33 permutation3
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw12722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1]]
def raw12722Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1]]
def raw12722step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw12722step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12722 raw12722Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw12722 raw12722Labels = mixedMoment B raw12722step0 raw12722step0Labels := by
      have hz : ∀ j, raw12722 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12722step0 = (fun i j => raw12722 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12722step0 raw12722; decide +kernel
      have hl : raw12722step0Labels = raw12722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12722 raw12722Labels permutation265 hz
    mixedMoment B raw12722step0 raw12722step0Labels = mixedMoment B raw12722step1 raw12722step1Labels := by
      have ha : raw12722step1 = (fun i j => raw12722step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12722step1 raw12722step0; decide +kernel
      have hl : raw12722step1Labels = raw12722step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12722step0 raw12722step0Labels permutation36 permutation3
    _ = mixedMoment B node3025 node3025Labels := by rfl

def raw12723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12723Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12723step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw12723step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12723 raw12723Labels = mixedMoment B node1189 node1189Labels := by
  calc
    mixedMoment B raw12723 raw12723Labels = mixedMoment B raw12723step0 raw12723step0Labels := by
      have hz : ∀ j, raw12723 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12723step0 = (fun i j => raw12723 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12723step0 raw12723; decide +kernel
      have hl : raw12723step0Labels = raw12723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12723 raw12723Labels permutation265 hz
    mixedMoment B raw12723step0 raw12723step0Labels = mixedMoment B raw12723step1 raw12723step1Labels := by
      have ha : raw12723step1 = (fun i j => raw12723step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12723step1 raw12723step0; decide +kernel
      have hl : raw12723step1Labels = raw12723step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12723step0 raw12723step0Labels permutation34 permutation3
    _ = mixedMoment B node1189 node1189Labels := by rfl

def raw12724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12724Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12724step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw12724step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12724 raw12724Labels = mixedMoment B node2909 node2909Labels := by
  calc
    mixedMoment B raw12724 raw12724Labels = mixedMoment B raw12724step0 raw12724step0Labels := by
      have ha : raw12724step0 = (fun i j => raw12724 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12724step0 raw12724; decide +kernel
      have hl : raw12724step0Labels = raw12724Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12724 raw12724Labels permutation154 permutation3
    _ = mixedMoment B node2909 node2909Labels := by rfl

def raw12725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12725Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12725step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw12725step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12725 raw12725Labels = mixedMoment B node2841 node2841Labels := by
  calc
    mixedMoment B raw12725 raw12725Labels = mixedMoment B raw12725step0 raw12725step0Labels := by
      have hz : ∀ j, raw12725 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12725step0 = (fun i j => raw12725 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12725step0 raw12725; decide +kernel
      have hl : raw12725step0Labels = raw12725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12725 raw12725Labels permutation265 hz
    mixedMoment B raw12725step0 raw12725step0Labels = mixedMoment B raw12725step1 raw12725step1Labels := by
      have ha : raw12725step1 = (fun i j => raw12725step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12725step1 raw12725step0; decide +kernel
      have hl : raw12725step1Labels = raw12725step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12725step0 raw12725step0Labels permutation34 permutation3
    _ = mixedMoment B node2841 node2841Labels := by rfl

def raw12726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12726Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12726step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12726step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12726 raw12726Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw12726 raw12726Labels = mixedMoment B raw12726step0 raw12726step0Labels := by
      have hz : ∀ j, raw12726 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12726step0 = (fun i j => raw12726 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12726step0 raw12726; decide +kernel
      have hl : raw12726step0Labels = raw12726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12726 raw12726Labels permutation265 hz
    mixedMoment B raw12726step0 raw12726step0Labels = mixedMoment B raw12726step1 raw12726step1Labels := by
      have ha : raw12726step1 = (fun i j => raw12726step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12726step1 raw12726step0; decide +kernel
      have hl : raw12726step1Labels = raw12726step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12726step0 raw12726step0Labels permutation32 permutation3
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw12727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1]]
def raw12727Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw12727step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw12727step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12727step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw12727step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12727 raw12727Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw12727 raw12727Labels = mixedMoment B raw12727step0 raw12727step0Labels := by
      have hz : ∀ j, raw12727 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12727step0 = (fun i j => raw12727 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12727step0 raw12727; decide +kernel
      have hl : raw12727step0Labels = raw12727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12727 raw12727Labels permutation520 hz
    mixedMoment B raw12727step0 raw12727step0Labels = mixedMoment B raw12727step1 raw12727step1Labels := by
      have hz : ∀ j, raw12727step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12727step1 = (fun i j => raw12727step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12727step1 raw12727step0; decide +kernel
      have hl : raw12727step1Labels = raw12727step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12727step0 raw12727step0Labels permutation56 hz
    mixedMoment B raw12727step1 raw12727step1Labels = mixedMoment B raw12727step2 raw12727step2Labels := by
      have ha : raw12727step2 = (fun i j => raw12727step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12727step2 raw12727step1; decide +kernel
      have hl : raw12727step2Labels = raw12727step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12727step1 raw12727step1Labels permutation8 permutation3
    _ = mixedMoment B node3055 node3055Labels := by rfl

def raw12728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12728step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12728step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12728step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12728step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12728step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12728step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12728 raw12728Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw12728 raw12728Labels = mixedMoment B raw12728step0 raw12728step0Labels := by
      have ha : raw12728step0 = (fun i j => raw12728 (permutation203 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12728step0 raw12728; decide +kernel
      have hl : raw12728step0Labels = raw12728Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12728 raw12728Labels permutation203 permutation7
    mixedMoment B raw12728step0 raw12728step0Labels = mixedMoment B raw12728step1 raw12728step1Labels := by
      have ha : raw12728step1 = -raw12728step0 := by apply Matrix.ext; change ∀ i j, raw12728step1 i j = -(raw12728step0 i j); unfold raw12728step1 raw12728step0; decide +kernel
      have hl : raw12728step1Labels = raw12728step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12728step1 raw12728step1Labels = mixedMoment B raw12728step2 raw12728step2Labels := by
      have ha : raw12728step2 = raw12728step1 := by apply Matrix.ext; unfold raw12728step2 raw12728step1; decide +kernel
      have hl : raw12728step1Labels = labelEmbedding1 ∘ raw12728step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12728step1 raw12728step1Labels raw12728step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw12729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12729step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12729step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12729step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12729step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12729step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12729 raw12729Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw12729 raw12729Labels = mixedMoment B raw12729step0 raw12729step0Labels := by
      have hz : ∀ j, raw12729 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12729step0 = (fun i j => raw12729 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12729step0 raw12729; decide +kernel
      have hl : raw12729step0Labels = raw12729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12729 raw12729Labels permutation265 hz
    mixedMoment B raw12729step0 raw12729step0Labels = mixedMoment B raw12729step1 raw12729step1Labels := by
      have ha : raw12729step1 = (fun i j => raw12729step0 (permutation61 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12729step1 raw12729step0; decide +kernel
      have hl : raw12729step1Labels = raw12729step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12729step0 raw12729step0Labels permutation61 permutation5
    mixedMoment B raw12729step1 raw12729step1Labels = mixedMoment B raw12729step2 raw12729step2Labels := by
      have ha : raw12729step2 = -raw12729step1 := by apply Matrix.ext; change ∀ i j, raw12729step2 i j = -(raw12729step1 i j); unfold raw12729step2 raw12729step1; decide +kernel
      have hl : raw12729step2Labels = raw12729step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12729step2 raw12729step2Labels = mixedMoment B raw12729step3 raw12729step3Labels := by
      have ha : raw12729step3 = raw12729step2 := by apply Matrix.ext; unfold raw12729step3 raw12729step2; decide +kernel
      have hl : raw12729step2Labels = labelEmbedding1 ∘ raw12729step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12729step2 raw12729step2Labels raw12729step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw12730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12730step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12730step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12730step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12730step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12730 raw12730Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw12730 raw12730Labels = mixedMoment B raw12730step0 raw12730step0Labels := by
      have hz : ∀ j, raw12730 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12730step0 = (fun i j => raw12730 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12730step0 raw12730; decide +kernel
      have hl : raw12730step0Labels = raw12730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12730 raw12730Labels permutation265 hz
    mixedMoment B raw12730step0 raw12730step0Labels = mixedMoment B raw12730step1 raw12730step1Labels := by
      have ha : raw12730step1 = (fun i j => raw12730step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12730step1 raw12730step0; decide +kernel
      have hl : raw12730step1Labels = raw12730step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12730step0 raw12730step0Labels permutation41 permutation7
    mixedMoment B raw12730step1 raw12730step1Labels = mixedMoment B raw12730step2 raw12730step2Labels := by
      have ha : raw12730step2 = -raw12730step1 := by apply Matrix.ext; change ∀ i j, raw12730step2 i j = -(raw12730step1 i j); unfold raw12730step2 raw12730step1; decide +kernel
      have hl : raw12730step2Labels = raw12730step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12730step2 raw12730step2Labels = mixedMoment B raw12730step3 raw12730step3Labels := by
      have ha : raw12730step3 = raw12730step2 := by apply Matrix.ext; unfold raw12730step3 raw12730step2; decide +kernel
      have hl : raw12730step2Labels = labelEmbedding1 ∘ raw12730step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12730step2 raw12730step2Labels raw12730step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw12731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw12731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12731step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12731step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12731step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12731step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12731step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12731step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12731step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12731step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12731step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12731 raw12731Labels = mixedMoment B node3889 node3889Labels := by
  calc
    mixedMoment B raw12731 raw12731Labels = mixedMoment B raw12731step0 raw12731step0Labels := by
      have hz : ∀ j, raw12731 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12731step0 = (fun i j => raw12731 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12731step0 raw12731; decide +kernel
      have hl : raw12731step0Labels = raw12731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12731 raw12731Labels permutation520 hz
    mixedMoment B raw12731step0 raw12731step0Labels = mixedMoment B raw12731step1 raw12731step1Labels := by
      have hz : ∀ j, raw12731step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12731step1 = (fun i j => raw12731step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12731step1 raw12731step0; decide +kernel
      have hl : raw12731step1Labels = raw12731step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12731step0 raw12731step0Labels permutation56 hz
    mixedMoment B raw12731step1 raw12731step1Labels = mixedMoment B raw12731step2 raw12731step2Labels := by
      have ha : raw12731step2 = (fun i j => raw12731step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12731step2 raw12731step1; decide +kernel
      have hl : raw12731step2Labels = raw12731step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12731step1 raw12731step1Labels permutation11 permutation7
    mixedMoment B raw12731step2 raw12731step2Labels = mixedMoment B raw12731step3 raw12731step3Labels := by
      have ha : raw12731step3 = -raw12731step2 := by apply Matrix.ext; change ∀ i j, raw12731step3 i j = -(raw12731step2 i j); unfold raw12731step3 raw12731step2; decide +kernel
      have hl : raw12731step3Labels = raw12731step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12731step3 raw12731step3Labels = mixedMoment B raw12731step4 raw12731step4Labels := by
      have ha : raw12731step4 = raw12731step3 := by apply Matrix.ext; unfold raw12731step4 raw12731step3; decide +kernel
      have hl : raw12731step3Labels = labelEmbedding1 ∘ raw12731step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12731step3 raw12731step3Labels raw12731step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3889 node3889Labels := by rfl

def raw12732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw12732step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12732step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12732step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12732step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12732step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12732 raw12732Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw12732 raw12732Labels = mixedMoment B raw12732step0 raw12732step0Labels := by
      have hz : ∀ j, raw12732 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12732step0 = (fun i j => raw12732 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12732step0 raw12732; decide +kernel
      have hl : raw12732step0Labels = raw12732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12732 raw12732Labels permutation265 hz
    mixedMoment B raw12732step0 raw12732step0Labels = mixedMoment B raw12732step1 raw12732step1Labels := by
      have ha : raw12732step1 = (fun i j => raw12732step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12732step1 raw12732step0; decide +kernel
      have hl : raw12732step1Labels = raw12732step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12732step0 raw12732step0Labels permutation41 permutation7
    mixedMoment B raw12732step1 raw12732step1Labels = mixedMoment B raw12732step2 raw12732step2Labels := by
      have ha : raw12732step2 = -raw12732step1 := by apply Matrix.ext; change ∀ i j, raw12732step2 i j = -(raw12732step1 i j); unfold raw12732step2 raw12732step1; decide +kernel
      have hl : raw12732step2Labels = raw12732step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12732step2 raw12732step2Labels = mixedMoment B raw12732step3 raw12732step3Labels := by
      have ha : raw12732step3 = raw12732step2 := by apply Matrix.ext; unfold raw12732step3 raw12732step2; decide +kernel
      have hl : raw12732step2Labels = labelEmbedding1 ∘ raw12732step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12732step2 raw12732step2Labels raw12732step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3883 node3883Labels := by rfl

def raw12733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12733step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12733step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12733step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12733step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12733step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12733 raw12733Labels = mixedMoment B node3239 node3239Labels := by
  calc
    mixedMoment B raw12733 raw12733Labels = mixedMoment B raw12733step0 raw12733step0Labels := by
      have ha : raw12733step0 = (fun i j => raw12733 (permutation195 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12733step0 raw12733; decide +kernel
      have hl : raw12733step0Labels = raw12733Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12733 raw12733Labels permutation195 permutation5
    mixedMoment B raw12733step0 raw12733step0Labels = mixedMoment B raw12733step1 raw12733step1Labels := by
      have ha : raw12733step1 = -raw12733step0 := by apply Matrix.ext; change ∀ i j, raw12733step1 i j = -(raw12733step0 i j); unfold raw12733step1 raw12733step0; decide +kernel
      have hl : raw12733step1Labels = raw12733step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12733step1 raw12733step1Labels = mixedMoment B raw12733step2 raw12733step2Labels := by
      have ha : raw12733step2 = raw12733step1 := by apply Matrix.ext; unfold raw12733step2 raw12733step1; decide +kernel
      have hl : raw12733step1Labels = labelEmbedding1 ∘ raw12733step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12733step1 raw12733step1Labels raw12733step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3239 node3239Labels := by rfl

def raw12734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12734step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12734step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12734step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12734 raw12734Labels = mixedMoment B node2834 node2834Labels := by
  calc
    mixedMoment B raw12734 raw12734Labels = mixedMoment B raw12734step0 raw12734step0Labels := by
      have ha : raw12734step0 = (fun i j => raw12734 (permutation362 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12734step0 raw12734; decide +kernel
      have hl : raw12734step0Labels = raw12734Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12734 raw12734Labels permutation362 permutation5
    mixedMoment B raw12734step0 raw12734step0Labels = mixedMoment B raw12734step1 raw12734step1Labels := by
      have ha : raw12734step1 = -raw12734step0 := by apply Matrix.ext; change ∀ i j, raw12734step1 i j = -(raw12734step0 i j); unfold raw12734step1 raw12734step0; decide +kernel
      have hl : raw12734step1Labels = raw12734step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12734step1 raw12734step1Labels = mixedMoment B raw12734step2 raw12734step2Labels := by
      have ha : raw12734step2 = raw12734step1 := by apply Matrix.ext; unfold raw12734step2 raw12734step1; decide +kernel
      have hl : raw12734step1Labels = labelEmbedding1 ∘ raw12734step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12734step1 raw12734step1Labels raw12734step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2834 node2834Labels := by rfl

def raw12735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12735step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12735step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12735step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12735step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12735step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12735 raw12735Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw12735 raw12735Labels = mixedMoment B raw12735step0 raw12735step0Labels := by
      have ha : raw12735step0 = (fun i j => raw12735 (permutation203 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12735step0 raw12735; decide +kernel
      have hl : raw12735step0Labels = raw12735Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12735 raw12735Labels permutation203 permutation7
    mixedMoment B raw12735step0 raw12735step0Labels = mixedMoment B raw12735step1 raw12735step1Labels := by
      have ha : raw12735step1 = -raw12735step0 := by apply Matrix.ext; change ∀ i j, raw12735step1 i j = -(raw12735step0 i j); unfold raw12735step1 raw12735step0; decide +kernel
      have hl : raw12735step1Labels = raw12735step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12735step1 raw12735step1Labels = mixedMoment B raw12735step2 raw12735step2Labels := by
      have ha : raw12735step2 = raw12735step1 := by apply Matrix.ext; unfold raw12735step2 raw12735step1; decide +kernel
      have hl : raw12735step1Labels = labelEmbedding1 ∘ raw12735step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12735step1 raw12735step1Labels raw12735step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw12736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw12736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12736step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12736step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12736step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12736step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12736step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12736 raw12736Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw12736 raw12736Labels = mixedMoment B raw12736step0 raw12736step0Labels := by
      have hz : ∀ j, raw12736 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12736step0 = (fun i j => raw12736 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12736step0 raw12736; decide +kernel
      have hl : raw12736step0Labels = raw12736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12736 raw12736Labels permutation520 hz
    mixedMoment B raw12736step0 raw12736step0Labels = mixedMoment B raw12736step1 raw12736step1Labels := by
      have ha : raw12736step1 = (fun i j => raw12736step0 (permutation45 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12736step1 raw12736step0; decide +kernel
      have hl : raw12736step1Labels = raw12736step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12736step0 raw12736step0Labels permutation45 permutation7
    mixedMoment B raw12736step1 raw12736step1Labels = mixedMoment B raw12736step2 raw12736step2Labels := by
      have ha : raw12736step2 = -raw12736step1 := by apply Matrix.ext; change ∀ i j, raw12736step2 i j = -(raw12736step1 i j); unfold raw12736step2 raw12736step1; decide +kernel
      have hl : raw12736step2Labels = raw12736step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12736step2 raw12736step2Labels = mixedMoment B raw12736step3 raw12736step3Labels := by
      have ha : raw12736step3 = raw12736step2 := by apply Matrix.ext; unfold raw12736step3 raw12736step2; decide +kernel
      have hl : raw12736step2Labels = labelEmbedding1 ∘ raw12736step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12736step2 raw12736step2Labels raw12736step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw12737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw12737step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12737step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12737step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12737step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12737 raw12737Labels = mixedMoment B node3567 node3567Labels := by
  calc
    mixedMoment B raw12737 raw12737Labels = mixedMoment B raw12737step0 raw12737step0Labels := by
      have ha : raw12737step0 = (fun i j => raw12737 (permutation203 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12737step0 raw12737; decide +kernel
      have hl : raw12737step0Labels = raw12737Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12737 raw12737Labels permutation203 permutation7
    mixedMoment B raw12737step0 raw12737step0Labels = mixedMoment B raw12737step1 raw12737step1Labels := by
      have ha : raw12737step1 = -raw12737step0 := by apply Matrix.ext; change ∀ i j, raw12737step1 i j = -(raw12737step0 i j); unfold raw12737step1 raw12737step0; decide +kernel
      have hl : raw12737step1Labels = raw12737step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12737step1 raw12737step1Labels = mixedMoment B raw12737step2 raw12737step2Labels := by
      have ha : raw12737step2 = raw12737step1 := by apply Matrix.ext; unfold raw12737step2 raw12737step1; decide +kernel
      have hl : raw12737step1Labels = labelEmbedding1 ∘ raw12737step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12737step1 raw12737step1Labels raw12737step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3567 node3567Labels := by rfl

def raw12738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12738step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12738step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12738step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12738step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12738step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12738 raw12738Labels = mixedMoment B node3303 node3303Labels := by
  calc
    mixedMoment B raw12738 raw12738Labels = mixedMoment B raw12738step0 raw12738step0Labels := by
      have hz : ∀ j, raw12738 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12738step0 = (fun i j => raw12738 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12738step0 raw12738; decide +kernel
      have hl : raw12738step0Labels = raw12738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12738 raw12738Labels permutation265 hz
    mixedMoment B raw12738step0 raw12738step0Labels = mixedMoment B raw12738step1 raw12738step1Labels := by
      have ha : raw12738step1 = (fun i j => raw12738step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12738step1 raw12738step0; decide +kernel
      have hl : raw12738step1Labels = raw12738step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12738step0 raw12738step0Labels permutation37 permutation5
    mixedMoment B raw12738step1 raw12738step1Labels = mixedMoment B raw12738step2 raw12738step2Labels := by
      have ha : raw12738step2 = -raw12738step1 := by apply Matrix.ext; change ∀ i j, raw12738step2 i j = -(raw12738step1 i j); unfold raw12738step2 raw12738step1; decide +kernel
      have hl : raw12738step2Labels = raw12738step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12738step2 raw12738step2Labels = mixedMoment B raw12738step3 raw12738step3Labels := by
      have ha : raw12738step3 = raw12738step2 := by apply Matrix.ext; unfold raw12738step3 raw12738step2; decide +kernel
      have hl : raw12738step2Labels = labelEmbedding1 ∘ raw12738step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12738step2 raw12738step2Labels raw12738step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3303 node3303Labels := by rfl

def raw12739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12739step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12739step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12739step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12739step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12739step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12739 raw12739Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw12739 raw12739Labels = mixedMoment B raw12739step0 raw12739step0Labels := by
      have ha : raw12739step0 = (fun i j => raw12739 (permutation203 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12739step0 raw12739; decide +kernel
      have hl : raw12739step0Labels = raw12739Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12739 raw12739Labels permutation203 permutation7
    mixedMoment B raw12739step0 raw12739step0Labels = mixedMoment B raw12739step1 raw12739step1Labels := by
      have ha : raw12739step1 = -raw12739step0 := by apply Matrix.ext; change ∀ i j, raw12739step1 i j = -(raw12739step0 i j); unfold raw12739step1 raw12739step0; decide +kernel
      have hl : raw12739step1Labels = raw12739step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12739step1 raw12739step1Labels = mixedMoment B raw12739step2 raw12739step2Labels := by
      have ha : raw12739step2 = raw12739step1 := by apply Matrix.ext; unfold raw12739step2 raw12739step1; decide +kernel
      have hl : raw12739step1Labels = labelEmbedding1 ∘ raw12739step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12739step1 raw12739step1Labels raw12739step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

def raw12740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12740step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12740step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12740step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12740step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12740 raw12740Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw12740 raw12740Labels = mixedMoment B raw12740step0 raw12740step0Labels := by
      have hz : ∀ j, raw12740 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12740step0 = (fun i j => raw12740 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12740step0 raw12740; decide +kernel
      have hl : raw12740step0Labels = raw12740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12740 raw12740Labels permutation265 hz
    mixedMoment B raw12740step0 raw12740step0Labels = mixedMoment B raw12740step1 raw12740step1Labels := by
      have ha : raw12740step1 = (fun i j => raw12740step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12740step1 raw12740step0; decide +kernel
      have hl : raw12740step1Labels = raw12740step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12740step0 raw12740step0Labels permutation41 permutation7
    mixedMoment B raw12740step1 raw12740step1Labels = mixedMoment B raw12740step2 raw12740step2Labels := by
      have ha : raw12740step2 = -raw12740step1 := by apply Matrix.ext; change ∀ i j, raw12740step2 i j = -(raw12740step1 i j); unfold raw12740step2 raw12740step1; decide +kernel
      have hl : raw12740step2Labels = raw12740step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12740step2 raw12740step2Labels = mixedMoment B raw12740step3 raw12740step3Labels := by
      have ha : raw12740step3 = raw12740step2 := by apply Matrix.ext; unfold raw12740step3 raw12740step2; decide +kernel
      have hl : raw12740step2Labels = labelEmbedding1 ∘ raw12740step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12740step2 raw12740step2Labels raw12740step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw12741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw12741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12741step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12741step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw12741step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12741step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12741step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12741step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12741step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12741step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12741step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12741 raw12741Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw12741 raw12741Labels = mixedMoment B raw12741step0 raw12741step0Labels := by
      have hz : ∀ j, raw12741 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12741step0 = (fun i j => raw12741 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12741step0 raw12741; decide +kernel
      have hl : raw12741step0Labels = raw12741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12741 raw12741Labels permutation520 hz
    mixedMoment B raw12741step0 raw12741step0Labels = mixedMoment B raw12741step1 raw12741step1Labels := by
      have hz : ∀ j, raw12741step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12741step1 = (fun i j => raw12741step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12741step1 raw12741step0; decide +kernel
      have hl : raw12741step1Labels = raw12741step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12741step0 raw12741step0Labels permutation56 hz
    mixedMoment B raw12741step1 raw12741step1Labels = mixedMoment B raw12741step2 raw12741step2Labels := by
      have ha : raw12741step2 = (fun i j => raw12741step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12741step2 raw12741step1; decide +kernel
      have hl : raw12741step2Labels = raw12741step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12741step1 raw12741step1Labels permutation11 permutation7
    mixedMoment B raw12741step2 raw12741step2Labels = mixedMoment B raw12741step3 raw12741step3Labels := by
      have ha : raw12741step3 = -raw12741step2 := by apply Matrix.ext; change ∀ i j, raw12741step3 i j = -(raw12741step2 i j); unfold raw12741step3 raw12741step2; decide +kernel
      have hl : raw12741step3Labels = raw12741step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12741step3 raw12741step3Labels = mixedMoment B raw12741step4 raw12741step4Labels := by
      have ha : raw12741step4 = raw12741step3 := by apply Matrix.ext; unfold raw12741step4 raw12741step3; decide +kernel
      have hl : raw12741step3Labels = labelEmbedding1 ∘ raw12741step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12741step3 raw12741step3Labels raw12741step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3583 node3583Labels := by rfl

def raw12742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12742step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12742step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12742step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12742step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12742 raw12742Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw12742 raw12742Labels = mixedMoment B raw12742step0 raw12742step0Labels := by
      have hz : ∀ j, raw12742 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12742step0 = (fun i j => raw12742 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12742step0 raw12742; decide +kernel
      have hl : raw12742step0Labels = raw12742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12742 raw12742Labels permutation265 hz
    mixedMoment B raw12742step0 raw12742step0Labels = mixedMoment B raw12742step1 raw12742step1Labels := by
      have ha : raw12742step1 = (fun i j => raw12742step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12742step1 raw12742step0; decide +kernel
      have hl : raw12742step1Labels = raw12742step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12742step0 raw12742step0Labels permutation41 permutation7
    mixedMoment B raw12742step1 raw12742step1Labels = mixedMoment B raw12742step2 raw12742step2Labels := by
      have ha : raw12742step2 = -raw12742step1 := by apply Matrix.ext; change ∀ i j, raw12742step2 i j = -(raw12742step1 i j); unfold raw12742step2 raw12742step1; decide +kernel
      have hl : raw12742step2Labels = raw12742step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12742step2 raw12742step2Labels = mixedMoment B raw12742step3 raw12742step3Labels := by
      have ha : raw12742step3 = raw12742step2 := by apply Matrix.ext; unfold raw12742step3 raw12742step2; decide +kernel
      have hl : raw12742step2Labels = labelEmbedding1 ∘ raw12742step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12742step2 raw12742step2Labels raw12742step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw12743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12743step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw12743step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw12743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12743 raw12743Labels = mixedMoment B node2466 node2466Labels := by
  calc
    mixedMoment B raw12743 raw12743Labels = mixedMoment B raw12743step0 raw12743step0Labels := by
      have hz : ∀ j, raw12743 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12743step0 = (fun i j => raw12743 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12743step0 raw12743; decide +kernel
      have hl : raw12743step0Labels = raw12743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12743 raw12743Labels permutation265 hz
    mixedMoment B raw12743step0 raw12743step0Labels = mixedMoment B raw12743step1 raw12743step1Labels := by
      have ha : raw12743step1 = (fun i j => raw12743step0 (permutation97 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12743step1 raw12743step0; decide +kernel
      have hl : raw12743step1Labels = raw12743step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12743step0 raw12743step0Labels permutation97 permutation5
    mixedMoment B raw12743step1 raw12743step1Labels = mixedMoment B raw12743step2 raw12743step2Labels := by
      have ha : raw12743step2 = raw12743step1 := by apply Matrix.ext; unfold raw12743step2 raw12743step1; decide +kernel
      have hl : raw12743step1Labels = labelEmbedding1 ∘ raw12743step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12743step1 raw12743step1Labels raw12743step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2466 node2466Labels := by rfl

def raw12744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12744step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw12744step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12744step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw12744step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12744 raw12744Labels = mixedMoment B node2463 node2463Labels := by
  calc
    mixedMoment B raw12744 raw12744Labels = mixedMoment B raw12744step0 raw12744step0Labels := by
      have ha : raw12744step0 = (fun i j => raw12744 (permutation501 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12744step0 raw12744; decide +kernel
      have hl : raw12744step0Labels = raw12744Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12744 raw12744Labels permutation501 permutation5
    mixedMoment B raw12744step0 raw12744step0Labels = mixedMoment B raw12744step1 raw12744step1Labels := by
      have ha : raw12744step1 = raw12744step0 := by apply Matrix.ext; unfold raw12744step1 raw12744step0; decide +kernel
      have hl : raw12744step0Labels = labelEmbedding1 ∘ raw12744step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12744step0 raw12744step0Labels raw12744step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2463 node2463Labels := by rfl

def raw12745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12745step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw12745step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw12745step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12745 raw12745Labels = mixedMoment B node2465 node2465Labels := by
  calc
    mixedMoment B raw12745 raw12745Labels = mixedMoment B raw12745step0 raw12745step0Labels := by
      have hz : ∀ j, raw12745 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12745step0 = (fun i j => raw12745 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12745step0 raw12745; decide +kernel
      have hl : raw12745step0Labels = raw12745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12745 raw12745Labels permutation265 hz
    mixedMoment B raw12745step0 raw12745step0Labels = mixedMoment B raw12745step1 raw12745step1Labels := by
      have ha : raw12745step1 = (fun i j => raw12745step0 (permutation96 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12745step1 raw12745step0; decide +kernel
      have hl : raw12745step1Labels = raw12745step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12745step0 raw12745step0Labels permutation96 permutation5
    mixedMoment B raw12745step1 raw12745step1Labels = mixedMoment B raw12745step2 raw12745step2Labels := by
      have ha : raw12745step2 = raw12745step1 := by apply Matrix.ext; unfold raw12745step2 raw12745step1; decide +kernel
      have hl : raw12745step1Labels = labelEmbedding1 ∘ raw12745step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12745step1 raw12745step1Labels raw12745step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2465 node2465Labels := by rfl

def raw12746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![0, 0, 0], ![1, 0, -1]]
def raw12746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw12746step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12746step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -3, 1], ![1, 0, -1]]
def raw12746step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12746step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw12746step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12746step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw12746step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12746 raw12746Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw12746 raw12746Labels = mixedMoment B raw12746step0 raw12746step0Labels := by
      have hz : ∀ j, raw12746 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12746step0 = (fun i j => raw12746 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12746step0 raw12746; decide +kernel
      have hl : raw12746step0Labels = raw12746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12746 raw12746Labels permutation520 hz
    mixedMoment B raw12746step0 raw12746step0Labels = mixedMoment B raw12746step1 raw12746step1Labels := by
      have hz : ∀ j, raw12746step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12746step1 = (fun i j => raw12746step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12746step1 raw12746step0; decide +kernel
      have hl : raw12746step1Labels = raw12746step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12746step0 raw12746step0Labels permutation56 hz
    mixedMoment B raw12746step1 raw12746step1Labels = mixedMoment B raw12746step2 raw12746step2Labels := by
      have ha : raw12746step2 = (fun i j => raw12746step1 (permutation24 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12746step2 raw12746step1; decide +kernel
      have hl : raw12746step2Labels = raw12746step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12746step1 raw12746step1Labels permutation24 permutation5
    mixedMoment B raw12746step2 raw12746step2Labels = mixedMoment B raw12746step3 raw12746step3Labels := by
      have ha : raw12746step3 = raw12746step2 := by apply Matrix.ext; unfold raw12746step3 raw12746step2; decide +kernel
      have hl : raw12746step2Labels = labelEmbedding1 ∘ raw12746step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12746step2 raw12746step2Labels raw12746step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw12747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1]]
def raw12747step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw12747step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw12747step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12747 raw12747Labels = mixedMoment B node2513 node2513Labels := by
  calc
    mixedMoment B raw12747 raw12747Labels = mixedMoment B raw12747step0 raw12747step0Labels := by
      have hz : ∀ j, raw12747 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12747step0 = (fun i j => raw12747 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12747step0 raw12747; decide +kernel
      have hl : raw12747step0Labels = raw12747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12747 raw12747Labels permutation265 hz
    mixedMoment B raw12747step0 raw12747step0Labels = mixedMoment B raw12747step1 raw12747step1Labels := by
      have ha : raw12747step1 = (fun i j => raw12747step0 (permutation96 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12747step1 raw12747step0; decide +kernel
      have hl : raw12747step1Labels = raw12747step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12747step0 raw12747step0Labels permutation96 permutation5
    mixedMoment B raw12747step1 raw12747step1Labels = mixedMoment B raw12747step2 raw12747step2Labels := by
      have ha : raw12747step2 = raw12747step1 := by apply Matrix.ext; unfold raw12747step2 raw12747step1; decide +kernel
      have hl : raw12747step1Labels = labelEmbedding1 ∘ raw12747step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12747step1 raw12747step1Labels raw12747step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2513 node2513Labels := by rfl

def raw12748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12748Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12748step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw12748step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12748step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw12748step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12748step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw12748step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12748 raw12748Labels = mixedMoment B node3240 node3240Labels := by
  calc
    mixedMoment B raw12748 raw12748Labels = mixedMoment B raw12748step0 raw12748step0Labels := by
      have hz : ∀ j, raw12748 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12748step0 = (fun i j => raw12748 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12748step0 raw12748; decide +kernel
      have hl : raw12748step0Labels = raw12748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12748 raw12748Labels permutation265 hz
    mixedMoment B raw12748step0 raw12748step0Labels = mixedMoment B raw12748step1 raw12748step1Labels := by
      have ha : raw12748step1 = (fun i j => raw12748step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12748step1 raw12748step0; decide +kernel
      have hl : raw12748step1Labels = raw12748step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12748step0 raw12748step0Labels permutation36 permutation5
    mixedMoment B raw12748step1 raw12748step1Labels = mixedMoment B raw12748step2 raw12748step2Labels := by
      have ha : raw12748step2 = -raw12748step1 := by apply Matrix.ext; change ∀ i j, raw12748step2 i j = -(raw12748step1 i j); unfold raw12748step2 raw12748step1; decide +kernel
      have hl : raw12748step2Labels = raw12748step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12748step2 raw12748step2Labels = mixedMoment B raw12748step3 raw12748step3Labels := by
      have ha : raw12748step3 = raw12748step2 := by apply Matrix.ext; unfold raw12748step3 raw12748step2; decide +kernel
      have hl : raw12748step2Labels = labelEmbedding1 ∘ raw12748step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12748step2 raw12748step2Labels raw12748step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3240 node3240Labels := by rfl

def raw12749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12749Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw12749step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12749step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12749step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12749step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12749step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12749 raw12749Labels = mixedMoment B node3561 node3561Labels := by
  calc
    mixedMoment B raw12749 raw12749Labels = mixedMoment B raw12749step0 raw12749step0Labels := by
      have ha : raw12749step0 = (fun i j => raw12749 (permutation203 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12749step0 raw12749; decide +kernel
      have hl : raw12749step0Labels = raw12749Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12749 raw12749Labels permutation203 permutation7
    mixedMoment B raw12749step0 raw12749step0Labels = mixedMoment B raw12749step1 raw12749step1Labels := by
      have ha : raw12749step1 = -raw12749step0 := by apply Matrix.ext; change ∀ i j, raw12749step1 i j = -(raw12749step0 i j); unfold raw12749step1 raw12749step0; decide +kernel
      have hl : raw12749step1Labels = raw12749step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12749step1 raw12749step1Labels = mixedMoment B raw12749step2 raw12749step2Labels := by
      have ha : raw12749step2 = raw12749step1 := by apply Matrix.ext; unfold raw12749step2 raw12749step1; decide +kernel
      have hl : raw12749step1Labels = labelEmbedding1 ∘ raw12749step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12749step1 raw12749step1Labels raw12749step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3561 node3561Labels := by rfl

def raw12750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12750Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12750step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12750step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw12750step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12750step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw12750step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12750step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw12750step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12750 raw12750Labels = mixedMoment B node2835 node2835Labels := by
  calc
    mixedMoment B raw12750 raw12750Labels = mixedMoment B raw12750step0 raw12750step0Labels := by
      have hz : ∀ j, raw12750 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12750step0 = (fun i j => raw12750 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12750step0 raw12750; decide +kernel
      have hl : raw12750step0Labels = raw12750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12750 raw12750Labels permutation265 hz
    mixedMoment B raw12750step0 raw12750step0Labels = mixedMoment B raw12750step1 raw12750step1Labels := by
      have ha : raw12750step1 = (fun i j => raw12750step0 (permutation60 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12750step1 raw12750step0; decide +kernel
      have hl : raw12750step1Labels = raw12750step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12750step0 raw12750step0Labels permutation60 permutation5
    mixedMoment B raw12750step1 raw12750step1Labels = mixedMoment B raw12750step2 raw12750step2Labels := by
      have ha : raw12750step2 = -raw12750step1 := by apply Matrix.ext; change ∀ i j, raw12750step2 i j = -(raw12750step1 i j); unfold raw12750step2 raw12750step1; decide +kernel
      have hl : raw12750step2Labels = raw12750step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12750step2 raw12750step2Labels = mixedMoment B raw12750step3 raw12750step3Labels := by
      have ha : raw12750step3 = raw12750step2 := by apply Matrix.ext; unfold raw12750step3 raw12750step2; decide +kernel
      have hl : raw12750step2Labels = labelEmbedding1 ∘ raw12750step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12750step2 raw12750step2Labels raw12750step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2835 node2835Labels := by rfl

def raw12751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12751Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12751step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw12751step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12751step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12751step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12751step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12751 raw12751Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw12751 raw12751Labels = mixedMoment B raw12751step0 raw12751step0Labels := by
      have hz : ∀ j, raw12751 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12751step0 = (fun i j => raw12751 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12751step0 raw12751; decide +kernel
      have hl : raw12751step0Labels = raw12751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12751 raw12751Labels permutation265 hz
    mixedMoment B raw12751step0 raw12751step0Labels = mixedMoment B raw12751step1 raw12751step1Labels := by
      have ha : raw12751step1 = (fun i j => raw12751step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12751step1 raw12751step0; decide +kernel
      have hl : raw12751step1Labels = raw12751step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12751step0 raw12751step0Labels permutation41 permutation7
    mixedMoment B raw12751step1 raw12751step1Labels = mixedMoment B raw12751step2 raw12751step2Labels := by
      have ha : raw12751step2 = -raw12751step1 := by apply Matrix.ext; change ∀ i j, raw12751step2 i j = -(raw12751step1 i j); unfold raw12751step2 raw12751step1; decide +kernel
      have hl : raw12751step2Labels = raw12751step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12751step2 raw12751step2Labels = mixedMoment B raw12751step3 raw12751step3Labels := by
      have ha : raw12751step3 = raw12751step2 := by apply Matrix.ext; unfold raw12751step3 raw12751step2; decide +kernel
      have hl : raw12751step2Labels = labelEmbedding1 ∘ raw12751step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12751step2 raw12751step2Labels raw12751step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw12752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1]]
def raw12752Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1]]
def raw12752step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw12752step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12752step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12752step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12752step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12752 raw12752Labels = mixedMoment B node3577 node3577Labels := by
  calc
    mixedMoment B raw12752 raw12752Labels = mixedMoment B raw12752step0 raw12752step0Labels := by
      have hz : ∀ j, raw12752 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12752step0 = (fun i j => raw12752 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12752step0 raw12752; decide +kernel
      have hl : raw12752step0Labels = raw12752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12752 raw12752Labels permutation265 hz
    mixedMoment B raw12752step0 raw12752step0Labels = mixedMoment B raw12752step1 raw12752step1Labels := by
      have ha : raw12752step1 = (fun i j => raw12752step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12752step1 raw12752step0; decide +kernel
      have hl : raw12752step1Labels = raw12752step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12752step0 raw12752step0Labels permutation41 permutation7
    mixedMoment B raw12752step1 raw12752step1Labels = mixedMoment B raw12752step2 raw12752step2Labels := by
      have ha : raw12752step2 = -raw12752step1 := by apply Matrix.ext; change ∀ i j, raw12752step2 i j = -(raw12752step1 i j); unfold raw12752step2 raw12752step1; decide +kernel
      have hl : raw12752step2Labels = raw12752step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12752step2 raw12752step2Labels = mixedMoment B raw12752step3 raw12752step3Labels := by
      have ha : raw12752step3 = raw12752step2 := by apply Matrix.ext; unfold raw12752step3 raw12752step2; decide +kernel
      have hl : raw12752step2Labels = labelEmbedding1 ∘ raw12752step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12752step2 raw12752step2Labels raw12752step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3577 node3577Labels := by rfl

def raw12753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12753Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12753step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw12753step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12753step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw12753step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12753step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw12753step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12753 raw12753Labels = mixedMoment B node3246 node3246Labels := by
  calc
    mixedMoment B raw12753 raw12753Labels = mixedMoment B raw12753step0 raw12753step0Labels := by
      have hz : ∀ j, raw12753 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12753step0 = (fun i j => raw12753 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12753step0 raw12753; decide +kernel
      have hl : raw12753step0Labels = raw12753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12753 raw12753Labels permutation265 hz
    mixedMoment B raw12753step0 raw12753step0Labels = mixedMoment B raw12753step1 raw12753step1Labels := by
      have ha : raw12753step1 = (fun i j => raw12753step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12753step1 raw12753step0; decide +kernel
      have hl : raw12753step1Labels = raw12753step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12753step0 raw12753step0Labels permutation35 permutation5
    mixedMoment B raw12753step1 raw12753step1Labels = mixedMoment B raw12753step2 raw12753step2Labels := by
      have ha : raw12753step2 = -raw12753step1 := by apply Matrix.ext; change ∀ i j, raw12753step2 i j = -(raw12753step1 i j); unfold raw12753step2 raw12753step1; decide +kernel
      have hl : raw12753step2Labels = raw12753step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12753step2 raw12753step2Labels = mixedMoment B raw12753step3 raw12753step3Labels := by
      have ha : raw12753step3 = raw12753step2 := by apply Matrix.ext; unfold raw12753step3 raw12753step2; decide +kernel
      have hl : raw12753step2Labels = labelEmbedding1 ∘ raw12753step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12753step2 raw12753step2Labels raw12753step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3246 node3246Labels := by rfl

def raw12754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12754Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw12754step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12754step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12754step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12754step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12754step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12754 raw12754Labels = mixedMoment B node3559 node3559Labels := by
  calc
    mixedMoment B raw12754 raw12754Labels = mixedMoment B raw12754step0 raw12754step0Labels := by
      have ha : raw12754step0 = (fun i j => raw12754 (permutation203 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12754step0 raw12754; decide +kernel
      have hl : raw12754step0Labels = raw12754Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12754 raw12754Labels permutation203 permutation7
    mixedMoment B raw12754step0 raw12754step0Labels = mixedMoment B raw12754step1 raw12754step1Labels := by
      have ha : raw12754step1 = -raw12754step0 := by apply Matrix.ext; change ∀ i j, raw12754step1 i j = -(raw12754step0 i j); unfold raw12754step1 raw12754step0; decide +kernel
      have hl : raw12754step1Labels = raw12754step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12754step1 raw12754step1Labels = mixedMoment B raw12754step2 raw12754step2Labels := by
      have ha : raw12754step2 = raw12754step1 := by apply Matrix.ext; unfold raw12754step2 raw12754step1; decide +kernel
      have hl : raw12754step1Labels = labelEmbedding1 ∘ raw12754step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12754step1 raw12754step1Labels raw12754step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3559 node3559Labels := by rfl

def raw12755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12755Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12755step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw12755step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12755step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw12755step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12755step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw12755step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12755 raw12755Labels = mixedMoment B node2841 node2841Labels := by
  calc
    mixedMoment B raw12755 raw12755Labels = mixedMoment B raw12755step0 raw12755step0Labels := by
      have hz : ∀ j, raw12755 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12755step0 = (fun i j => raw12755 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12755step0 raw12755; decide +kernel
      have hl : raw12755step0Labels = raw12755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12755 raw12755Labels permutation265 hz
    mixedMoment B raw12755step0 raw12755step0Labels = mixedMoment B raw12755step1 raw12755step1Labels := by
      have ha : raw12755step1 = (fun i j => raw12755step0 (permutation59 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12755step1 raw12755step0; decide +kernel
      have hl : raw12755step1Labels = raw12755step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12755step0 raw12755step0Labels permutation59 permutation5
    mixedMoment B raw12755step1 raw12755step1Labels = mixedMoment B raw12755step2 raw12755step2Labels := by
      have ha : raw12755step2 = -raw12755step1 := by apply Matrix.ext; change ∀ i j, raw12755step2 i j = -(raw12755step1 i j); unfold raw12755step2 raw12755step1; decide +kernel
      have hl : raw12755step2Labels = raw12755step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12755step2 raw12755step2Labels = mixedMoment B raw12755step3 raw12755step3Labels := by
      have ha : raw12755step3 = raw12755step2 := by apply Matrix.ext; unfold raw12755step3 raw12755step2; decide +kernel
      have hl : raw12755step2Labels = labelEmbedding1 ∘ raw12755step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12755step2 raw12755step2Labels raw12755step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2841 node2841Labels := by rfl

def raw12756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12756Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12756step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw12756step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12756step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12756step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12756step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12756 raw12756Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw12756 raw12756Labels = mixedMoment B raw12756step0 raw12756step0Labels := by
      have hz : ∀ j, raw12756 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12756step0 = (fun i j => raw12756 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12756step0 raw12756; decide +kernel
      have hl : raw12756step0Labels = raw12756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12756 raw12756Labels permutation265 hz
    mixedMoment B raw12756step0 raw12756step0Labels = mixedMoment B raw12756step1 raw12756step1Labels := by
      have ha : raw12756step1 = (fun i j => raw12756step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12756step1 raw12756step0; decide +kernel
      have hl : raw12756step1Labels = raw12756step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12756step0 raw12756step0Labels permutation41 permutation7
    mixedMoment B raw12756step1 raw12756step1Labels = mixedMoment B raw12756step2 raw12756step2Labels := by
      have ha : raw12756step2 = -raw12756step1 := by apply Matrix.ext; change ∀ i j, raw12756step2 i j = -(raw12756step1 i j); unfold raw12756step2 raw12756step1; decide +kernel
      have hl : raw12756step2Labels = raw12756step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12756step2 raw12756step2Labels = mixedMoment B raw12756step3 raw12756step3Labels := by
      have ha : raw12756step3 = raw12756step2 := by apply Matrix.ext; unfold raw12756step3 raw12756step2; decide +kernel
      have hl : raw12756step2Labels = labelEmbedding1 ∘ raw12756step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12756step2 raw12756step2Labels raw12756step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw12757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1]]
def raw12757Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw12757step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12757step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw12757step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12757step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw12757step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12757step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12757step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12757step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12757step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12757 raw12757Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw12757 raw12757Labels = mixedMoment B raw12757step0 raw12757step0Labels := by
      have hz : ∀ j, raw12757 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12757step0 = (fun i j => raw12757 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12757step0 raw12757; decide +kernel
      have hl : raw12757step0Labels = raw12757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12757 raw12757Labels permutation520 hz
    mixedMoment B raw12757step0 raw12757step0Labels = mixedMoment B raw12757step1 raw12757step1Labels := by
      have hz : ∀ j, raw12757step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12757step1 = (fun i j => raw12757step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12757step1 raw12757step0; decide +kernel
      have hl : raw12757step1Labels = raw12757step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12757step0 raw12757step0Labels permutation56 hz
    mixedMoment B raw12757step1 raw12757step1Labels = mixedMoment B raw12757step2 raw12757step2Labels := by
      have ha : raw12757step2 = (fun i j => raw12757step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12757step2 raw12757step1; decide +kernel
      have hl : raw12757step2Labels = raw12757step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12757step1 raw12757step1Labels permutation11 permutation7
    mixedMoment B raw12757step2 raw12757step2Labels = mixedMoment B raw12757step3 raw12757step3Labels := by
      have ha : raw12757step3 = -raw12757step2 := by apply Matrix.ext; change ∀ i j, raw12757step3 i j = -(raw12757step2 i j); unfold raw12757step3 raw12757step2; decide +kernel
      have hl : raw12757step3Labels = raw12757step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12757step3 raw12757step3Labels = mixedMoment B raw12757step4 raw12757step4Labels := by
      have ha : raw12757step4 = raw12757step3 := by apply Matrix.ext; unfold raw12757step4 raw12757step3; decide +kernel
      have hl : raw12757step3Labels = labelEmbedding1 ∘ raw12757step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12757step3 raw12757step3Labels raw12757step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3584 node3584Labels := by rfl

def raw12758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12758 raw12758Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw12758 raw12758Labels = mixedMoment B raw12758step0 raw12758step0Labels := by
      have hz : ∀ j, raw12758 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12758step0 = (fun i j => raw12758 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12758step0 raw12758; decide +kernel
      have hl : raw12758step0Labels = raw12758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12758 raw12758Labels permutation265 hz
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw12759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12759 raw12759Labels = mixedMoment B node1276 node1276Labels := by
  calc
    mixedMoment B raw12759 raw12759Labels = mixedMoment B raw12759step0 raw12759step0Labels := by
      have ha : raw12759step0 = (fun i j => raw12759 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12759step0 raw12759; decide +kernel
      have hl : raw12759step0Labels = raw12759Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12759 raw12759Labels permutation182 permutation2
    _ = mixedMoment B node1276 node1276Labels := by rfl

def raw12760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12760step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12760step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12760 raw12760Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw12760 raw12760Labels = mixedMoment B raw12760step0 raw12760step0Labels := by
      have hz : ∀ j, raw12760 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12760step0 = (fun i j => raw12760 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12760step0 raw12760; decide +kernel
      have hl : raw12760step0Labels = raw12760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12760 raw12760Labels permutation265 hz
    mixedMoment B raw12760step0 raw12760step0Labels = mixedMoment B raw12760step1 raw12760step1Labels := by
      have ha : raw12760step1 = (fun i j => raw12760step0 (permutation41 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12760step1 raw12760step0; decide +kernel
      have hl : raw12760step1Labels = raw12760step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12760step0 raw12760step0Labels permutation41 permutation2
    _ = mixedMoment B node1291 node1291Labels := by rfl

def raw12761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12761step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw12761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12761 raw12761Labels = mixedMoment B node1280 node1280Labels := by
  calc
    mixedMoment B raw12761 raw12761Labels = mixedMoment B raw12761step0 raw12761step0Labels := by
      have hz : ∀ j, raw12761 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12761step0 = (fun i j => raw12761 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12761step0 raw12761; decide +kernel
      have hl : raw12761step0Labels = raw12761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12761 raw12761Labels permutation265 hz
    mixedMoment B raw12761step0 raw12761step0Labels = mixedMoment B raw12761step1 raw12761step1Labels := by
      have ha : raw12761step1 = (fun i j => raw12761step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12761step1 raw12761step0; decide +kernel
      have hl : raw12761step1Labels = raw12761step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12761step0 raw12761step0Labels permutation35 permutation2
    _ = mixedMoment B node1280 node1280Labels := by rfl

def raw12762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw12762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw12762step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12762 raw12762Labels = mixedMoment B node1278 node1278Labels := by
  calc
    mixedMoment B raw12762 raw12762Labels = mixedMoment B raw12762step0 raw12762step0Labels := by
      have hz : ∀ j, raw12762 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12762step0 = (fun i j => raw12762 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12762step0 raw12762; decide +kernel
      have hl : raw12762step0Labels = raw12762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12762 raw12762Labels permutation265 hz
    mixedMoment B raw12762step0 raw12762step0Labels = mixedMoment B raw12762step1 raw12762step1Labels := by
      have ha : raw12762step1 = (fun i j => raw12762step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12762step1 raw12762step0; decide +kernel
      have hl : raw12762step1Labels = raw12762step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12762step0 raw12762step0Labels permutation33 permutation2
    _ = mixedMoment B node1278 node1278Labels := by rfl

def raw12763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw12763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12763 raw12763Labels = mixedMoment B node1277 node1277Labels := by
  calc
    mixedMoment B raw12763 raw12763Labels = mixedMoment B raw12763step0 raw12763step0Labels := by
      have hz : ∀ j, raw12763 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12763step0 = (fun i j => raw12763 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12763step0 raw12763; decide +kernel
      have hl : raw12763step0Labels = raw12763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12763 raw12763Labels permutation265 hz
    _ = mixedMoment B node1277 node1277Labels := by rfl

def raw12764 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2], ![-1, 1], ![0, 0], ![1, -1]]
def raw12764Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12764step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![2, -2], ![-1, 1], ![1, -1]]
def raw12764step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12764step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![2, -2], ![-1, 1], ![1, -1]]
def raw12764step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12764step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw12764step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical12764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12764 raw12764Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw12764 raw12764Labels = mixedMoment B raw12764step0 raw12764step0Labels := by
      have hz : ∀ j, raw12764 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12764step0 = (fun i j => raw12764 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12764step0 raw12764; decide +kernel
      have hl : raw12764step0Labels = raw12764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12764 raw12764Labels permutation520 hz
    mixedMoment B raw12764step0 raw12764step0Labels = mixedMoment B raw12764step1 raw12764step1Labels := by
      have hz : ∀ j, raw12764step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12764step1 = (fun i j => raw12764step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12764step1 raw12764step0; decide +kernel
      have hl : raw12764step1Labels = raw12764step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12764step0 raw12764step0Labels permutation56 hz
    mixedMoment B raw12764step1 raw12764step1Labels = mixedMoment B raw12764step2 raw12764step2Labels := by
      have ha : raw12764step2 = (fun i j => raw12764step1 (permutation11 i) (permutation0 j)) := by apply Matrix.ext; unfold raw12764step2 raw12764step1; decide +kernel
      have hl : raw12764step2Labels = raw12764step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12764step1 raw12764step1Labels permutation11 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw12765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12765step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12765step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12765step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12765 raw12765Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw12765 raw12765Labels = mixedMoment B raw12765step0 raw12765step0Labels := by
      have ha : raw12765step0 = (fun i j => raw12765 (permutation428 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12765step0 raw12765; decide +kernel
      have hl : raw12765step0Labels = raw12765Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12765 raw12765Labels permutation428 permutation4
    mixedMoment B raw12765step0 raw12765step0Labels = mixedMoment B raw12765step1 raw12765step1Labels := by
      have ha : raw12765step1 = raw12765step0 := by apply Matrix.ext; unfold raw12765step1 raw12765step0; decide +kernel
      have hl : raw12765step0Labels = labelEmbedding7 ∘ raw12765step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12765step0 raw12765step0Labels raw12765step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw12766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12766step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12766step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12766step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12766step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12766 raw12766Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw12766 raw12766Labels = mixedMoment B raw12766step0 raw12766step0Labels := by
      have hz : ∀ j, raw12766 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12766step0 = (fun i j => raw12766 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12766step0 raw12766; decide +kernel
      have hl : raw12766step0Labels = raw12766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12766 raw12766Labels permutation265 hz
    mixedMoment B raw12766step0 raw12766step0Labels = mixedMoment B raw12766step1 raw12766step1Labels := by
      have ha : raw12766step1 = (fun i j => raw12766step0 (permutation61 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12766step1 raw12766step0; decide +kernel
      have hl : raw12766step1Labels = raw12766step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12766step0 raw12766step0Labels permutation61 permutation7
    mixedMoment B raw12766step1 raw12766step1Labels = mixedMoment B raw12766step2 raw12766step2Labels := by
      have ha : raw12766step2 = -raw12766step1 := by apply Matrix.ext; change ∀ i j, raw12766step2 i j = -(raw12766step1 i j); unfold raw12766step2 raw12766step1; decide +kernel
      have hl : raw12766step2Labels = raw12766step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12766step2 raw12766step2Labels = mixedMoment B raw12766step3 raw12766step3Labels := by
      have ha : raw12766step3 = raw12766step2 := by apply Matrix.ext; unfold raw12766step3 raw12766step2; decide +kernel
      have hl : raw12766step2Labels = labelEmbedding10 ∘ raw12766step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12766step2 raw12766step2Labels raw12766step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw12767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12767step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12767step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12767 raw12767Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw12767 raw12767Labels = mixedMoment B raw12767step0 raw12767step0Labels := by
      have hz : ∀ j, raw12767 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12767step0 = (fun i j => raw12767 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12767step0 raw12767; decide +kernel
      have hl : raw12767step0Labels = raw12767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12767 raw12767Labels permutation265 hz
    mixedMoment B raw12767step0 raw12767step0Labels = mixedMoment B raw12767step1 raw12767step1Labels := by
      have ha : raw12767step1 = (fun i j => raw12767step0 (permutation78 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12767step1 raw12767step0; decide +kernel
      have hl : raw12767step1Labels = raw12767step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12767step0 raw12767step0Labels permutation78 permutation4
    mixedMoment B raw12767step1 raw12767step1Labels = mixedMoment B raw12767step2 raw12767step2Labels := by
      have ha : raw12767step2 = raw12767step1 := by apply Matrix.ext; unfold raw12767step2 raw12767step1; decide +kernel
      have hl : raw12767step1Labels = labelEmbedding7 ∘ raw12767step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12767step1 raw12767step1Labels raw12767step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw12768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12768step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12768step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12768 raw12768Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw12768 raw12768Labels = mixedMoment B raw12768step0 raw12768step0Labels := by
      have hz : ∀ j, raw12768 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12768step0 = (fun i j => raw12768 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12768step0 raw12768; decide +kernel
      have hl : raw12768step0Labels = raw12768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12768 raw12768Labels permutation265 hz
    mixedMoment B raw12768step0 raw12768step0Labels = mixedMoment B raw12768step1 raw12768step1Labels := by
      have ha : raw12768step1 = (fun i j => raw12768step0 (permutation75 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12768step1 raw12768step0; decide +kernel
      have hl : raw12768step1Labels = raw12768step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12768step0 raw12768step0Labels permutation75 permutation4
    mixedMoment B raw12768step1 raw12768step1Labels = mixedMoment B raw12768step2 raw12768step2Labels := by
      have ha : raw12768step2 = raw12768step1 := by apply Matrix.ext; unfold raw12768step2 raw12768step1; decide +kernel
      have hl : raw12768step1Labels = labelEmbedding7 ∘ raw12768step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12768step1 raw12768step1Labels raw12768step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw12769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12769step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12769step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12769step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12769step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12769step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12769step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12769step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12769step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12769 raw12769Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw12769 raw12769Labels = mixedMoment B raw12769step0 raw12769step0Labels := by
      have hz : ∀ j, raw12769 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12769step0 = (fun i j => raw12769 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12769step0 raw12769; decide +kernel
      have hl : raw12769step0Labels = raw12769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12769 raw12769Labels permutation590 hz
    mixedMoment B raw12769step0 raw12769step0Labels = mixedMoment B raw12769step1 raw12769step1Labels := by
      have hz : ∀ j, raw12769step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12769step1 = (fun i j => raw12769step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12769step1 raw12769step0; decide +kernel
      have hl : raw12769step1Labels = raw12769step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12769step0 raw12769step0Labels permutation56 hz
    mixedMoment B raw12769step1 raw12769step1Labels = mixedMoment B raw12769step2 raw12769step2Labels := by
      have ha : raw12769step2 = (fun i j => raw12769step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12769step2 raw12769step1; decide +kernel
      have hl : raw12769step2Labels = raw12769step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12769step1 raw12769step1Labels permutation15 permutation6
    mixedMoment B raw12769step2 raw12769step2Labels = mixedMoment B raw12769step3 raw12769step3Labels := by
      have ha : raw12769step3 = -raw12769step2 := by apply Matrix.ext; change ∀ i j, raw12769step3 i j = -(raw12769step2 i j); unfold raw12769step3 raw12769step2; decide +kernel
      have hl : raw12769step3Labels = raw12769step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12769step3 raw12769step3Labels = mixedMoment B raw12769step4 raw12769step4Labels := by
      have ha : raw12769step4 = raw12769step3 := by apply Matrix.ext; unfold raw12769step4 raw12769step3; decide +kernel
      have hl : raw12769step3Labels = labelEmbedding9 ∘ raw12769step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12769step3 raw12769step3Labels raw12769step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw12770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12770step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12770step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12770 raw12770Labels = mixedMoment B node4469 node4469Labels := by
  calc
    mixedMoment B raw12770 raw12770Labels = mixedMoment B raw12770step0 raw12770step0Labels := by
      have ha : raw12770step0 = (fun i j => raw12770 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12770step0 raw12770; decide +kernel
      have hl : raw12770step0Labels = raw12770Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12770 raw12770Labels permutation184 permutation3
    mixedMoment B raw12770step0 raw12770step0Labels = mixedMoment B raw12770step1 raw12770step1Labels := by
      have ha : raw12770step1 = raw12770step0 := by apply Matrix.ext; unfold raw12770step1 raw12770step0; decide +kernel
      have hl : raw12770step0Labels = labelEmbedding6 ∘ raw12770step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12770step0 raw12770step0Labels raw12770step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4469 node4469Labels := by rfl

def raw12771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12771step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12771step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12771step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12771 raw12771Labels = mixedMoment B node5197 node5197Labels := by
  calc
    mixedMoment B raw12771 raw12771Labels = mixedMoment B raw12771step0 raw12771step0Labels := by
      have ha : raw12771step0 = (fun i j => raw12771 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12771step0 raw12771; decide +kernel
      have hl : raw12771step0Labels = raw12771Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12771 raw12771Labels permutation184 permutation3
    mixedMoment B raw12771step0 raw12771step0Labels = mixedMoment B raw12771step1 raw12771step1Labels := by
      have ha : raw12771step1 = raw12771step0 := by apply Matrix.ext; unfold raw12771step1 raw12771step0; decide +kernel
      have hl : raw12771step0Labels = labelEmbedding6 ∘ raw12771step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12771step0 raw12771step0Labels raw12771step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5197 node5197Labels := by rfl

def raw12772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12772step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12772step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12772step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12772 raw12772Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw12772 raw12772Labels = mixedMoment B raw12772step0 raw12772step0Labels := by
      have ha : raw12772step0 = (fun i j => raw12772 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12772step0 raw12772; decide +kernel
      have hl : raw12772step0Labels = raw12772Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12772 raw12772Labels permutation208 permutation3
    mixedMoment B raw12772step0 raw12772step0Labels = mixedMoment B raw12772step1 raw12772step1Labels := by
      have ha : raw12772step1 = raw12772step0 := by apply Matrix.ext; unfold raw12772step1 raw12772step0; decide +kernel
      have hl : raw12772step0Labels = labelEmbedding6 ∘ raw12772step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12772step0 raw12772step0Labels raw12772step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

def raw12773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12773step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12773step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12773step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12773 raw12773Labels = mixedMoment B node5263 node5263Labels := by
  calc
    mixedMoment B raw12773 raw12773Labels = mixedMoment B raw12773step0 raw12773step0Labels := by
      have ha : raw12773step0 = (fun i j => raw12773 (permutation232 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12773step0 raw12773; decide +kernel
      have hl : raw12773step0Labels = raw12773Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12773 raw12773Labels permutation232 permutation3
    mixedMoment B raw12773step0 raw12773step0Labels = mixedMoment B raw12773step1 raw12773step1Labels := by
      have ha : raw12773step1 = raw12773step0 := by apply Matrix.ext; unfold raw12773step1 raw12773step0; decide +kernel
      have hl : raw12773step0Labels = labelEmbedding6 ∘ raw12773step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12773step0 raw12773step0Labels raw12773step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5263 node5263Labels := by rfl

def raw12774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12774step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12774step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12774step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12774 raw12774Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw12774 raw12774Labels = mixedMoment B raw12774step0 raw12774step0Labels := by
      have hz : ∀ j, raw12774 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12774step0 = (fun i j => raw12774 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12774step0 raw12774; decide +kernel
      have hl : raw12774step0Labels = raw12774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12774 raw12774Labels permutation590 hz
    mixedMoment B raw12774step0 raw12774step0Labels = mixedMoment B raw12774step1 raw12774step1Labels := by
      have ha : raw12774step1 = (fun i j => raw12774step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12774step1 raw12774step0; decide +kernel
      have hl : raw12774step1Labels = raw12774step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12774step0 raw12774step0Labels permutation41 permutation3
    mixedMoment B raw12774step1 raw12774step1Labels = mixedMoment B raw12774step2 raw12774step2Labels := by
      have ha : raw12774step2 = raw12774step1 := by apply Matrix.ext; unfold raw12774step2 raw12774step1; decide +kernel
      have hl : raw12774step1Labels = labelEmbedding6 ∘ raw12774step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12774step1 raw12774step1Labels raw12774step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw12775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12775step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw12775step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12775step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw12775step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12775 raw12775Labels = mixedMoment B node4486 node4486Labels := by
  calc
    mixedMoment B raw12775 raw12775Labels = mixedMoment B raw12775step0 raw12775step0Labels := by
      have hz : ∀ j, raw12775 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12775step0 = (fun i j => raw12775 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12775step0 raw12775; decide +kernel
      have hl : raw12775step0Labels = raw12775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12775 raw12775Labels permutation265 hz
    mixedMoment B raw12775step0 raw12775step0Labels = mixedMoment B raw12775step1 raw12775step1Labels := by
      have ha : raw12775step1 = (fun i j => raw12775step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12775step1 raw12775step0; decide +kernel
      have hl : raw12775step1Labels = raw12775step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12775step0 raw12775step0Labels permutation41 permutation3
    mixedMoment B raw12775step1 raw12775step1Labels = mixedMoment B raw12775step2 raw12775step2Labels := by
      have ha : raw12775step2 = raw12775step1 := by apply Matrix.ext; unfold raw12775step2 raw12775step1; decide +kernel
      have hl : raw12775step1Labels = labelEmbedding6 ∘ raw12775step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12775step1 raw12775step1Labels raw12775step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4486 node4486Labels := by rfl

def raw12776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw12776step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12776step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw12776step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12776 raw12776Labels = mixedMoment B node5091 node5091Labels := by
  calc
    mixedMoment B raw12776 raw12776Labels = mixedMoment B raw12776step0 raw12776step0Labels := by
      have ha : raw12776step0 = (fun i j => raw12776 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12776step0 raw12776; decide +kernel
      have hl : raw12776step0Labels = raw12776Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12776 raw12776Labels permutation161 permutation3
    mixedMoment B raw12776step0 raw12776step0Labels = mixedMoment B raw12776step1 raw12776step1Labels := by
      have ha : raw12776step1 = raw12776step0 := by apply Matrix.ext; unfold raw12776step1 raw12776step0; decide +kernel
      have hl : raw12776step0Labels = labelEmbedding6 ∘ raw12776step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12776step0 raw12776step0Labels raw12776step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5091 node5091Labels := by rfl

def raw12777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw12777step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw12777step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12777 raw12777Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw12777 raw12777Labels = mixedMoment B raw12777step0 raw12777step0Labels := by
      have hz : ∀ j, raw12777 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12777step0 = (fun i j => raw12777 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12777step0 raw12777; decide +kernel
      have hl : raw12777step0Labels = raw12777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12777 raw12777Labels permutation265 hz
    mixedMoment B raw12777step0 raw12777step0Labels = mixedMoment B raw12777step1 raw12777step1Labels := by
      have ha : raw12777step1 = (fun i j => raw12777step0 (permutation78 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12777step1 raw12777step0; decide +kernel
      have hl : raw12777step1Labels = raw12777step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12777step0 raw12777step0Labels permutation78 permutation4
    mixedMoment B raw12777step1 raw12777step1Labels = mixedMoment B raw12777step2 raw12777step2Labels := by
      have ha : raw12777step2 = raw12777step1 := by apply Matrix.ext; unfold raw12777step2 raw12777step1; decide +kernel
      have hl : raw12777step1Labels = labelEmbedding7 ∘ raw12777step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12777step1 raw12777step1Labels raw12777step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5151 node5151Labels := by rfl

def raw12778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12778step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12778step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12778step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12778step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12778 raw12778Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw12778 raw12778Labels = mixedMoment B raw12778step0 raw12778step0Labels := by
      have hz : ∀ j, raw12778 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12778step0 = (fun i j => raw12778 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12778step0 raw12778; decide +kernel
      have hl : raw12778step0Labels = raw12778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12778 raw12778Labels permutation265 hz
    mixedMoment B raw12778step0 raw12778step0Labels = mixedMoment B raw12778step1 raw12778step1Labels := by
      have ha : raw12778step1 = (fun i j => raw12778step0 (permutation79 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12778step1 raw12778step0; decide +kernel
      have hl : raw12778step1Labels = raw12778step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12778step0 raw12778step0Labels permutation79 permutation4
    mixedMoment B raw12778step1 raw12778step1Labels = mixedMoment B raw12778step2 raw12778step2Labels := by
      have ha : raw12778step2 = raw12778step1 := by apply Matrix.ext; unfold raw12778step2 raw12778step1; decide +kernel
      have hl : raw12778step1Labels = labelEmbedding7 ∘ raw12778step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12778step1 raw12778step1Labels raw12778step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

def raw12779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12779step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12779step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12779step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12779step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12779step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12779step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12779 raw12779Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw12779 raw12779Labels = mixedMoment B raw12779step0 raw12779step0Labels := by
      have hz : ∀ j, raw12779 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12779step0 = (fun i j => raw12779 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12779step0 raw12779; decide +kernel
      have hl : raw12779step0Labels = raw12779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12779 raw12779Labels permutation590 hz
    mixedMoment B raw12779step0 raw12779step0Labels = mixedMoment B raw12779step1 raw12779step1Labels := by
      have hz : ∀ j, raw12779step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12779step1 = (fun i j => raw12779step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12779step1 raw12779step0; decide +kernel
      have hl : raw12779step1Labels = raw12779step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12779step0 raw12779step0Labels permutation56 hz
    mixedMoment B raw12779step1 raw12779step1Labels = mixedMoment B raw12779step2 raw12779step2Labels := by
      have ha : raw12779step2 = (fun i j => raw12779step1 (permutation19 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12779step2 raw12779step1; decide +kernel
      have hl : raw12779step2Labels = raw12779step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12779step1 raw12779step1Labels permutation19 permutation4
    mixedMoment B raw12779step2 raw12779step2Labels = mixedMoment B raw12779step3 raw12779step3Labels := by
      have ha : raw12779step3 = raw12779step2 := by apply Matrix.ext; unfold raw12779step3 raw12779step2; decide +kernel
      have hl : raw12779step2Labels = labelEmbedding7 ∘ raw12779step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12779step2 raw12779step2Labels raw12779step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw12780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12780step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12780step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12780step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12780 raw12780Labels = mixedMoment B node4475 node4475Labels := by
  calc
    mixedMoment B raw12780 raw12780Labels = mixedMoment B raw12780step0 raw12780step0Labels := by
      have hz : ∀ j, raw12780 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12780step0 = (fun i j => raw12780 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12780step0 raw12780; decide +kernel
      have hl : raw12780step0Labels = raw12780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12780 raw12780Labels permutation265 hz
    mixedMoment B raw12780step0 raw12780step0Labels = mixedMoment B raw12780step1 raw12780step1Labels := by
      have ha : raw12780step1 = (fun i j => raw12780step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12780step1 raw12780step0; decide +kernel
      have hl : raw12780step1Labels = raw12780step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12780step0 raw12780step0Labels permutation35 permutation3
    mixedMoment B raw12780step1 raw12780step1Labels = mixedMoment B raw12780step2 raw12780step2Labels := by
      have ha : raw12780step2 = raw12780step1 := by apply Matrix.ext; unfold raw12780step2 raw12780step1; decide +kernel
      have hl : raw12780step1Labels = labelEmbedding6 ∘ raw12780step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12780step1 raw12780step1Labels raw12780step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4475 node4475Labels := by rfl

def raw12781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12781step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12781step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12781step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12781 raw12781Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw12781 raw12781Labels = mixedMoment B raw12781step0 raw12781step0Labels := by
      have ha : raw12781step0 = (fun i j => raw12781 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12781step0 raw12781; decide +kernel
      have hl : raw12781step0Labels = raw12781Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12781 raw12781Labels permutation155 permutation3
    mixedMoment B raw12781step0 raw12781step0Labels = mixedMoment B raw12781step1 raw12781step1Labels := by
      have ha : raw12781step1 = raw12781step0 := by apply Matrix.ext; unfold raw12781step1 raw12781step0; decide +kernel
      have hl : raw12781step0Labels = labelEmbedding6 ∘ raw12781step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12781step0 raw12781step0Labels raw12781step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5086 node5086Labels := by rfl

def raw12782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12782step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12782step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12782step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw12782step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12782 raw12782Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw12782 raw12782Labels = mixedMoment B raw12782step0 raw12782step0Labels := by
      have hz : ∀ j, raw12782 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12782step0 = (fun i j => raw12782 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12782step0 raw12782; decide +kernel
      have hl : raw12782step0Labels = raw12782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12782 raw12782Labels permutation265 hz
    mixedMoment B raw12782step0 raw12782step0Labels = mixedMoment B raw12782step1 raw12782step1Labels := by
      have ha : raw12782step1 = (fun i j => raw12782step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12782step1 raw12782step0; decide +kernel
      have hl : raw12782step1Labels = raw12782step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12782step0 raw12782step0Labels permutation35 permutation3
    mixedMoment B raw12782step1 raw12782step1Labels = mixedMoment B raw12782step2 raw12782step2Labels := by
      have ha : raw12782step2 = raw12782step1 := by apply Matrix.ext; unfold raw12782step2 raw12782step1; decide +kernel
      have hl : raw12782step1Labels = labelEmbedding6 ∘ raw12782step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12782step1 raw12782step1Labels raw12782step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw12783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12783step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12783step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12783step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12783 raw12783Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw12783 raw12783Labels = mixedMoment B raw12783step0 raw12783step0Labels := by
      have hz : ∀ j, raw12783 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12783step0 = (fun i j => raw12783 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12783step0 raw12783; decide +kernel
      have hl : raw12783step0Labels = raw12783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12783 raw12783Labels permutation265 hz
    mixedMoment B raw12783step0 raw12783step0Labels = mixedMoment B raw12783step1 raw12783step1Labels := by
      have ha : raw12783step1 = (fun i j => raw12783step0 (permutation45 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12783step1 raw12783step0; decide +kernel
      have hl : raw12783step1Labels = raw12783step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12783step0 raw12783step0Labels permutation45 permutation3
    mixedMoment B raw12783step1 raw12783step1Labels = mixedMoment B raw12783step2 raw12783step2Labels := by
      have ha : raw12783step2 = raw12783step1 := by apply Matrix.ext; unfold raw12783step2 raw12783step1; decide +kernel
      have hl : raw12783step1Labels = labelEmbedding6 ∘ raw12783step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12783step1 raw12783step1Labels raw12783step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw12784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw12784step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12784step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![2, 0, -2], ![1, 0, -1]]
def raw12784step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12784step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12784step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12784step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12784step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12784 raw12784Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw12784 raw12784Labels = mixedMoment B raw12784step0 raw12784step0Labels := by
      have hz : ∀ j, raw12784 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12784step0 = (fun i j => raw12784 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12784step0 raw12784; decide +kernel
      have hl : raw12784step0Labels = raw12784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12784 raw12784Labels permutation590 hz
    mixedMoment B raw12784step0 raw12784step0Labels = mixedMoment B raw12784step1 raw12784step1Labels := by
      have hz : ∀ j, raw12784step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12784step1 = (fun i j => raw12784step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12784step1 raw12784step0; decide +kernel
      have hl : raw12784step1Labels = raw12784step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12784step0 raw12784step0Labels permutation56 hz
    mixedMoment B raw12784step1 raw12784step1Labels = mixedMoment B raw12784step2 raw12784step2Labels := by
      have ha : raw12784step2 = (fun i j => raw12784step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12784step2 raw12784step1; decide +kernel
      have hl : raw12784step2Labels = raw12784step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12784step1 raw12784step1Labels permutation9 permutation3
    mixedMoment B raw12784step2 raw12784step2Labels = mixedMoment B raw12784step3 raw12784step3Labels := by
      have ha : raw12784step3 = raw12784step2 := by apply Matrix.ext; unfold raw12784step3 raw12784step2; decide +kernel
      have hl : raw12784step2Labels = labelEmbedding6 ∘ raw12784step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12784step2 raw12784step2Labels raw12784step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw12785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12785step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12785step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12785step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12785step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12785 raw12785Labels = mixedMoment B node4471 node4471Labels := by
  calc
    mixedMoment B raw12785 raw12785Labels = mixedMoment B raw12785step0 raw12785step0Labels := by
      have hz : ∀ j, raw12785 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12785step0 = (fun i j => raw12785 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12785step0 raw12785; decide +kernel
      have hl : raw12785step0Labels = raw12785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12785 raw12785Labels permutation265 hz
    mixedMoment B raw12785step0 raw12785step0Labels = mixedMoment B raw12785step1 raw12785step1Labels := by
      have ha : raw12785step1 = (fun i j => raw12785step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12785step1 raw12785step0; decide +kernel
      have hl : raw12785step1Labels = raw12785step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12785step0 raw12785step0Labels permutation33 permutation3
    mixedMoment B raw12785step1 raw12785step1Labels = mixedMoment B raw12785step2 raw12785step2Labels := by
      have ha : raw12785step2 = raw12785step1 := by apply Matrix.ext; unfold raw12785step2 raw12785step1; decide +kernel
      have hl : raw12785step1Labels = labelEmbedding6 ∘ raw12785step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12785step1 raw12785step1Labels raw12785step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4471 node4471Labels := by rfl

def raw12786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12786step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12786step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12786step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12786 raw12786Labels = mixedMoment B node5083 node5083Labels := by
  calc
    mixedMoment B raw12786 raw12786Labels = mixedMoment B raw12786step0 raw12786step0Labels := by
      have ha : raw12786step0 = (fun i j => raw12786 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12786step0 raw12786; decide +kernel
      have hl : raw12786step0Labels = raw12786Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12786 raw12786Labels permutation153 permutation3
    mixedMoment B raw12786step0 raw12786step0Labels = mixedMoment B raw12786step1 raw12786step1Labels := by
      have ha : raw12786step1 = raw12786step0 := by apply Matrix.ext; unfold raw12786step1 raw12786step0; decide +kernel
      have hl : raw12786step0Labels = labelEmbedding6 ∘ raw12786step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12786step0 raw12786step0Labels raw12786step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5083 node5083Labels := by rfl

def raw12787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12787step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12787step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12787step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12787 raw12787Labels = mixedMoment B node5199 node5199Labels := by
  calc
    mixedMoment B raw12787 raw12787Labels = mixedMoment B raw12787step0 raw12787step0Labels := by
      have hz : ∀ j, raw12787 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12787step0 = (fun i j => raw12787 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12787step0 raw12787; decide +kernel
      have hl : raw12787step0Labels = raw12787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12787 raw12787Labels permutation265 hz
    mixedMoment B raw12787step0 raw12787step0Labels = mixedMoment B raw12787step1 raw12787step1Labels := by
      have ha : raw12787step1 = (fun i j => raw12787step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12787step1 raw12787step0; decide +kernel
      have hl : raw12787step1Labels = raw12787step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12787step0 raw12787step0Labels permutation33 permutation3
    mixedMoment B raw12787step1 raw12787step1Labels = mixedMoment B raw12787step2 raw12787step2Labels := by
      have ha : raw12787step2 = raw12787step1 := by apply Matrix.ext; unfold raw12787step2 raw12787step1; decide +kernel
      have hl : raw12787step1Labels = labelEmbedding6 ∘ raw12787step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12787step1 raw12787step1Labels raw12787step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5199 node5199Labels := by rfl

def raw12788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw12788step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw12788step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw12788step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12788 raw12788Labels = mixedMoment B node5233 node5233Labels := by
  calc
    mixedMoment B raw12788 raw12788Labels = mixedMoment B raw12788step0 raw12788step0Labels := by
      have hz : ∀ j, raw12788 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12788step0 = (fun i j => raw12788 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12788step0 raw12788; decide +kernel
      have hl : raw12788step0Labels = raw12788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12788 raw12788Labels permutation265 hz
    mixedMoment B raw12788step0 raw12788step0Labels = mixedMoment B raw12788step1 raw12788step1Labels := by
      have ha : raw12788step1 = (fun i j => raw12788step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12788step1 raw12788step0; decide +kernel
      have hl : raw12788step1Labels = raw12788step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12788step0 raw12788step0Labels permutation39 permutation3
    mixedMoment B raw12788step1 raw12788step1Labels = mixedMoment B raw12788step2 raw12788step2Labels := by
      have ha : raw12788step2 = raw12788step1 := by apply Matrix.ext; unfold raw12788step2 raw12788step1; decide +kernel
      have hl : raw12788step1Labels = labelEmbedding6 ∘ raw12788step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12788step1 raw12788step1Labels raw12788step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5233 node5233Labels := by rfl

def raw12789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0]]
def raw12789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw12789step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12789step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw12789step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12789step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw12789step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12789step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw12789step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12789 raw12789Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw12789 raw12789Labels = mixedMoment B raw12789step0 raw12789step0Labels := by
      have hz : ∀ j, raw12789 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12789step0 = (fun i j => raw12789 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12789step0 raw12789; decide +kernel
      have hl : raw12789step0Labels = raw12789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12789 raw12789Labels permutation590 hz
    mixedMoment B raw12789step0 raw12789step0Labels = mixedMoment B raw12789step1 raw12789step1Labels := by
      have hz : ∀ j, raw12789step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12789step1 = (fun i j => raw12789step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12789step1 raw12789step0; decide +kernel
      have hl : raw12789step1Labels = raw12789step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12789step0 raw12789step0Labels permutation56 hz
    mixedMoment B raw12789step1 raw12789step1Labels = mixedMoment B raw12789step2 raw12789step2Labels := by
      have ha : raw12789step2 = (fun i j => raw12789step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12789step2 raw12789step1; decide +kernel
      have hl : raw12789step2Labels = raw12789step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12789step1 raw12789step1Labels permutation8 permutation3
    mixedMoment B raw12789step2 raw12789step2Labels = mixedMoment B raw12789step3 raw12789step3Labels := by
      have ha : raw12789step3 = raw12789step2 := by apply Matrix.ext; unfold raw12789step3 raw12789step2; decide +kernel
      have hl : raw12789step2Labels = labelEmbedding6 ∘ raw12789step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12789step2 raw12789step2Labels raw12789step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw12790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12790step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12790step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12790step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12790step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12790 raw12790Labels = mixedMoment B node4470 node4470Labels := by
  calc
    mixedMoment B raw12790 raw12790Labels = mixedMoment B raw12790step0 raw12790step0Labels := by
      have hz : ∀ j, raw12790 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12790step0 = (fun i j => raw12790 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12790step0 raw12790; decide +kernel
      have hl : raw12790step0Labels = raw12790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12790 raw12790Labels permutation265 hz
    mixedMoment B raw12790step0 raw12790step0Labels = mixedMoment B raw12790step1 raw12790step1Labels := by
      have ha : raw12790step1 = (fun i j => raw12790step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12790step1 raw12790step0; decide +kernel
      have hl : raw12790step1Labels = raw12790step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12790step0 raw12790step0Labels permutation32 permutation3
    mixedMoment B raw12790step1 raw12790step1Labels = mixedMoment B raw12790step2 raw12790step2Labels := by
      have ha : raw12790step2 = raw12790step1 := by apply Matrix.ext; unfold raw12790step2 raw12790step1; decide +kernel
      have hl : raw12790step1Labels = labelEmbedding6 ∘ raw12790step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12790step1 raw12790step1Labels raw12790step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4470 node4470Labels := by rfl

def raw12791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12791step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12791step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12791step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12791 raw12791Labels = mixedMoment B node5082 node5082Labels := by
  calc
    mixedMoment B raw12791 raw12791Labels = mixedMoment B raw12791step0 raw12791step0Labels := by
      have ha : raw12791step0 = (fun i j => raw12791 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12791step0 raw12791; decide +kernel
      have hl : raw12791step0Labels = raw12791Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12791 raw12791Labels permutation152 permutation3
    mixedMoment B raw12791step0 raw12791step0Labels = mixedMoment B raw12791step1 raw12791step1Labels := by
      have ha : raw12791step1 = raw12791step0 := by apply Matrix.ext; unfold raw12791step1 raw12791step0; decide +kernel
      have hl : raw12791step0Labels = labelEmbedding6 ∘ raw12791step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12791step0 raw12791step0Labels raw12791step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5082 node5082Labels := by rfl

def raw12792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12792step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12792step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12792step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12792 raw12792Labels = mixedMoment B node5198 node5198Labels := by
  calc
    mixedMoment B raw12792 raw12792Labels = mixedMoment B raw12792step0 raw12792step0Labels := by
      have hz : ∀ j, raw12792 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12792step0 = (fun i j => raw12792 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12792step0 raw12792; decide +kernel
      have hl : raw12792step0Labels = raw12792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12792 raw12792Labels permutation265 hz
    mixedMoment B raw12792step0 raw12792step0Labels = mixedMoment B raw12792step1 raw12792step1Labels := by
      have ha : raw12792step1 = (fun i j => raw12792step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12792step1 raw12792step0; decide +kernel
      have hl : raw12792step1Labels = raw12792step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12792step0 raw12792step0Labels permutation32 permutation3
    mixedMoment B raw12792step1 raw12792step1Labels = mixedMoment B raw12792step2 raw12792step2Labels := by
      have ha : raw12792step2 = raw12792step1 := by apply Matrix.ext; unfold raw12792step2 raw12792step1; decide +kernel
      have hl : raw12792step1Labels = labelEmbedding6 ∘ raw12792step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12792step1 raw12792step1Labels raw12792step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5198 node5198Labels := by rfl

def raw12793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw12793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw12793step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw12793step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12793 raw12793Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw12793 raw12793Labels = mixedMoment B raw12793step0 raw12793step0Labels := by
      have hz : ∀ j, raw12793 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12793step0 = (fun i j => raw12793 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12793step0 raw12793; decide +kernel
      have hl : raw12793step0Labels = raw12793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12793 raw12793Labels permutation265 hz
    mixedMoment B raw12793step0 raw12793step0Labels = mixedMoment B raw12793step1 raw12793step1Labels := by
      have ha : raw12793step1 = (fun i j => raw12793step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12793step1 raw12793step0; decide +kernel
      have hl : raw12793step1Labels = raw12793step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12793step0 raw12793step0Labels permutation38 permutation3
    mixedMoment B raw12793step1 raw12793step1Labels = mixedMoment B raw12793step2 raw12793step2Labels := by
      have ha : raw12793step2 = raw12793step1 := by apply Matrix.ext; unfold raw12793step2 raw12793step1; decide +kernel
      have hl : raw12793step1Labels = labelEmbedding6 ∘ raw12793step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12793step1 raw12793step1Labels raw12793step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5232 node5232Labels := by rfl

def raw12794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw12794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw12794step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw12794step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12794step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw12794step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12794 raw12794Labels = mixedMoment B node5264 node5264Labels := by
  calc
    mixedMoment B raw12794 raw12794Labels = mixedMoment B raw12794step0 raw12794step0Labels := by
      have hz : ∀ j, raw12794 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12794step0 = (fun i j => raw12794 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12794step0 raw12794; decide +kernel
      have hl : raw12794step0Labels = raw12794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12794 raw12794Labels permutation265 hz
    mixedMoment B raw12794step0 raw12794step0Labels = mixedMoment B raw12794step1 raw12794step1Labels := by
      have ha : raw12794step1 = (fun i j => raw12794step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12794step1 raw12794step0; decide +kernel
      have hl : raw12794step1Labels = raw12794step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12794step0 raw12794step0Labels permutation44 permutation3
    mixedMoment B raw12794step1 raw12794step1Labels = mixedMoment B raw12794step2 raw12794step2Labels := by
      have ha : raw12794step2 = raw12794step1 := by apply Matrix.ext; unfold raw12794step2 raw12794step1; decide +kernel
      have hl : raw12794step1Labels = labelEmbedding6 ∘ raw12794step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12794step1 raw12794step1Labels raw12794step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5264 node5264Labels := by rfl

def raw12795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12795Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12795step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12795step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12795step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12795 raw12795Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw12795 raw12795Labels = mixedMoment B raw12795step0 raw12795step0Labels := by
      have ha : raw12795step0 = (fun i j => raw12795 (permutation362 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12795step0 raw12795; decide +kernel
      have hl : raw12795step0Labels = raw12795Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12795 raw12795Labels permutation362 permutation6
    mixedMoment B raw12795step0 raw12795step0Labels = mixedMoment B raw12795step1 raw12795step1Labels := by
      have ha : raw12795step1 = -raw12795step0 := by apply Matrix.ext; change ∀ i j, raw12795step1 i j = -(raw12795step0 i j); unfold raw12795step1 raw12795step0; decide +kernel
      have hl : raw12795step1Labels = raw12795step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw12796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12796Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12796step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw12796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12796 raw12796Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw12796 raw12796Labels = mixedMoment B raw12796step0 raw12796step0Labels := by
      have hz : ∀ j, raw12796 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12796step0 = (fun i j => raw12796 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12796step0 raw12796; decide +kernel
      have hl : raw12796step0Labels = raw12796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12796 raw12796Labels permutation265 hz
    mixedMoment B raw12796step0 raw12796step0Labels = mixedMoment B raw12796step1 raw12796step1Labels := by
      have ha : raw12796step1 = (fun i j => raw12796step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12796step1 raw12796step0; decide +kernel
      have hl : raw12796step1Labels = raw12796step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12796step0 raw12796step0Labels permutation96 permutation6
    _ = mixedMoment B node3995 node3995Labels := by rfl

def raw12797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12797Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw12797step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12797step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12797 raw12797Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw12797 raw12797Labels = mixedMoment B raw12797step0 raw12797step0Labels := by
      have hz : ∀ j, raw12797 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12797step0 = (fun i j => raw12797 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12797step0 raw12797; decide +kernel
      have hl : raw12797step0Labels = raw12797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12797 raw12797Labels permutation265 hz
    mixedMoment B raw12797step0 raw12797step0Labels = mixedMoment B raw12797step1 raw12797step1Labels := by
      have ha : raw12797step1 = (fun i j => raw12797step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12797step1 raw12797step0; decide +kernel
      have hl : raw12797step1Labels = raw12797step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12797step0 raw12797step0Labels permutation96 permutation6
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw12798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12798Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw12798step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12798step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12798step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw12798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12798 raw12798Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw12798 raw12798Labels = mixedMoment B raw12798step0 raw12798step0Labels := by
      have hz : ∀ j, raw12798 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12798step0 = (fun i j => raw12798 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12798step0 raw12798; decide +kernel
      have hl : raw12798step0Labels = raw12798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12798 raw12798Labels permutation265 hz
    mixedMoment B raw12798step0 raw12798step0Labels = mixedMoment B raw12798step1 raw12798step1Labels := by
      have ha : raw12798step1 = (fun i j => raw12798step0 (permutation61 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12798step1 raw12798step0; decide +kernel
      have hl : raw12798step1Labels = raw12798step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12798step0 raw12798step0Labels permutation61 permutation6
    mixedMoment B raw12798step1 raw12798step1Labels = mixedMoment B raw12798step2 raw12798step2Labels := by
      have ha : raw12798step2 = -raw12798step1 := by apply Matrix.ext; change ∀ i j, raw12798step2 i j = -(raw12798step1 i j); unfold raw12798step2 raw12798step1; decide +kernel
      have hl : raw12798step2Labels = raw12798step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw12799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw12799Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12799step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12799step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1]]
def raw12799step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12799step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12799step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12799step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12799step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12799 raw12799Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw12799 raw12799Labels = mixedMoment B raw12799step0 raw12799step0Labels := by
      have hz : ∀ j, raw12799 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw12799step0 = (fun i j => raw12799 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw12799step0 raw12799; decide +kernel
      have hl : raw12799step0Labels = raw12799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12799 raw12799Labels permutation590 hz
    mixedMoment B raw12799step0 raw12799step0Labels = mixedMoment B raw12799step1 raw12799step1Labels := by
      have hz : ∀ j, raw12799step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12799step1 = (fun i j => raw12799step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12799step1 raw12799step0; decide +kernel
      have hl : raw12799step1Labels = raw12799step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12799step0 raw12799step0Labels permutation56 hz
    mixedMoment B raw12799step1 raw12799step1Labels = mixedMoment B raw12799step2 raw12799step2Labels := by
      have ha : raw12799step2 = (fun i j => raw12799step1 (permutation15 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12799step2 raw12799step1; decide +kernel
      have hl : raw12799step2Labels = raw12799step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12799step1 raw12799step1Labels permutation15 permutation6
    mixedMoment B raw12799step2 raw12799step2Labels = mixedMoment B raw12799step3 raw12799step3Labels := by
      have ha : raw12799step3 = -raw12799step2 := by apply Matrix.ext; change ∀ i j, raw12799step3 i j = -(raw12799step2 i j); unfold raw12799step3 raw12799step2; decide +kernel
      have hl : raw12799step3Labels = raw12799step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3888 node3888Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
