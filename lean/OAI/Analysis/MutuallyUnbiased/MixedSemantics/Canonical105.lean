import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw13440 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13440Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw13440step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13440step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw13440step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13440 raw13440Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw13440 raw13440Labels = mixedMoment B raw13440step0 raw13440step0Labels := by
      have ha : raw13440step0 = (fun i j => raw13440 (permutation178 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13440step0 raw13440; decide +kernel
      have hl : raw13440step0Labels = raw13440Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13440 raw13440Labels permutation178 permutation6
    mixedMoment B raw13440step0 raw13440step0Labels = mixedMoment B raw13440step1 raw13440step1Labels := by
      have ha : raw13440step1 = raw13440step0 := by apply Matrix.ext; unfold raw13440step1 raw13440step0; decide +kernel
      have hl : raw13440step0Labels = labelEmbedding9 ∘ raw13440step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13440step0 raw13440step0Labels raw13440step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5286 node5286Labels := by rfl

def raw13441 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13441Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw13441step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13441step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw13441step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13441 raw13441Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw13441 raw13441Labels = mixedMoment B raw13441step0 raw13441step0Labels := by
      have ha : raw13441step0 = (fun i j => raw13441 (permutation180 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13441step0 raw13441; decide +kernel
      have hl : raw13441step0Labels = raw13441Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13441 raw13441Labels permutation180 permutation6
    mixedMoment B raw13441step0 raw13441step0Labels = mixedMoment B raw13441step1 raw13441step1Labels := by
      have ha : raw13441step1 = raw13441step0 := by apply Matrix.ext; unfold raw13441step1 raw13441step0; decide +kernel
      have hl : raw13441step0Labels = labelEmbedding9 ∘ raw13441step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13441step0 raw13441step0Labels raw13441step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5286 node5286Labels := by rfl

def raw13442 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13442step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13442step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13442step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13442step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13442step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13442 raw13442Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw13442 raw13442Labels = mixedMoment B raw13442step0 raw13442step0Labels := by
      have ha : raw13442step0 = (fun i j => raw13442 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13442step0 raw13442; decide +kernel
      have hl : raw13442step0Labels = raw13442Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13442 raw13442Labels permutation240 permutation4
    mixedMoment B raw13442step0 raw13442step0Labels = mixedMoment B raw13442step1 raw13442step1Labels := by
      have ha : raw13442step1 = -raw13442step0 := by apply Matrix.ext; change ∀ i j, raw13442step1 i j = -(raw13442step0 i j); unfold raw13442step1 raw13442step0; decide +kernel
      have hl : raw13442step1Labels = raw13442step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13442step1 raw13442step1Labels = mixedMoment B raw13442step2 raw13442step2Labels := by
      have ha : raw13442step2 = raw13442step1 := by apply Matrix.ext; unfold raw13442step2 raw13442step1; decide +kernel
      have hl : raw13442step1Labels = labelEmbedding7 ∘ raw13442step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13442step1 raw13442step1Labels raw13442step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4887 node4887Labels := by rfl

def raw13443 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13443step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13443step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13443step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13443step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13443 raw13443Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw13443 raw13443Labels = mixedMoment B raw13443step0 raw13443step0Labels := by
      have hz : ∀ j, raw13443 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13443step0 = (fun i j => raw13443 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13443step0 raw13443; decide +kernel
      have hl : raw13443step0Labels = raw13443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13443 raw13443Labels permutation346 hz
    mixedMoment B raw13443step0 raw13443step0Labels = mixedMoment B raw13443step1 raw13443step1Labels := by
      have ha : raw13443step1 = (fun i j => raw13443step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13443step1 raw13443step0; decide +kernel
      have hl : raw13443step1Labels = raw13443step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13443step0 raw13443step0Labels permutation35 permutation6
    mixedMoment B raw13443step1 raw13443step1Labels = mixedMoment B raw13443step2 raw13443step2Labels := by
      have ha : raw13443step2 = raw13443step1 := by apply Matrix.ext; unfold raw13443step2 raw13443step1; decide +kernel
      have hl : raw13443step1Labels = labelEmbedding9 ∘ raw13443step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13443step1 raw13443step1Labels raw13443step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw13444 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13444Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13444step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13444step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13444step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13444 raw13444Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw13444 raw13444Labels = mixedMoment B raw13444step0 raw13444step0Labels := by
      have ha : raw13444step0 = (fun i j => raw13444 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13444step0 raw13444; decide +kernel
      have hl : raw13444step0Labels = raw13444Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13444 raw13444Labels permutation155 permutation6
    mixedMoment B raw13444step0 raw13444step0Labels = mixedMoment B raw13444step1 raw13444step1Labels := by
      have ha : raw13444step1 = raw13444step0 := by apply Matrix.ext; unfold raw13444step1 raw13444step0; decide +kernel
      have hl : raw13444step0Labels = labelEmbedding9 ∘ raw13444step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13444step0 raw13444step0Labels raw13444step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw13445 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13445Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13445step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13445step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13445step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13445step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13445 raw13445Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw13445 raw13445Labels = mixedMoment B raw13445step0 raw13445step0Labels := by
      have ha : raw13445step0 = (fun i j => raw13445 (permutation157 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13445step0 raw13445; decide +kernel
      have hl : raw13445step0Labels = raw13445Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13445 raw13445Labels permutation157 permutation6
    mixedMoment B raw13445step0 raw13445step0Labels = mixedMoment B raw13445step1 raw13445step1Labels := by
      have ha : raw13445step1 = raw13445step0 := by apply Matrix.ext; unfold raw13445step1 raw13445step0; decide +kernel
      have hl : raw13445step0Labels = labelEmbedding9 ∘ raw13445step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13445step0 raw13445step0Labels raw13445step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw13446 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13446Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13446step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13446step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13446step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13446step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13446step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13446 raw13446Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw13446 raw13446Labels = mixedMoment B raw13446step0 raw13446step0Labels := by
      have ha : raw13446step0 = (fun i j => raw13446 (permutation218 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13446step0 raw13446; decide +kernel
      have hl : raw13446step0Labels = raw13446Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13446 raw13446Labels permutation218 permutation4
    mixedMoment B raw13446step0 raw13446step0Labels = mixedMoment B raw13446step1 raw13446step1Labels := by
      have ha : raw13446step1 = -raw13446step0 := by apply Matrix.ext; change ∀ i j, raw13446step1 i j = -(raw13446step0 i j); unfold raw13446step1 raw13446step0; decide +kernel
      have hl : raw13446step1Labels = raw13446step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13446step1 raw13446step1Labels = mixedMoment B raw13446step2 raw13446step2Labels := by
      have ha : raw13446step2 = raw13446step1 := by apply Matrix.ext; unfold raw13446step2 raw13446step1; decide +kernel
      have hl : raw13446step1Labels = labelEmbedding7 ∘ raw13446step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13446step1 raw13446step1Labels raw13446step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4887 node4887Labels := by rfl

def raw13447 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13447Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13447step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13447step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13447step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13447step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13447 raw13447Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw13447 raw13447Labels = mixedMoment B raw13447step0 raw13447step0Labels := by
      have hz : ∀ j, raw13447 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13447step0 = (fun i j => raw13447 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13447step0 raw13447; decide +kernel
      have hl : raw13447step0Labels = raw13447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13447 raw13447Labels permutation346 hz
    mixedMoment B raw13447step0 raw13447step0Labels = mixedMoment B raw13447step1 raw13447step1Labels := by
      have ha : raw13447step1 = (fun i j => raw13447step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13447step1 raw13447step0; decide +kernel
      have hl : raw13447step1Labels = raw13447step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13447step0 raw13447step0Labels permutation33 permutation6
    mixedMoment B raw13447step1 raw13447step1Labels = mixedMoment B raw13447step2 raw13447step2Labels := by
      have ha : raw13447step2 = raw13447step1 := by apply Matrix.ext; unfold raw13447step2 raw13447step1; decide +kernel
      have hl : raw13447step1Labels = labelEmbedding9 ∘ raw13447step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13447step1 raw13447step1Labels raw13447step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw13448 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13448Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13448step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13448step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13448 raw13448Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw13448 raw13448Labels = mixedMoment B raw13448step0 raw13448step0Labels := by
      have ha : raw13448step0 = (fun i j => raw13448 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13448step0 raw13448; decide +kernel
      have hl : raw13448step0Labels = raw13448Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13448 raw13448Labels permutation156 permutation6
    mixedMoment B raw13448step0 raw13448step0Labels = mixedMoment B raw13448step1 raw13448step1Labels := by
      have ha : raw13448step1 = raw13448step0 := by apply Matrix.ext; unfold raw13448step1 raw13448step0; decide +kernel
      have hl : raw13448step0Labels = labelEmbedding9 ∘ raw13448step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13448step0 raw13448step0Labels raw13448step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw13449 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13449Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13449step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13449step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13449step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13449step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13449 raw13449Labels = mixedMoment B node2741 node2741Labels := by
  calc
    mixedMoment B raw13449 raw13449Labels = mixedMoment B raw13449step0 raw13449step0Labels := by
      have hz : ∀ j, raw13449 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13449step0 = (fun i j => raw13449 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13449step0 raw13449; decide +kernel
      have hl : raw13449step0Labels = raw13449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13449 raw13449Labels permutation346 hz
    mixedMoment B raw13449step0 raw13449step0Labels = mixedMoment B raw13449step1 raw13449step1Labels := by
      have ha : raw13449step1 = (fun i j => raw13449step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13449step1 raw13449step0; decide +kernel
      have hl : raw13449step1Labels = raw13449step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13449step0 raw13449step0Labels permutation32 permutation7
    mixedMoment B raw13449step1 raw13449step1Labels = mixedMoment B raw13449step2 raw13449step2Labels := by
      have ha : raw13449step2 = raw13449step1 := by apply Matrix.ext; unfold raw13449step2 raw13449step1; decide +kernel
      have hl : raw13449step1Labels = labelEmbedding1 ∘ raw13449step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13449step1 raw13449step1Labels raw13449step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2741 node2741Labels := by rfl

def raw13450 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13450Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13450step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13450step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13450step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13450 raw13450Labels = mixedMoment B node2703 node2703Labels := by
  calc
    mixedMoment B raw13450 raw13450Labels = mixedMoment B raw13450step0 raw13450step0Labels := by
      have ha : raw13450step0 = (fun i j => raw13450 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13450step0 raw13450; decide +kernel
      have hl : raw13450step0Labels = raw13450Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13450 raw13450Labels permutation153 permutation7
    mixedMoment B raw13450step0 raw13450step0Labels = mixedMoment B raw13450step1 raw13450step1Labels := by
      have ha : raw13450step1 = raw13450step0 := by apply Matrix.ext; unfold raw13450step1 raw13450step0; decide +kernel
      have hl : raw13450step0Labels = labelEmbedding1 ∘ raw13450step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13450step0 raw13450step0Labels raw13450step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2703 node2703Labels := by rfl

def raw13451 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13451Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13451step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13451step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13451step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13451 raw13451Labels = mixedMoment B node2703 node2703Labels := by
  calc
    mixedMoment B raw13451 raw13451Labels = mixedMoment B raw13451step0 raw13451step0Labels := by
      have ha : raw13451step0 = (fun i j => raw13451 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13451step0 raw13451; decide +kernel
      have hl : raw13451step0Labels = raw13451Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13451 raw13451Labels permutation152 permutation7
    mixedMoment B raw13451step0 raw13451step0Labels = mixedMoment B raw13451step1 raw13451step1Labels := by
      have ha : raw13451step1 = raw13451step0 := by apply Matrix.ext; unfold raw13451step1 raw13451step0; decide +kernel
      have hl : raw13451step0Labels = labelEmbedding1 ∘ raw13451step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13451step0 raw13451step0Labels raw13451step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2703 node2703Labels := by rfl

def raw13452 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13452Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13452step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13452step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13452 raw13452Labels = mixedMoment B node3221 node3221Labels := by
  calc
    mixedMoment B raw13452 raw13452Labels = mixedMoment B raw13452step0 raw13452step0Labels := by
      have ha : raw13452step0 = (fun i j => raw13452 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13452step0 raw13452; decide +kernel
      have hl : raw13452step0Labels = raw13452Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13452 raw13452Labels permutation152 permutation7
    mixedMoment B raw13452step0 raw13452step0Labels = mixedMoment B raw13452step1 raw13452step1Labels := by
      have ha : raw13452step1 = raw13452step0 := by apply Matrix.ext; unfold raw13452step1 raw13452step0; decide +kernel
      have hl : raw13452step0Labels = labelEmbedding1 ∘ raw13452step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13452step0 raw13452step0Labels raw13452step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3221 node3221Labels := by rfl

def raw13453 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13453Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13453step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13453step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13453step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13453step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13453 raw13453Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw13453 raw13453Labels = mixedMoment B raw13453step0 raw13453step0Labels := by
      have hz : ∀ j, raw13453 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13453step0 = (fun i j => raw13453 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13453step0 raw13453; decide +kernel
      have hl : raw13453step0Labels = raw13453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13453 raw13453Labels permutation346 hz
    mixedMoment B raw13453step0 raw13453step0Labels = mixedMoment B raw13453step1 raw13453step1Labels := by
      have ha : raw13453step1 = (fun i j => raw13453step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13453step1 raw13453step0; decide +kernel
      have hl : raw13453step1Labels = raw13453step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13453step0 raw13453step0Labels permutation32 permutation7
    mixedMoment B raw13453step1 raw13453step1Labels = mixedMoment B raw13453step2 raw13453step2Labels := by
      have ha : raw13453step2 = raw13453step1 := by apply Matrix.ext; unfold raw13453step2 raw13453step1; decide +kernel
      have hl : raw13453step1Labels = labelEmbedding1 ∘ raw13453step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13453step1 raw13453step1Labels raw13453step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3053 node3053Labels := by rfl

def raw13454 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13454Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13454step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13454step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13454 raw13454Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw13454 raw13454Labels = mixedMoment B raw13454step0 raw13454step0Labels := by
      have ha : raw13454step0 = (fun i j => raw13454 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13454step0 raw13454; decide +kernel
      have hl : raw13454step0Labels = raw13454Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13454 raw13454Labels permutation153 permutation7
    mixedMoment B raw13454step0 raw13454step0Labels = mixedMoment B raw13454step1 raw13454step1Labels := by
      have ha : raw13454step1 = raw13454step0 := by apply Matrix.ext; unfold raw13454step1 raw13454step0; decide +kernel
      have hl : raw13454step0Labels = labelEmbedding1 ∘ raw13454step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13454step0 raw13454step0Labels raw13454step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3023 node3023Labels := by rfl

def raw13455 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13455Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13455step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13455step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13455 raw13455Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw13455 raw13455Labels = mixedMoment B raw13455step0 raw13455step0Labels := by
      have ha : raw13455step0 = (fun i j => raw13455 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13455step0 raw13455; decide +kernel
      have hl : raw13455step0Labels = raw13455Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13455 raw13455Labels permutation152 permutation7
    mixedMoment B raw13455step0 raw13455step0Labels = mixedMoment B raw13455step1 raw13455step1Labels := by
      have ha : raw13455step1 = raw13455step0 := by apply Matrix.ext; unfold raw13455step1 raw13455step0; decide +kernel
      have hl : raw13455step0Labels = labelEmbedding1 ∘ raw13455step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13455step0 raw13455step0Labels raw13455step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3023 node3023Labels := by rfl

def raw13456 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13456Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13456step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13456step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13456step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13456step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13456 raw13456Labels = mixedMoment B node3226 node3226Labels := by
  calc
    mixedMoment B raw13456 raw13456Labels = mixedMoment B raw13456step0 raw13456step0Labels := by
      have ha : raw13456step0 = (fun i j => raw13456 (permutation244 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13456step0 raw13456; decide +kernel
      have hl : raw13456step0Labels = raw13456Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13456 raw13456Labels permutation244 permutation5
    mixedMoment B raw13456step0 raw13456step0Labels = mixedMoment B raw13456step1 raw13456step1Labels := by
      have ha : raw13456step1 = -raw13456step0 := by apply Matrix.ext; change ∀ i j, raw13456step1 i j = -(raw13456step0 i j); unfold raw13456step1 raw13456step0; decide +kernel
      have hl : raw13456step1Labels = raw13456step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13456step1 raw13456step1Labels = mixedMoment B raw13456step2 raw13456step2Labels := by
      have ha : raw13456step2 = raw13456step1 := by apply Matrix.ext; unfold raw13456step2 raw13456step1; decide +kernel
      have hl : raw13456step1Labels = labelEmbedding1 ∘ raw13456step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13456step1 raw13456step1Labels raw13456step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3226 node3226Labels := by rfl

def raw13457 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13457Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13457step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13457step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13457step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13457step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13457 raw13457Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw13457 raw13457Labels = mixedMoment B raw13457step0 raw13457step0Labels := by
      have hz : ∀ j, raw13457 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13457step0 = (fun i j => raw13457 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13457step0 raw13457; decide +kernel
      have hl : raw13457step0Labels = raw13457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13457 raw13457Labels permutation346 hz
    mixedMoment B raw13457step0 raw13457step0Labels = mixedMoment B raw13457step1 raw13457step1Labels := by
      have ha : raw13457step1 = (fun i j => raw13457step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13457step1 raw13457step0; decide +kernel
      have hl : raw13457step1Labels = raw13457step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13457step0 raw13457step0Labels permutation32 permutation7
    mixedMoment B raw13457step1 raw13457step1Labels = mixedMoment B raw13457step2 raw13457step2Labels := by
      have ha : raw13457step2 = raw13457step1 := by apply Matrix.ext; unfold raw13457step2 raw13457step1; decide +kernel
      have hl : raw13457step1Labels = labelEmbedding1 ∘ raw13457step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13457step1 raw13457step1Labels raw13457step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw13458 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13458Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13458step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13458step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13458 raw13458Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw13458 raw13458Labels = mixedMoment B raw13458step0 raw13458step0Labels := by
      have ha : raw13458step0 = (fun i j => raw13458 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13458step0 raw13458; decide +kernel
      have hl : raw13458step0Labels = raw13458Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13458 raw13458Labels permutation153 permutation7
    mixedMoment B raw13458step0 raw13458step0Labels = mixedMoment B raw13458step1 raw13458step1Labels := by
      have ha : raw13458step1 = raw13458step0 := by apply Matrix.ext; unfold raw13458step1 raw13458step0; decide +kernel
      have hl : raw13458step0Labels = labelEmbedding1 ∘ raw13458step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13458step0 raw13458step0Labels raw13458step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw13459 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13459Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13459step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13459step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13459step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13459 raw13459Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw13459 raw13459Labels = mixedMoment B raw13459step0 raw13459step0Labels := by
      have ha : raw13459step0 = (fun i j => raw13459 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13459step0 raw13459; decide +kernel
      have hl : raw13459step0Labels = raw13459Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13459 raw13459Labels permutation152 permutation7
    mixedMoment B raw13459step0 raw13459step0Labels = mixedMoment B raw13459step1 raw13459step1Labels := by
      have ha : raw13459step1 = raw13459step0 := by apply Matrix.ext; unfold raw13459step1 raw13459step0; decide +kernel
      have hl : raw13459step0Labels = labelEmbedding1 ∘ raw13459step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13459step0 raw13459step0Labels raw13459step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw13460 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13460Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13460step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13460step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13460step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13460step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13460step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13460 raw13460Labels = mixedMoment B node3226 node3226Labels := by
  calc
    mixedMoment B raw13460 raw13460Labels = mixedMoment B raw13460step0 raw13460step0Labels := by
      have ha : raw13460step0 = (fun i j => raw13460 (permutation222 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13460step0 raw13460; decide +kernel
      have hl : raw13460step0Labels = raw13460Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13460 raw13460Labels permutation222 permutation5
    mixedMoment B raw13460step0 raw13460step0Labels = mixedMoment B raw13460step1 raw13460step1Labels := by
      have ha : raw13460step1 = -raw13460step0 := by apply Matrix.ext; change ∀ i j, raw13460step1 i j = -(raw13460step0 i j); unfold raw13460step1 raw13460step0; decide +kernel
      have hl : raw13460step1Labels = raw13460step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13460step1 raw13460step1Labels = mixedMoment B raw13460step2 raw13460step2Labels := by
      have ha : raw13460step2 = raw13460step1 := by apply Matrix.ext; unfold raw13460step2 raw13460step1; decide +kernel
      have hl : raw13460step1Labels = labelEmbedding1 ∘ raw13460step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13460step1 raw13460step1Labels raw13460step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3226 node3226Labels := by rfl

def raw13461 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13461Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13461step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13461step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13461step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13461step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13461 raw13461Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw13461 raw13461Labels = mixedMoment B raw13461step0 raw13461step0Labels := by
      have hz : ∀ j, raw13461 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13461step0 = (fun i j => raw13461 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13461step0 raw13461; decide +kernel
      have hl : raw13461step0Labels = raw13461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13461 raw13461Labels permutation346 hz
    mixedMoment B raw13461step0 raw13461step0Labels = mixedMoment B raw13461step1 raw13461step1Labels := by
      have ha : raw13461step1 = (fun i j => raw13461step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13461step1 raw13461step0; decide +kernel
      have hl : raw13461step1Labels = raw13461step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13461step0 raw13461step0Labels permutation34 permutation7
    mixedMoment B raw13461step1 raw13461step1Labels = mixedMoment B raw13461step2 raw13461step2Labels := by
      have ha : raw13461step2 = raw13461step1 := by apply Matrix.ext; unfold raw13461step2 raw13461step1; decide +kernel
      have hl : raw13461step1Labels = labelEmbedding1 ∘ raw13461step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13461step1 raw13461step1Labels raw13461step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw13462 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13462Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13462step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13462step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13462step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13462 raw13462Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw13462 raw13462Labels = mixedMoment B raw13462step0 raw13462step0Labels := by
      have ha : raw13462step0 = (fun i j => raw13462 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13462step0 raw13462; decide +kernel
      have hl : raw13462step0Labels = raw13462Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13462 raw13462Labels permutation154 permutation7
    mixedMoment B raw13462step0 raw13462step0Labels = mixedMoment B raw13462step1 raw13462step1Labels := by
      have ha : raw13462step1 = raw13462step0 := by apply Matrix.ext; unfold raw13462step1 raw13462step0; decide +kernel
      have hl : raw13462step0Labels = labelEmbedding1 ∘ raw13462step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13462step0 raw13462step0Labels raw13462step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw13463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13463step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13463step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13463 raw13463Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw13463 raw13463Labels = mixedMoment B raw13463step0 raw13463step0Labels := by
      have hz : ∀ j, raw13463 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13463step0 = (fun i j => raw13463 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13463step0 raw13463; decide +kernel
      have hl : raw13463step0Labels = raw13463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13463 raw13463Labels permutation346 hz
    mixedMoment B raw13463step0 raw13463step0Labels = mixedMoment B raw13463step1 raw13463step1Labels := by
      have ha : raw13463step1 = (fun i j => raw13463step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13463step1 raw13463step0; decide +kernel
      have hl : raw13463step1Labels = raw13463step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13463step0 raw13463step0Labels permutation36 permutation2
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw13464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13464step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13464 raw13464Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw13464 raw13464Labels = mixedMoment B raw13464step0 raw13464step0Labels := by
      have ha : raw13464step0 = (fun i j => raw13464 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13464step0 raw13464; decide +kernel
      have hl : raw13464step0Labels = raw13464Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13464 raw13464Labels permutation180 permutation2
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw13465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13465step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13465step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13465step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13465step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13465step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13465step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13465step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13465 raw13465Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw13465 raw13465Labels = mixedMoment B raw13465step0 raw13465step0Labels := by
      have hz : ∀ j, raw13465 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13465step0 = (fun i j => raw13465 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13465step0 raw13465; decide +kernel
      have hl : raw13465step0Labels = raw13465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13465 raw13465Labels permutation346 hz
    mixedMoment B raw13465step0 raw13465step0Labels = mixedMoment B raw13465step1 raw13465step1Labels := by
      have ha : raw13465step1 = (fun i j => raw13465step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13465step1 raw13465step0; decide +kernel
      have hl : raw13465step1Labels = raw13465step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13465step0 raw13465step0Labels permutation50 permutation7
    mixedMoment B raw13465step1 raw13465step1Labels = mixedMoment B raw13465step2 raw13465step2Labels := by
      have ha : raw13465step2 = -raw13465step1 := by apply Matrix.ext; change ∀ i j, raw13465step2 i j = -(raw13465step1 i j); unfold raw13465step2 raw13465step1; decide +kernel
      have hl : raw13465step2Labels = raw13465step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13465step2 raw13465step2Labels = mixedMoment B raw13465step3 raw13465step3Labels := by
      have ha : raw13465step3 = raw13465step2 := by apply Matrix.ext; unfold raw13465step3 raw13465step2; decide +kernel
      have hl : raw13465step2Labels = labelEmbedding10 ∘ raw13465step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13465step2 raw13465step2Labels raw13465step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw13466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13466step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13466step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13466step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13466step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13466step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13466step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13466step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13466 raw13466Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw13466 raw13466Labels = mixedMoment B raw13466step0 raw13466step0Labels := by
      have hz : ∀ j, raw13466 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13466step0 = (fun i j => raw13466 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13466step0 raw13466; decide +kernel
      have hl : raw13466step0Labels = raw13466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13466 raw13466Labels permutation346 hz
    mixedMoment B raw13466step0 raw13466step0Labels = mixedMoment B raw13466step1 raw13466step1Labels := by
      have ha : raw13466step1 = (fun i j => raw13466step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13466step1 raw13466step0; decide +kernel
      have hl : raw13466step1Labels = raw13466step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13466step0 raw13466step0Labels permutation51 permutation7
    mixedMoment B raw13466step1 raw13466step1Labels = mixedMoment B raw13466step2 raw13466step2Labels := by
      have ha : raw13466step2 = -raw13466step1 := by apply Matrix.ext; change ∀ i j, raw13466step2 i j = -(raw13466step1 i j); unfold raw13466step2 raw13466step1; decide +kernel
      have hl : raw13466step2Labels = raw13466step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13466step2 raw13466step2Labels = mixedMoment B raw13466step3 raw13466step3Labels := by
      have ha : raw13466step3 = raw13466step2 := by apply Matrix.ext; unfold raw13466step3 raw13466step2; decide +kernel
      have hl : raw13466step2Labels = labelEmbedding10 ∘ raw13466step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13466step2 raw13466step2Labels raw13466step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw13467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13467step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13467step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13467step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13467step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13467step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13467step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13467step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13467 raw13467Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw13467 raw13467Labels = mixedMoment B raw13467step0 raw13467step0Labels := by
      have hz : ∀ j, raw13467 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13467step0 = (fun i j => raw13467 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13467step0 raw13467; decide +kernel
      have hl : raw13467step0Labels = raw13467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13467 raw13467Labels permutation346 hz
    mixedMoment B raw13467step0 raw13467step0Labels = mixedMoment B raw13467step1 raw13467step1Labels := by
      have ha : raw13467step1 = (fun i j => raw13467step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13467step1 raw13467step0; decide +kernel
      have hl : raw13467step1Labels = raw13467step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13467step0 raw13467step0Labels permutation50 permutation7
    mixedMoment B raw13467step1 raw13467step1Labels = mixedMoment B raw13467step2 raw13467step2Labels := by
      have ha : raw13467step2 = -raw13467step1 := by apply Matrix.ext; change ∀ i j, raw13467step2 i j = -(raw13467step1 i j); unfold raw13467step2 raw13467step1; decide +kernel
      have hl : raw13467step2Labels = raw13467step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13467step2 raw13467step2Labels = mixedMoment B raw13467step3 raw13467step3Labels := by
      have ha : raw13467step3 = raw13467step2 := by apply Matrix.ext; unfold raw13467step3 raw13467step2; decide +kernel
      have hl : raw13467step2Labels = labelEmbedding10 ∘ raw13467step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13467step2 raw13467step2Labels raw13467step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw13468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13468step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13468step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13468 raw13468Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw13468 raw13468Labels = mixedMoment B raw13468step0 raw13468step0Labels := by
      have hz : ∀ j, raw13468 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13468step0 = (fun i j => raw13468 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13468step0 raw13468; decide +kernel
      have hl : raw13468step0Labels = raw13468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13468 raw13468Labels permutation346 hz
    mixedMoment B raw13468step0 raw13468step0Labels = mixedMoment B raw13468step1 raw13468step1Labels := by
      have ha : raw13468step1 = (fun i j => raw13468step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13468step1 raw13468step0; decide +kernel
      have hl : raw13468step1Labels = raw13468step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13468step0 raw13468step0Labels permutation50 permutation2
    _ = mixedMoment B node4618 node4618Labels := by rfl

def raw13469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13469step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13469 raw13469Labels = mixedMoment B node5162 node5162Labels := by
  calc
    mixedMoment B raw13469 raw13469Labels = mixedMoment B raw13469step0 raw13469step0Labels := by
      have ha : raw13469step0 = (fun i j => raw13469 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13469step0 raw13469; decide +kernel
      have hl : raw13469step0Labels = raw13469Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13469 raw13469Labels permutation194 permutation2
    _ = mixedMoment B node5162 node5162Labels := by rfl

def raw13470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13470step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13470 raw13470Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw13470 raw13470Labels = mixedMoment B raw13470step0 raw13470step0Labels := by
      have hz : ∀ j, raw13470 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13470step0 = (fun i j => raw13470 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13470step0 raw13470; decide +kernel
      have hl : raw13470step0Labels = raw13470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13470 raw13470Labels permutation346 hz
    mixedMoment B raw13470step0 raw13470step0Labels = mixedMoment B raw13470step1 raw13470step1Labels := by
      have ha : raw13470step1 = (fun i j => raw13470step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13470step1 raw13470step0; decide +kernel
      have hl : raw13470step1Labels = raw13470step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13470step0 raw13470step0Labels permutation42 permutation2
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw13471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13471 raw13471Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw13471 raw13471Labels = mixedMoment B raw13471step0 raw13471step0Labels := by
      have hz : ∀ j, raw13471 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13471step0 = (fun i j => raw13471 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13471step0 raw13471; decide +kernel
      have hl : raw13471step0Labels = raw13471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13471 raw13471Labels permutation346 hz
    mixedMoment B raw13471step0 raw13471step0Labels = mixedMoment B raw13471step1 raw13471step1Labels := by
      have ha : raw13471step1 = (fun i j => raw13471step0 (permutation48 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13471step1 raw13471step0; decide +kernel
      have hl : raw13471step1Labels = raw13471step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13471step0 raw13471step0Labels permutation48 permutation2
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw13472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13472step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13472 raw13472Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw13472 raw13472Labels = mixedMoment B raw13472step0 raw13472step0Labels := by
      have hz : ∀ j, raw13472 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13472step0 = (fun i j => raw13472 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13472step0 raw13472; decide +kernel
      have hl : raw13472step0Labels = raw13472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13472 raw13472Labels permutation346 hz
    mixedMoment B raw13472step0 raw13472step0Labels = mixedMoment B raw13472step1 raw13472step1Labels := by
      have ha : raw13472step1 = (fun i j => raw13472step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13472step1 raw13472step0; decide +kernel
      have hl : raw13472step1Labels = raw13472step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13472step0 raw13472step0Labels permutation50 permutation2
    _ = mixedMoment B node5273 node5273Labels := by rfl

def raw13473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13473step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13473step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13473step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13473 raw13473Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw13473 raw13473Labels = mixedMoment B raw13473step0 raw13473step0Labels := by
      have ha : raw13473step0 = (fun i j => raw13473 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13473step0 raw13473; decide +kernel
      have hl : raw13473step0Labels = raw13473Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13473 raw13473Labels permutation160 permutation3
    mixedMoment B raw13473step0 raw13473step0Labels = mixedMoment B raw13473step1 raw13473step1Labels := by
      have ha : raw13473step1 = raw13473step0 := by apply Matrix.ext; unfold raw13473step1 raw13473step0; decide +kernel
      have hl : raw13473step0Labels = labelEmbedding6 ∘ raw13473step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13473step0 raw13473step0Labels raw13473step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw13474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13474 raw13474Labels = mixedMoment B node5197 node5197Labels := by
  calc
    mixedMoment B raw13474 raw13474Labels = mixedMoment B raw13474step0 raw13474step0Labels := by
      have ha : raw13474step0 = (fun i j => raw13474 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13474step0 raw13474; decide +kernel
      have hl : raw13474step0Labels = raw13474Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13474 raw13474Labels permutation170 permutation2
    _ = mixedMoment B node5197 node5197Labels := by rfl

def raw13475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13475step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13475 raw13475Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw13475 raw13475Labels = mixedMoment B raw13475step0 raw13475step0Labels := by
      have ha : raw13475step0 = (fun i j => raw13475 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13475step0 raw13475; decide +kernel
      have hl : raw13475step0Labels = raw13475Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13475 raw13475Labels permutation162 permutation2
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw13476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13476step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13476 raw13476Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw13476 raw13476Labels = mixedMoment B raw13476step0 raw13476step0Labels := by
      have ha : raw13476step0 = (fun i j => raw13476 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13476step0 raw13476; decide +kernel
      have hl : raw13476step0Labels = raw13476Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13476 raw13476Labels permutation168 permutation2
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw13477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13477 raw13477Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw13477 raw13477Labels = mixedMoment B raw13477step0 raw13477step0Labels := by
      have ha : raw13477step0 = (fun i j => raw13477 (permutation246 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13477step0 raw13477; decide +kernel
      have hl : raw13477step0Labels = raw13477Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13477 raw13477Labels permutation246 permutation2
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw13478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13478step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13478step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13478step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13478 raw13478Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw13478 raw13478Labels = mixedMoment B raw13478step0 raw13478step0Labels := by
      have hz : ∀ j, raw13478 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13478step0 = (fun i j => raw13478 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13478step0 raw13478; decide +kernel
      have hl : raw13478step0Labels = raw13478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13478 raw13478Labels permutation346 hz
    mixedMoment B raw13478step0 raw13478step0Labels = mixedMoment B raw13478step1 raw13478step1Labels := by
      have ha : raw13478step1 = (fun i j => raw13478step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13478step1 raw13478step0; decide +kernel
      have hl : raw13478step1Labels = raw13478step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13478step0 raw13478step0Labels permutation35 permutation3
    mixedMoment B raw13478step1 raw13478step1Labels = mixedMoment B raw13478step2 raw13478step2Labels := by
      have ha : raw13478step2 = raw13478step1 := by apply Matrix.ext; unfold raw13478step2 raw13478step1; decide +kernel
      have hl : raw13478step1Labels = labelEmbedding6 ∘ raw13478step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13478step1 raw13478step1Labels raw13478step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw13479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13479 raw13479Labels = mixedMoment B node5199 node5199Labels := by
  calc
    mixedMoment B raw13479 raw13479Labels = mixedMoment B raw13479step0 raw13479step0Labels := by
      have hz : ∀ j, raw13479 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13479step0 = (fun i j => raw13479 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13479step0 raw13479; decide +kernel
      have hl : raw13479step0Labels = raw13479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13479 raw13479Labels permutation346 hz
    mixedMoment B raw13479step0 raw13479step0Labels = mixedMoment B raw13479step1 raw13479step1Labels := by
      have ha : raw13479step1 = (fun i j => raw13479step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13479step1 raw13479step0; decide +kernel
      have hl : raw13479step1Labels = raw13479step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13479step0 raw13479step0Labels permutation37 permutation2
    _ = mixedMoment B node5199 node5199Labels := by rfl

def raw13480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13480step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13480 raw13480Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw13480 raw13480Labels = mixedMoment B raw13480step0 raw13480step0Labels := by
      have ha : raw13480step0 = (fun i j => raw13480 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13480step0 raw13480; decide +kernel
      have hl : raw13480step0Labels = raw13480Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13480 raw13480Labels permutation181 permutation2
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw13481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13481step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw13481step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13481 raw13481Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw13481 raw13481Labels = mixedMoment B raw13481step0 raw13481step0Labels := by
      have hz : ∀ j, raw13481 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13481step0 = (fun i j => raw13481 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13481step0 raw13481; decide +kernel
      have hl : raw13481step0Labels = raw13481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13481 raw13481Labels permutation346 hz
    mixedMoment B raw13481step0 raw13481step0Labels = mixedMoment B raw13481step1 raw13481step1Labels := by
      have ha : raw13481step1 = (fun i j => raw13481step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13481step1 raw13481step0; decide +kernel
      have hl : raw13481step1Labels = raw13481step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13481step0 raw13481step0Labels permutation35 permutation2
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw13482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13482step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13482step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13482step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13482 raw13482Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw13482 raw13482Labels = mixedMoment B raw13482step0 raw13482step0Labels := by
      have hz : ∀ j, raw13482 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13482step0 = (fun i j => raw13482 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13482step0 raw13482; decide +kernel
      have hl : raw13482step0Labels = raw13482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13482 raw13482Labels permutation346 hz
    mixedMoment B raw13482step0 raw13482step0Labels = mixedMoment B raw13482step1 raw13482step1Labels := by
      have ha : raw13482step1 = (fun i j => raw13482step0 (permutation51 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13482step1 raw13482step0; decide +kernel
      have hl : raw13482step1Labels = raw13482step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13482step0 raw13482step0Labels permutation51 permutation2
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw13483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13483step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13483step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13483step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13483 raw13483Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw13483 raw13483Labels = mixedMoment B raw13483step0 raw13483step0Labels := by
      have hz : ∀ j, raw13483 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13483step0 = (fun i j => raw13483 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13483step0 raw13483; decide +kernel
      have hl : raw13483step0Labels = raw13483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13483 raw13483Labels permutation346 hz
    mixedMoment B raw13483step0 raw13483step0Labels = mixedMoment B raw13483step1 raw13483step1Labels := by
      have ha : raw13483step1 = (fun i j => raw13483step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13483step1 raw13483step0; decide +kernel
      have hl : raw13483step1Labels = raw13483step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13483step0 raw13483step0Labels permutation33 permutation3
    mixedMoment B raw13483step1 raw13483step1Labels = mixedMoment B raw13483step2 raw13483step2Labels := by
      have ha : raw13483step2 = raw13483step1 := by apply Matrix.ext; unfold raw13483step2 raw13483step1; decide +kernel
      have hl : raw13483step1Labels = labelEmbedding6 ∘ raw13483step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13483step1 raw13483step1Labels raw13483step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw13484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13484step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13484 raw13484Labels = mixedMoment B node5199 node5199Labels := by
  calc
    mixedMoment B raw13484 raw13484Labels = mixedMoment B raw13484step0 raw13484step0Labels := by
      have hz : ∀ j, raw13484 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13484step0 = (fun i j => raw13484 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13484step0 raw13484; decide +kernel
      have hl : raw13484step0Labels = raw13484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13484 raw13484Labels permutation346 hz
    mixedMoment B raw13484step0 raw13484step0Labels = mixedMoment B raw13484step1 raw13484step1Labels := by
      have ha : raw13484step1 = (fun i j => raw13484step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13484step1 raw13484step0; decide +kernel
      have hl : raw13484step1Labels = raw13484step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13484step0 raw13484step0Labels permutation36 permutation2
    _ = mixedMoment B node5199 node5199Labels := by rfl

def raw13485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13485step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13485 raw13485Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw13485 raw13485Labels = mixedMoment B raw13485step0 raw13485step0Labels := by
      have ha : raw13485step0 = (fun i j => raw13485 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13485step0 raw13485; decide +kernel
      have hl : raw13485step0Labels = raw13485Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13485 raw13485Labels permutation180 permutation2
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw13486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13486step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13486step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw13486step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13486 raw13486Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw13486 raw13486Labels = mixedMoment B raw13486step0 raw13486step0Labels := by
      have hz : ∀ j, raw13486 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13486step0 = (fun i j => raw13486 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13486step0 raw13486; decide +kernel
      have hl : raw13486step0Labels = raw13486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13486 raw13486Labels permutation346 hz
    mixedMoment B raw13486step0 raw13486step0Labels = mixedMoment B raw13486step1 raw13486step1Labels := by
      have ha : raw13486step1 = (fun i j => raw13486step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13486step1 raw13486step0; decide +kernel
      have hl : raw13486step1Labels = raw13486step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13486step0 raw13486step0Labels permutation33 permutation2
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw13487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw13487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw13487step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13487step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13487 raw13487Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw13487 raw13487Labels = mixedMoment B raw13487step0 raw13487step0Labels := by
      have hz : ∀ j, raw13487 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13487step0 = (fun i j => raw13487 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13487step0 raw13487; decide +kernel
      have hl : raw13487step0Labels = raw13487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13487 raw13487Labels permutation346 hz
    mixedMoment B raw13487step0 raw13487step0Labels = mixedMoment B raw13487step1 raw13487step1Labels := by
      have ha : raw13487step1 = (fun i j => raw13487step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13487step1 raw13487step0; decide +kernel
      have hl : raw13487step1Labels = raw13487step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13487step0 raw13487step0Labels permutation50 permutation2
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw13488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13488step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw13488step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13488step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw13488step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13488 raw13488Labels = mixedMoment B node4600 node4600Labels := by
  calc
    mixedMoment B raw13488 raw13488Labels = mixedMoment B raw13488step0 raw13488step0Labels := by
      have hz : ∀ j, raw13488 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13488step0 = (fun i j => raw13488 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13488step0 raw13488; decide +kernel
      have hl : raw13488step0Labels = raw13488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13488 raw13488Labels permutation346 hz
    mixedMoment B raw13488step0 raw13488step0Labels = mixedMoment B raw13488step1 raw13488step1Labels := by
      have ha : raw13488step1 = (fun i j => raw13488step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13488step1 raw13488step0; decide +kernel
      have hl : raw13488step1Labels = raw13488step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13488step0 raw13488step0Labels permutation32 permutation3
    mixedMoment B raw13488step1 raw13488step1Labels = mixedMoment B raw13488step2 raw13488step2Labels := by
      have ha : raw13488step2 = raw13488step1 := by apply Matrix.ext; unfold raw13488step2 raw13488step1; decide +kernel
      have hl : raw13488step1Labels = labelEmbedding6 ∘ raw13488step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13488step1 raw13488step1Labels raw13488step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4600 node4600Labels := by rfl

def raw13489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13489Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13489step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13489 raw13489Labels = mixedMoment B node5205 node5205Labels := by
  calc
    mixedMoment B raw13489 raw13489Labels = mixedMoment B raw13489step0 raw13489step0Labels := by
      have hz : ∀ j, raw13489 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13489step0 = (fun i j => raw13489 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13489step0 raw13489; decide +kernel
      have hl : raw13489step0Labels = raw13489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13489 raw13489Labels permutation346 hz
    _ = mixedMoment B node5205 node5205Labels := by rfl

def raw13490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13490step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13490 raw13490Labels = mixedMoment B node5150 node5150Labels := by
  calc
    mixedMoment B raw13490 raw13490Labels = mixedMoment B raw13490step0 raw13490step0Labels := by
      have ha : raw13490step0 = (fun i j => raw13490 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13490step0 raw13490; decide +kernel
      have hl : raw13490step0Labels = raw13490Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13490 raw13490Labels permutation176 permutation2
    _ = mixedMoment B node5150 node5150Labels := by rfl

def raw13491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13491Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13491step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13491step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw13491step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13491step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13491 raw13491Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw13491 raw13491Labels = mixedMoment B raw13491step0 raw13491step0Labels := by
      have hz : ∀ j, raw13491 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13491step0 = (fun i j => raw13491 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13491step0 raw13491; decide +kernel
      have hl : raw13491step0Labels = raw13491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13491 raw13491Labels permutation346 hz
    mixedMoment B raw13491step0 raw13491step0Labels = mixedMoment B raw13491step1 raw13491step1Labels := by
      have ha : raw13491step1 = (fun i j => raw13491step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13491step1 raw13491step0; decide +kernel
      have hl : raw13491step1Labels = raw13491step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13491step0 raw13491step0Labels permutation149 permutation5
    mixedMoment B raw13491step1 raw13491step1Labels = mixedMoment B raw13491step2 raw13491step2Labels := by
      have ha : raw13491step2 = raw13491step1 := by apply Matrix.ext; unfold raw13491step2 raw13491step1; decide +kernel
      have hl : raw13491step1Labels = labelEmbedding8 ∘ raw13491step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13491step1 raw13491step1Labels raw13491step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw13492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw13492Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw13492step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13492step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw13492step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13492step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13492 raw13492Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw13492 raw13492Labels = mixedMoment B raw13492step0 raw13492step0Labels := by
      have hz : ∀ j, raw13492 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13492step0 = (fun i j => raw13492 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13492step0 raw13492; decide +kernel
      have hl : raw13492step0Labels = raw13492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13492 raw13492Labels permutation346 hz
    mixedMoment B raw13492step0 raw13492step0Labels = mixedMoment B raw13492step1 raw13492step1Labels := by
      have ha : raw13492step1 = (fun i j => raw13492step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13492step1 raw13492step0; decide +kernel
      have hl : raw13492step1Labels = raw13492step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13492step0 raw13492step0Labels permutation143 permutation5
    mixedMoment B raw13492step1 raw13492step1Labels = mixedMoment B raw13492step2 raw13492step2Labels := by
      have ha : raw13492step2 = raw13492step1 := by apply Matrix.ext; unfold raw13492step2 raw13492step1; decide +kernel
      have hl : raw13492step1Labels = labelEmbedding8 ∘ raw13492step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13492step1 raw13492step1Labels raw13492step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw13493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13493step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13493step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13493 raw13493Labels = mixedMoment B node4028 node4028Labels := by
  calc
    mixedMoment B raw13493 raw13493Labels = mixedMoment B raw13493step0 raw13493step0Labels := by
      have hz : ∀ j, raw13493 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13493step0 = (fun i j => raw13493 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13493step0 raw13493; decide +kernel
      have hl : raw13493step0Labels = raw13493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13493 raw13493Labels permutation346 hz
    mixedMoment B raw13493step0 raw13493step0Labels = mixedMoment B raw13493step1 raw13493step1Labels := by
      have ha : raw13493step1 = (fun i j => raw13493step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13493step1 raw13493step0; decide +kernel
      have hl : raw13493step1Labels = raw13493step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13493step0 raw13493step0Labels permutation32 permutation3
    _ = mixedMoment B node4028 node4028Labels := by rfl

def raw13494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13494step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13494 raw13494Labels = mixedMoment B node4026 node4026Labels := by
  calc
    mixedMoment B raw13494 raw13494Labels = mixedMoment B raw13494step0 raw13494step0Labels := by
      have ha : raw13494step0 = (fun i j => raw13494 (permutation255 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13494step0 raw13494; decide +kernel
      have hl : raw13494step0Labels = raw13494Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13494 raw13494Labels permutation255 permutation6
    mixedMoment B raw13494step0 raw13494step0Labels = mixedMoment B raw13494step1 raw13494step1Labels := by
      have ha : raw13494step1 = -raw13494step0 := by apply Matrix.ext; change ∀ i j, raw13494step1 i j = -(raw13494step0 i j); unfold raw13494step1 raw13494step0; decide +kernel
      have hl : raw13494step1Labels = raw13494step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4026 node4026Labels := by rfl

def raw13495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13495step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13495step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13495 raw13495Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw13495 raw13495Labels = mixedMoment B raw13495step0 raw13495step0Labels := by
      have hz : ∀ j, raw13495 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13495step0 = (fun i j => raw13495 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13495step0 raw13495; decide +kernel
      have hl : raw13495step0Labels = raw13495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13495 raw13495Labels permutation346 hz
    mixedMoment B raw13495step0 raw13495step0Labels = mixedMoment B raw13495step1 raw13495step1Labels := by
      have ha : raw13495step1 = (fun i j => raw13495step0 (permutation54 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13495step1 raw13495step0; decide +kernel
      have hl : raw13495step1Labels = raw13495step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13495step0 raw13495step0Labels permutation54 permutation6
    mixedMoment B raw13495step1 raw13495step1Labels = mixedMoment B raw13495step2 raw13495step2Labels := by
      have ha : raw13495step2 = -raw13495step1 := by apply Matrix.ext; change ∀ i j, raw13495step2 i j = -(raw13495step1 i j); unfold raw13495step2 raw13495step1; decide +kernel
      have hl : raw13495step2Labels = raw13495step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw13496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13496step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13496 raw13496Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw13496 raw13496Labels = mixedMoment B raw13496step0 raw13496step0Labels := by
      have hz : ∀ j, raw13496 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13496step0 = (fun i j => raw13496 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13496step0 raw13496; decide +kernel
      have hl : raw13496step0Labels = raw13496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13496 raw13496Labels permutation346 hz
    mixedMoment B raw13496step0 raw13496step0Labels = mixedMoment B raw13496step1 raw13496step1Labels := by
      have ha : raw13496step1 = (fun i j => raw13496step0 (permutation52 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13496step1 raw13496step0; decide +kernel
      have hl : raw13496step1Labels = raw13496step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13496step0 raw13496step0Labels permutation52 permutation6
    mixedMoment B raw13496step1 raw13496step1Labels = mixedMoment B raw13496step2 raw13496step2Labels := by
      have ha : raw13496step2 = -raw13496step1 := by apply Matrix.ext; change ∀ i j, raw13496step2 i j = -(raw13496step1 i j); unfold raw13496step2 raw13496step1; decide +kernel
      have hl : raw13496step2Labels = raw13496step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw13497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13497step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13497step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13497 raw13497Labels = mixedMoment B node4036 node4036Labels := by
  calc
    mixedMoment B raw13497 raw13497Labels = mixedMoment B raw13497step0 raw13497step0Labels := by
      have hz : ∀ j, raw13497 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13497step0 = (fun i j => raw13497 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13497step0 raw13497; decide +kernel
      have hl : raw13497step0Labels = raw13497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13497 raw13497Labels permutation346 hz
    mixedMoment B raw13497step0 raw13497step0Labels = mixedMoment B raw13497step1 raw13497step1Labels := by
      have ha : raw13497step1 = (fun i j => raw13497step0 (permutation53 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13497step1 raw13497step0; decide +kernel
      have hl : raw13497step1Labels = raw13497step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13497step0 raw13497step0Labels permutation53 permutation6
    mixedMoment B raw13497step1 raw13497step1Labels = mixedMoment B raw13497step2 raw13497step2Labels := by
      have ha : raw13497step2 = -raw13497step1 := by apply Matrix.ext; change ∀ i j, raw13497step2 i j = -(raw13497step1 i j); unfold raw13497step2 raw13497step1; decide +kernel
      have hl : raw13497step2Labels = raw13497step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4036 node4036Labels := by rfl

def raw13498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13498step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13498 raw13498Labels = mixedMoment B node1298 node1298Labels := by
  calc
    mixedMoment B raw13498 raw13498Labels = mixedMoment B raw13498step0 raw13498step0Labels := by
      have hz : ∀ j, raw13498 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13498step0 = (fun i j => raw13498 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13498step0 raw13498; decide +kernel
      have hl : raw13498step0Labels = raw13498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13498 raw13498Labels permutation346 hz
    mixedMoment B raw13498step0 raw13498step0Labels = mixedMoment B raw13498step1 raw13498step1Labels := by
      have ha : raw13498step1 = (fun i j => raw13498step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13498step1 raw13498step0; decide +kernel
      have hl : raw13498step1Labels = raw13498step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13498step0 raw13498step0Labels permutation32 permutation3
    _ = mixedMoment B node1298 node1298Labels := by rfl

def raw13499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13499 raw13499Labels = mixedMoment B node2957 node2957Labels := by
  calc
    mixedMoment B raw13499 raw13499Labels = mixedMoment B raw13499step0 raw13499step0Labels := by
      have ha : raw13499step0 = (fun i j => raw13499 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13499step0 raw13499; decide +kernel
      have hl : raw13499step0Labels = raw13499Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13499 raw13499Labels permutation176 permutation3
    _ = mixedMoment B node2957 node2957Labels := by rfl

def raw13500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13500 raw13500Labels = mixedMoment B node3099 node3099Labels := by
  calc
    mixedMoment B raw13500 raw13500Labels = mixedMoment B raw13500step0 raw13500step0Labels := by
      have hz : ∀ j, raw13500 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13500step0 = (fun i j => raw13500 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13500step0 raw13500; decide +kernel
      have hl : raw13500step0Labels = raw13500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13500 raw13500Labels permutation346 hz
    mixedMoment B raw13500step0 raw13500step0Labels = mixedMoment B raw13500step1 raw13500step1Labels := by
      have ha : raw13500step1 = (fun i j => raw13500step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13500step1 raw13500step0; decide +kernel
      have hl : raw13500step1Labels = raw13500step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13500step0 raw13500step0Labels permutation38 permutation3
    _ = mixedMoment B node3099 node3099Labels := by rfl

def raw13501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13501step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13501 raw13501Labels = mixedMoment B node3099 node3099Labels := by
  calc
    mixedMoment B raw13501 raw13501Labels = mixedMoment B raw13501step0 raw13501step0Labels := by
      have hz : ∀ j, raw13501 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13501step0 = (fun i j => raw13501 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13501step0 raw13501; decide +kernel
      have hl : raw13501step0Labels = raw13501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13501 raw13501Labels permutation346 hz
    mixedMoment B raw13501step0 raw13501step0Labels = mixedMoment B raw13501step1 raw13501step1Labels := by
      have ha : raw13501step1 = (fun i j => raw13501step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13501step1 raw13501step0; decide +kernel
      have hl : raw13501step1Labels = raw13501step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13501step0 raw13501step0Labels permutation44 permutation3
    _ = mixedMoment B node3099 node3099Labels := by rfl

def raw13502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13502step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13502 raw13502Labels = mixedMoment B node3111 node3111Labels := by
  calc
    mixedMoment B raw13502 raw13502Labels = mixedMoment B raw13502step0 raw13502step0Labels := by
      have hz : ∀ j, raw13502 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13502step0 = (fun i j => raw13502 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13502step0 raw13502; decide +kernel
      have hl : raw13502step0Labels = raw13502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13502 raw13502Labels permutation346 hz
    mixedMoment B raw13502step0 raw13502step0Labels = mixedMoment B raw13502step1 raw13502step1Labels := by
      have ha : raw13502step1 = (fun i j => raw13502step0 (permutation50 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13502step1 raw13502step0; decide +kernel
      have hl : raw13502step1Labels = raw13502step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13502step0 raw13502step0Labels permutation50 permutation3
    _ = mixedMoment B node3111 node3111Labels := by rfl

def raw13503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13503 raw13503Labels = mixedMoment B node1233 node1233Labels := by
  calc
    mixedMoment B raw13503 raw13503Labels = mixedMoment B raw13503step0 raw13503step0Labels := by
      have ha : raw13503step0 = (fun i j => raw13503 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13503step0 raw13503; decide +kernel
      have hl : raw13503step0Labels = raw13503Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13503 raw13503Labels permutation160 permutation3
    _ = mixedMoment B node1233 node1233Labels := by rfl

def raw13504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13504 raw13504Labels = mixedMoment B node2878 node2878Labels := by
  calc
    mixedMoment B raw13504 raw13504Labels = mixedMoment B raw13504step0 raw13504step0Labels := by
      have ha : raw13504step0 = (fun i j => raw13504 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13504step0 raw13504; decide +kernel
      have hl : raw13504step0Labels = raw13504Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13504 raw13504Labels permutation160 permutation3
    _ = mixedMoment B node2878 node2878Labels := by rfl

def raw13505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13505 raw13505Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw13505 raw13505Labels = mixedMoment B raw13505step0 raw13505step0Labels := by
      have ha : raw13505step0 = (fun i j => raw13505 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13505step0 raw13505; decide +kernel
      have hl : raw13505step0Labels = raw13505Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13505 raw13505Labels permutation160 permutation3
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw13506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13506 raw13506Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw13506 raw13506Labels = mixedMoment B raw13506step0 raw13506step0Labels := by
      have ha : raw13506step0 = (fun i j => raw13506 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13506step0 raw13506; decide +kernel
      have hl : raw13506step0Labels = raw13506Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13506 raw13506Labels permutation166 permutation3
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw13507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13507 raw13507Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw13507 raw13507Labels = mixedMoment B raw13507step0 raw13507step0Labels := by
      have ha : raw13507step0 = (fun i j => raw13507 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13507step0 raw13507; decide +kernel
      have hl : raw13507step0Labels = raw13507Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13507 raw13507Labels permutation173 permutation3
    _ = mixedMoment B node3087 node3087Labels := by rfl

def raw13508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13508step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13508 raw13508Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw13508 raw13508Labels = mixedMoment B raw13508step0 raw13508step0Labels := by
      have hz : ∀ j, raw13508 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13508step0 = (fun i j => raw13508 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13508step0 raw13508; decide +kernel
      have hl : raw13508step0Labels = raw13508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13508 raw13508Labels permutation346 hz
    mixedMoment B raw13508step0 raw13508step0Labels = mixedMoment B raw13508step1 raw13508step1Labels := by
      have ha : raw13508step1 = (fun i j => raw13508step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13508step1 raw13508step0; decide +kernel
      have hl : raw13508step1Labels = raw13508step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13508step0 raw13508step0Labels permutation35 permutation3
    _ = mixedMoment B node1237 node1237Labels := by rfl

def raw13509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13509step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13509step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13509 raw13509Labels = mixedMoment B node2882 node2882Labels := by
  calc
    mixedMoment B raw13509 raw13509Labels = mixedMoment B raw13509step0 raw13509step0Labels := by
      have hz : ∀ j, raw13509 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13509step0 = (fun i j => raw13509 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13509step0 raw13509; decide +kernel
      have hl : raw13509step0Labels = raw13509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13509 raw13509Labels permutation346 hz
    mixedMoment B raw13509step0 raw13509step0Labels = mixedMoment B raw13509step1 raw13509step1Labels := by
      have ha : raw13509step1 = (fun i j => raw13509step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13509step1 raw13509step0; decide +kernel
      have hl : raw13509step1Labels = raw13509step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13509step0 raw13509step0Labels permutation35 permutation3
    _ = mixedMoment B node2882 node2882Labels := by rfl

def raw13510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13510Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13510step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13510 raw13510Labels = mixedMoment B node2925 node2925Labels := by
  calc
    mixedMoment B raw13510 raw13510Labels = mixedMoment B raw13510step0 raw13510step0Labels := by
      have ha : raw13510step0 = (fun i j => raw13510 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13510step0 raw13510; decide +kernel
      have hl : raw13510step0Labels = raw13510Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13510 raw13510Labels permutation179 permutation3
    _ = mixedMoment B node2925 node2925Labels := by rfl

def raw13511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13511Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13511step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13511 raw13511Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw13511 raw13511Labels = mixedMoment B raw13511step0 raw13511step0Labels := by
      have hz : ∀ j, raw13511 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13511step0 = (fun i j => raw13511 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13511step0 raw13511; decide +kernel
      have hl : raw13511step0Labels = raw13511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13511 raw13511Labels permutation346 hz
    mixedMoment B raw13511step0 raw13511step0Labels = mixedMoment B raw13511step1 raw13511step1Labels := by
      have ha : raw13511step1 = (fun i j => raw13511step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13511step1 raw13511step0; decide +kernel
      have hl : raw13511step1Labels = raw13511step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13511step0 raw13511step0Labels permutation35 permutation3
    _ = mixedMoment B node3078 node3078Labels := by rfl

def raw13512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13512Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13512step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13512step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13512step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13512 raw13512Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw13512 raw13512Labels = mixedMoment B raw13512step0 raw13512step0Labels := by
      have hz : ∀ j, raw13512 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13512step0 = (fun i j => raw13512 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13512step0 raw13512; decide +kernel
      have hl : raw13512step0Labels = raw13512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13512 raw13512Labels permutation346 hz
    mixedMoment B raw13512step0 raw13512step0Labels = mixedMoment B raw13512step1 raw13512step1Labels := by
      have ha : raw13512step1 = (fun i j => raw13512step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13512step1 raw13512step0; decide +kernel
      have hl : raw13512step1Labels = raw13512step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13512step0 raw13512step0Labels permutation37 permutation3
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw13513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13513Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13513step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13513 raw13513Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw13513 raw13513Labels = mixedMoment B raw13513step0 raw13513step0Labels := by
      have hz : ∀ j, raw13513 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13513step0 = (fun i j => raw13513 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13513step0 raw13513; decide +kernel
      have hl : raw13513step0Labels = raw13513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13513 raw13513Labels permutation346 hz
    mixedMoment B raw13513step0 raw13513step0Labels = mixedMoment B raw13513step1 raw13513step1Labels := by
      have ha : raw13513step1 = (fun i j => raw13513step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13513step1 raw13513step0; decide +kernel
      have hl : raw13513step1Labels = raw13513step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13513step0 raw13513step0Labels permutation33 permutation3
    _ = mixedMoment B node1237 node1237Labels := by rfl

def raw13514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13514Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13514step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13514 raw13514Labels = mixedMoment B node2882 node2882Labels := by
  calc
    mixedMoment B raw13514 raw13514Labels = mixedMoment B raw13514step0 raw13514step0Labels := by
      have hz : ∀ j, raw13514 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13514step0 = (fun i j => raw13514 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13514step0 raw13514; decide +kernel
      have hl : raw13514step0Labels = raw13514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13514 raw13514Labels permutation346 hz
    mixedMoment B raw13514step0 raw13514step0Labels = mixedMoment B raw13514step1 raw13514step1Labels := by
      have ha : raw13514step1 = (fun i j => raw13514step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13514step1 raw13514step0; decide +kernel
      have hl : raw13514step1Labels = raw13514step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13514step0 raw13514step0Labels permutation33 permutation3
    _ = mixedMoment B node2882 node2882Labels := by rfl

def raw13515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13515Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13515 raw13515Labels = mixedMoment B node2925 node2925Labels := by
  calc
    mixedMoment B raw13515 raw13515Labels = mixedMoment B raw13515step0 raw13515step0Labels := by
      have ha : raw13515step0 = (fun i j => raw13515 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13515step0 raw13515; decide +kernel
      have hl : raw13515step0Labels = raw13515Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13515 raw13515Labels permutation177 permutation3
    _ = mixedMoment B node2925 node2925Labels := by rfl

def raw13516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13516Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13516step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13516step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13516 raw13516Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw13516 raw13516Labels = mixedMoment B raw13516step0 raw13516step0Labels := by
      have hz : ∀ j, raw13516 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13516step0 = (fun i j => raw13516 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13516step0 raw13516; decide +kernel
      have hl : raw13516step0Labels = raw13516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13516 raw13516Labels permutation346 hz
    mixedMoment B raw13516step0 raw13516step0Labels = mixedMoment B raw13516step1 raw13516step1Labels := by
      have ha : raw13516step1 = (fun i j => raw13516step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13516step1 raw13516step0; decide +kernel
      have hl : raw13516step1Labels = raw13516step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13516step0 raw13516step0Labels permutation33 permutation3
    _ = mixedMoment B node3078 node3078Labels := by rfl

def raw13517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw13517Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw13517step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13517step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13517 raw13517Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw13517 raw13517Labels = mixedMoment B raw13517step0 raw13517step0Labels := by
      have hz : ∀ j, raw13517 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13517step0 = (fun i j => raw13517 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13517step0 raw13517; decide +kernel
      have hl : raw13517step0Labels = raw13517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13517 raw13517Labels permutation346 hz
    mixedMoment B raw13517step0 raw13517step0Labels = mixedMoment B raw13517step1 raw13517step1Labels := by
      have ha : raw13517step1 = (fun i j => raw13517step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13517step1 raw13517step0; decide +kernel
      have hl : raw13517step1Labels = raw13517step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13517step0 raw13517step0Labels permutation36 permutation3
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw13518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13518Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13518step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw13518step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13518 raw13518Labels = mixedMoment B node1234 node1234Labels := by
  calc
    mixedMoment B raw13518 raw13518Labels = mixedMoment B raw13518step0 raw13518step0Labels := by
      have hz : ∀ j, raw13518 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13518step0 = (fun i j => raw13518 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13518step0 raw13518; decide +kernel
      have hl : raw13518step0Labels = raw13518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13518 raw13518Labels permutation346 hz
    mixedMoment B raw13518step0 raw13518step0Labels = mixedMoment B raw13518step1 raw13518step1Labels := by
      have ha : raw13518step1 = (fun i j => raw13518step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13518step1 raw13518step0; decide +kernel
      have hl : raw13518step1Labels = raw13518step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13518step0 raw13518step0Labels permutation32 permutation3
    _ = mixedMoment B node1234 node1234Labels := by rfl

def raw13519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13519Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13519step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw13519step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13519 raw13519Labels = mixedMoment B node2879 node2879Labels := by
  calc
    mixedMoment B raw13519 raw13519Labels = mixedMoment B raw13519step0 raw13519step0Labels := by
      have hz : ∀ j, raw13519 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13519step0 = (fun i j => raw13519 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13519step0 raw13519; decide +kernel
      have hl : raw13519step0Labels = raw13519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13519 raw13519Labels permutation346 hz
    mixedMoment B raw13519step0 raw13519step0Labels = mixedMoment B raw13519step1 raw13519step1Labels := by
      have ha : raw13519step1 = (fun i j => raw13519step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13519step1 raw13519step0; decide +kernel
      have hl : raw13519step1Labels = raw13519step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13519step0 raw13519step0Labels permutation32 permutation3
    _ = mixedMoment B node2879 node2879Labels := by rfl

def raw13520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13520Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw13520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13520 raw13520Labels = mixedMoment B node2923 node2923Labels := by
  calc
    mixedMoment B raw13520 raw13520Labels = mixedMoment B raw13520step0 raw13520step0Labels := by
      have ha : raw13520step0 = (fun i j => raw13520 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13520step0 raw13520; decide +kernel
      have hl : raw13520step0Labels = raw13520Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13520 raw13520Labels permutation176 permutation3
    _ = mixedMoment B node2923 node2923Labels := by rfl

def raw13521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13521Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13521step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13521step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13521 raw13521Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw13521 raw13521Labels = mixedMoment B raw13521step0 raw13521step0Labels := by
      have hz : ∀ j, raw13521 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13521step0 = (fun i j => raw13521 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13521step0 raw13521; decide +kernel
      have hl : raw13521step0Labels = raw13521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13521 raw13521Labels permutation346 hz
    mixedMoment B raw13521step0 raw13521step0Labels = mixedMoment B raw13521step1 raw13521step1Labels := by
      have ha : raw13521step1 = (fun i j => raw13521step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13521step1 raw13521step0; decide +kernel
      have hl : raw13521step1Labels = raw13521step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13521step0 raw13521step0Labels permutation32 permutation3
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw13522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw13522Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw13522step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13522step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13522step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13522 raw13522Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw13522 raw13522Labels = mixedMoment B raw13522step0 raw13522step0Labels := by
      have hz : ∀ j, raw13522 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13522step0 = (fun i j => raw13522 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13522step0 raw13522; decide +kernel
      have hl : raw13522step0Labels = raw13522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13522 raw13522Labels permutation346 hz
    mixedMoment B raw13522step0 raw13522step0Labels = mixedMoment B raw13522step1 raw13522step1Labels := by
      have ha : raw13522step1 = (fun i j => raw13522step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13522step1 raw13522step0; decide +kernel
      have hl : raw13522step1Labels = raw13522step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13522step0 raw13522step0Labels permutation34 permutation3
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw13523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13523Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13523step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13523step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13523step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13523step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13523step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13523step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13523 raw13523Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw13523 raw13523Labels = mixedMoment B raw13523step0 raw13523step0Labels := by
      have hz : ∀ j, raw13523 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13523step0 = (fun i j => raw13523 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13523step0 raw13523; decide +kernel
      have hl : raw13523step0Labels = raw13523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13523 raw13523Labels permutation346 hz
    mixedMoment B raw13523step0 raw13523step0Labels = mixedMoment B raw13523step1 raw13523step1Labels := by
      have ha : raw13523step1 = (fun i j => raw13523step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13523step1 raw13523step0; decide +kernel
      have hl : raw13523step1Labels = raw13523step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13523step0 raw13523step0Labels permutation50 permutation7
    mixedMoment B raw13523step1 raw13523step1Labels = mixedMoment B raw13523step2 raw13523step2Labels := by
      have ha : raw13523step2 = -raw13523step1 := by apply Matrix.ext; change ∀ i j, raw13523step2 i j = -(raw13523step1 i j); unfold raw13523step2 raw13523step1; decide +kernel
      have hl : raw13523step2Labels = raw13523step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13523step2 raw13523step2Labels = mixedMoment B raw13523step3 raw13523step3Labels := by
      have ha : raw13523step3 = raw13523step2 := by apply Matrix.ext; unfold raw13523step3 raw13523step2; decide +kernel
      have hl : raw13523step2Labels = labelEmbedding1 ∘ raw13523step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13523step2 raw13523step2Labels raw13523step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3885 node3885Labels := by rfl

def raw13524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13524Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13524step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13524step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13524step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13524step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13524step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13524 raw13524Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw13524 raw13524Labels = mixedMoment B raw13524step0 raw13524step0Labels := by
      have ha : raw13524step0 = (fun i j => raw13524 (permutation252 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13524step0 raw13524; decide +kernel
      have hl : raw13524step0Labels = raw13524Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13524 raw13524Labels permutation252 permutation7
    mixedMoment B raw13524step0 raw13524step0Labels = mixedMoment B raw13524step1 raw13524step1Labels := by
      have ha : raw13524step1 = -raw13524step0 := by apply Matrix.ext; change ∀ i j, raw13524step1 i j = -(raw13524step0 i j); unfold raw13524step1 raw13524step0; decide +kernel
      have hl : raw13524step1Labels = raw13524step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13524step1 raw13524step1Labels = mixedMoment B raw13524step2 raw13524step2Labels := by
      have ha : raw13524step2 = raw13524step1 := by apply Matrix.ext; unfold raw13524step2 raw13524step1; decide +kernel
      have hl : raw13524step1Labels = labelEmbedding1 ∘ raw13524step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13524step1 raw13524step1Labels raw13524step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3875 node3875Labels := by rfl

def raw13525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13525Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13525step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13525step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13525step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13525step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13525step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13525step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13525step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13525 raw13525Labels = mixedMoment B node3887 node3887Labels := by
  calc
    mixedMoment B raw13525 raw13525Labels = mixedMoment B raw13525step0 raw13525step0Labels := by
      have hz : ∀ j, raw13525 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13525step0 = (fun i j => raw13525 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13525step0 raw13525; decide +kernel
      have hl : raw13525step0Labels = raw13525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13525 raw13525Labels permutation346 hz
    mixedMoment B raw13525step0 raw13525step0Labels = mixedMoment B raw13525step1 raw13525step1Labels := by
      have ha : raw13525step1 = (fun i j => raw13525step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13525step1 raw13525step0; decide +kernel
      have hl : raw13525step1Labels = raw13525step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13525step0 raw13525step0Labels permutation50 permutation7
    mixedMoment B raw13525step1 raw13525step1Labels = mixedMoment B raw13525step2 raw13525step2Labels := by
      have ha : raw13525step2 = -raw13525step1 := by apply Matrix.ext; change ∀ i j, raw13525step2 i j = -(raw13525step1 i j); unfold raw13525step2 raw13525step1; decide +kernel
      have hl : raw13525step2Labels = raw13525step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13525step2 raw13525step2Labels = mixedMoment B raw13525step3 raw13525step3Labels := by
      have ha : raw13525step3 = raw13525step2 := by apply Matrix.ext; unfold raw13525step3 raw13525step2; decide +kernel
      have hl : raw13525step2Labels = labelEmbedding1 ∘ raw13525step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13525step2 raw13525step2Labels raw13525step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3887 node3887Labels := by rfl

def raw13526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13526Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13526step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13526step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13526step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13526step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13526step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13526step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13526 raw13526Labels = mixedMoment B node3887 node3887Labels := by
  calc
    mixedMoment B raw13526 raw13526Labels = mixedMoment B raw13526step0 raw13526step0Labels := by
      have hz : ∀ j, raw13526 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13526step0 = (fun i j => raw13526 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13526step0 raw13526; decide +kernel
      have hl : raw13526step0Labels = raw13526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13526 raw13526Labels permutation346 hz
    mixedMoment B raw13526step0 raw13526step0Labels = mixedMoment B raw13526step1 raw13526step1Labels := by
      have ha : raw13526step1 = (fun i j => raw13526step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13526step1 raw13526step0; decide +kernel
      have hl : raw13526step1Labels = raw13526step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13526step0 raw13526step0Labels permutation51 permutation7
    mixedMoment B raw13526step1 raw13526step1Labels = mixedMoment B raw13526step2 raw13526step2Labels := by
      have ha : raw13526step2 = -raw13526step1 := by apply Matrix.ext; change ∀ i j, raw13526step2 i j = -(raw13526step1 i j); unfold raw13526step2 raw13526step1; decide +kernel
      have hl : raw13526step2Labels = raw13526step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13526step2 raw13526step2Labels = mixedMoment B raw13526step3 raw13526step3Labels := by
      have ha : raw13526step3 = raw13526step2 := by apply Matrix.ext; unfold raw13526step3 raw13526step2; decide +kernel
      have hl : raw13526step2Labels = labelEmbedding1 ∘ raw13526step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13526step2 raw13526step2Labels raw13526step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3887 node3887Labels := by rfl

def raw13527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13527Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13527step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13527step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13527step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13527step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13527step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13527step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13527step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13527 raw13527Labels = mixedMoment B node3859 node3859Labels := by
  calc
    mixedMoment B raw13527 raw13527Labels = mixedMoment B raw13527step0 raw13527step0Labels := by
      have hz : ∀ j, raw13527 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13527step0 = (fun i j => raw13527 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13527step0 raw13527; decide +kernel
      have hl : raw13527step0Labels = raw13527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13527 raw13527Labels permutation346 hz
    mixedMoment B raw13527step0 raw13527step0Labels = mixedMoment B raw13527step1 raw13527step1Labels := by
      have ha : raw13527step1 = (fun i j => raw13527step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13527step1 raw13527step0; decide +kernel
      have hl : raw13527step1Labels = raw13527step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13527step0 raw13527step0Labels permutation50 permutation7
    mixedMoment B raw13527step1 raw13527step1Labels = mixedMoment B raw13527step2 raw13527step2Labels := by
      have ha : raw13527step2 = -raw13527step1 := by apply Matrix.ext; change ∀ i j, raw13527step2 i j = -(raw13527step1 i j); unfold raw13527step2 raw13527step1; decide +kernel
      have hl : raw13527step2Labels = raw13527step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13527step2 raw13527step2Labels = mixedMoment B raw13527step3 raw13527step3Labels := by
      have ha : raw13527step3 = raw13527step2 := by apply Matrix.ext; unfold raw13527step3 raw13527step2; decide +kernel
      have hl : raw13527step2Labels = labelEmbedding1 ∘ raw13527step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13527step2 raw13527step2Labels raw13527step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3859 node3859Labels := by rfl

def raw13528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13528Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13528step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13528step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13528step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13528step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13528step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13528step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13528 raw13528Labels = mixedMoment B node3304 node3304Labels := by
  calc
    mixedMoment B raw13528 raw13528Labels = mixedMoment B raw13528step0 raw13528step0Labels := by
      have hz : ∀ j, raw13528 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13528step0 = (fun i j => raw13528 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13528step0 raw13528; decide +kernel
      have hl : raw13528step0Labels = raw13528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13528 raw13528Labels permutation346 hz
    mixedMoment B raw13528step0 raw13528step0Labels = mixedMoment B raw13528step1 raw13528step1Labels := by
      have ha : raw13528step1 = (fun i j => raw13528step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13528step1 raw13528step0; decide +kernel
      have hl : raw13528step1Labels = raw13528step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13528step0 raw13528step0Labels permutation50 permutation7
    mixedMoment B raw13528step1 raw13528step1Labels = mixedMoment B raw13528step2 raw13528step2Labels := by
      have ha : raw13528step2 = -raw13528step1 := by apply Matrix.ext; change ∀ i j, raw13528step2 i j = -(raw13528step1 i j); unfold raw13528step2 raw13528step1; decide +kernel
      have hl : raw13528step2Labels = raw13528step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13528step2 raw13528step2Labels = mixedMoment B raw13528step3 raw13528step3Labels := by
      have ha : raw13528step3 = raw13528step2 := by apply Matrix.ext; unfold raw13528step3 raw13528step2; decide +kernel
      have hl : raw13528step2Labels = labelEmbedding1 ∘ raw13528step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13528step2 raw13528step2Labels raw13528step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3304 node3304Labels := by rfl

def raw13529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13529Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13529step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13529step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13529step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13529step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13529step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13529 raw13529Labels = mixedMoment B node3563 node3563Labels := by
  calc
    mixedMoment B raw13529 raw13529Labels = mixedMoment B raw13529step0 raw13529step0Labels := by
      have ha : raw13529step0 = (fun i j => raw13529 (permutation252 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13529step0 raw13529; decide +kernel
      have hl : raw13529step0Labels = raw13529Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13529 raw13529Labels permutation252 permutation7
    mixedMoment B raw13529step0 raw13529step0Labels = mixedMoment B raw13529step1 raw13529step1Labels := by
      have ha : raw13529step1 = -raw13529step0 := by apply Matrix.ext; change ∀ i j, raw13529step1 i j = -(raw13529step0 i j); unfold raw13529step1 raw13529step0; decide +kernel
      have hl : raw13529step1Labels = raw13529step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13529step1 raw13529step1Labels = mixedMoment B raw13529step2 raw13529step2Labels := by
      have ha : raw13529step2 = raw13529step1 := by apply Matrix.ext; unfold raw13529step2 raw13529step1; decide +kernel
      have hl : raw13529step1Labels = labelEmbedding1 ∘ raw13529step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13529step1 raw13529step1Labels raw13529step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3563 node3563Labels := by rfl

def raw13530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13530Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13530step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13530step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13530step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13530step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13530step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13530step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13530 raw13530Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw13530 raw13530Labels = mixedMoment B raw13530step0 raw13530step0Labels := by
      have hz : ∀ j, raw13530 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13530step0 = (fun i j => raw13530 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13530step0 raw13530; decide +kernel
      have hl : raw13530step0Labels = raw13530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13530 raw13530Labels permutation346 hz
    mixedMoment B raw13530step0 raw13530step0Labels = mixedMoment B raw13530step1 raw13530step1Labels := by
      have ha : raw13530step1 = (fun i j => raw13530step0 (permutation52 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13530step1 raw13530step0; decide +kernel
      have hl : raw13530step1Labels = raw13530step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13530step0 raw13530step0Labels permutation52 permutation7
    mixedMoment B raw13530step1 raw13530step1Labels = mixedMoment B raw13530step2 raw13530step2Labels := by
      have ha : raw13530step2 = -raw13530step1 := by apply Matrix.ext; change ∀ i j, raw13530step2 i j = -(raw13530step1 i j); unfold raw13530step2 raw13530step1; decide +kernel
      have hl : raw13530step2Labels = raw13530step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13530step2 raw13530step2Labels = mixedMoment B raw13530step3 raw13530step3Labels := by
      have ha : raw13530step3 = raw13530step2 := by apply Matrix.ext; unfold raw13530step3 raw13530step2; decide +kernel
      have hl : raw13530step2Labels = labelEmbedding1 ∘ raw13530step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13530step2 raw13530step2Labels raw13530step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

def raw13531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13531Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13531step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13531step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13531step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13531step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13531step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13531step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13531 raw13531Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw13531 raw13531Labels = mixedMoment B raw13531step0 raw13531step0Labels := by
      have hz : ∀ j, raw13531 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13531step0 = (fun i j => raw13531 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13531step0 raw13531; decide +kernel
      have hl : raw13531step0Labels = raw13531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13531 raw13531Labels permutation346 hz
    mixedMoment B raw13531step0 raw13531step0Labels = mixedMoment B raw13531step1 raw13531step1Labels := by
      have ha : raw13531step1 = (fun i j => raw13531step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13531step1 raw13531step0; decide +kernel
      have hl : raw13531step1Labels = raw13531step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13531step0 raw13531step0Labels permutation54 permutation7
    mixedMoment B raw13531step1 raw13531step1Labels = mixedMoment B raw13531step2 raw13531step2Labels := by
      have ha : raw13531step2 = -raw13531step1 := by apply Matrix.ext; change ∀ i j, raw13531step2 i j = -(raw13531step1 i j); unfold raw13531step2 raw13531step1; decide +kernel
      have hl : raw13531step2Labels = raw13531step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13531step2 raw13531step2Labels = mixedMoment B raw13531step3 raw13531step3Labels := by
      have ha : raw13531step3 = raw13531step2 := by apply Matrix.ext; unfold raw13531step3 raw13531step2; decide +kernel
      have hl : raw13531step2Labels = labelEmbedding1 ∘ raw13531step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13531step2 raw13531step2Labels raw13531step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

def raw13532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13532Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13532step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13532step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13532step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13532step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13532step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13532step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13532 raw13532Labels = mixedMoment B node3546 node3546Labels := by
  calc
    mixedMoment B raw13532 raw13532Labels = mixedMoment B raw13532step0 raw13532step0Labels := by
      have hz : ∀ j, raw13532 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13532step0 = (fun i j => raw13532 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13532step0 raw13532; decide +kernel
      have hl : raw13532step0Labels = raw13532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13532 raw13532Labels permutation346 hz
    mixedMoment B raw13532step0 raw13532step0Labels = mixedMoment B raw13532step1 raw13532step1Labels := by
      have ha : raw13532step1 = (fun i j => raw13532step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13532step1 raw13532step0; decide +kernel
      have hl : raw13532step1Labels = raw13532step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13532step0 raw13532step0Labels permutation50 permutation7
    mixedMoment B raw13532step1 raw13532step1Labels = mixedMoment B raw13532step2 raw13532step2Labels := by
      have ha : raw13532step2 = -raw13532step1 := by apply Matrix.ext; change ∀ i j, raw13532step2 i j = -(raw13532step1 i j); unfold raw13532step2 raw13532step1; decide +kernel
      have hl : raw13532step2Labels = raw13532step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13532step2 raw13532step2Labels = mixedMoment B raw13532step3 raw13532step3Labels := by
      have ha : raw13532step3 = raw13532step2 := by apply Matrix.ext; unfold raw13532step3 raw13532step2; decide +kernel
      have hl : raw13532step2Labels = labelEmbedding1 ∘ raw13532step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13532step2 raw13532step2Labels raw13532step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3546 node3546Labels := by rfl

def raw13533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13533Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13533step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13533step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13533step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13533step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13533step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13533 raw13533Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw13533 raw13533Labels = mixedMoment B raw13533step0 raw13533step0Labels := by
      have ha : raw13533step0 = (fun i j => raw13533 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13533step0 raw13533; decide +kernel
      have hl : raw13533step0Labels = raw13533Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13533 raw13533Labels permutation160 permutation5
    mixedMoment B raw13533step0 raw13533step0Labels = mixedMoment B raw13533step1 raw13533step1Labels := by
      have ha : raw13533step1 = -raw13533step0 := by apply Matrix.ext; change ∀ i j, raw13533step1 i j = -(raw13533step0 i j); unfold raw13533step1 raw13533step0; decide +kernel
      have hl : raw13533step1Labels = raw13533step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13533step1 raw13533step1Labels = mixedMoment B raw13533step2 raw13533step2Labels := by
      have ha : raw13533step2 = raw13533step1 := by apply Matrix.ext; unfold raw13533step2 raw13533step1; decide +kernel
      have hl : raw13533step1Labels = labelEmbedding1 ∘ raw13533step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13533step1 raw13533step1Labels raw13533step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

def raw13534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13534Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13534step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13534step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13534step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13534step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13534step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13534 raw13534Labels = mixedMoment B node3569 node3569Labels := by
  calc
    mixedMoment B raw13534 raw13534Labels = mixedMoment B raw13534step0 raw13534step0Labels := by
      have ha : raw13534step0 = (fun i j => raw13534 (permutation252 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13534step0 raw13534; decide +kernel
      have hl : raw13534step0Labels = raw13534Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13534 raw13534Labels permutation252 permutation7
    mixedMoment B raw13534step0 raw13534step0Labels = mixedMoment B raw13534step1 raw13534step1Labels := by
      have ha : raw13534step1 = -raw13534step0 := by apply Matrix.ext; change ∀ i j, raw13534step1 i j = -(raw13534step0 i j); unfold raw13534step1 raw13534step0; decide +kernel
      have hl : raw13534step1Labels = raw13534step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13534step1 raw13534step1Labels = mixedMoment B raw13534step2 raw13534step2Labels := by
      have ha : raw13534step2 = raw13534step1 := by apply Matrix.ext; unfold raw13534step2 raw13534step1; decide +kernel
      have hl : raw13534step1Labels = labelEmbedding1 ∘ raw13534step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13534step1 raw13534step1Labels raw13534step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3569 node3569Labels := by rfl

def raw13535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13535Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13535step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13535step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13535step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13535step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13535step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13535 raw13535Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw13535 raw13535Labels = mixedMoment B raw13535step0 raw13535step0Labels := by
      have ha : raw13535step0 = (fun i j => raw13535 (permutation252 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13535step0 raw13535; decide +kernel
      have hl : raw13535step0Labels = raw13535Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13535 raw13535Labels permutation252 permutation7
    mixedMoment B raw13535step0 raw13535step0Labels = mixedMoment B raw13535step1 raw13535step1Labels := by
      have ha : raw13535step1 = -raw13535step0 := by apply Matrix.ext; change ∀ i j, raw13535step1 i j = -(raw13535step0 i j); unfold raw13535step1 raw13535step0; decide +kernel
      have hl : raw13535step1Labels = raw13535step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13535step1 raw13535step1Labels = mixedMoment B raw13535step2 raw13535step2Labels := by
      have ha : raw13535step2 = raw13535step1 := by apply Matrix.ext; unfold raw13535step2 raw13535step1; decide +kernel
      have hl : raw13535step1Labels = labelEmbedding1 ∘ raw13535step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13535step1 raw13535step1Labels raw13535step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3571 node3571Labels := by rfl

def raw13536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13536Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13536step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13536step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13536step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13536step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13536step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13536 raw13536Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw13536 raw13536Labels = mixedMoment B raw13536step0 raw13536step0Labels := by
      have ha : raw13536step0 = (fun i j => raw13536 (permutation253 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13536step0 raw13536; decide +kernel
      have hl : raw13536step0Labels = raw13536Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13536 raw13536Labels permutation253 permutation7
    mixedMoment B raw13536step0 raw13536step0Labels = mixedMoment B raw13536step1 raw13536step1Labels := by
      have ha : raw13536step1 = -raw13536step0 := by apply Matrix.ext; change ∀ i j, raw13536step1 i j = -(raw13536step0 i j); unfold raw13536step1 raw13536step0; decide +kernel
      have hl : raw13536step1Labels = raw13536step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13536step1 raw13536step1Labels = mixedMoment B raw13536step2 raw13536step2Labels := by
      have ha : raw13536step2 = raw13536step1 := by apply Matrix.ext; unfold raw13536step2 raw13536step1; decide +kernel
      have hl : raw13536step1Labels = labelEmbedding1 ∘ raw13536step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13536step1 raw13536step1Labels raw13536step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3571 node3571Labels := by rfl

def raw13537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13537Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13537step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13537step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13537step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13537step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13537step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13537 raw13537Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw13537 raw13537Labels = mixedMoment B raw13537step0 raw13537step0Labels := by
      have ha : raw13537step0 = (fun i j => raw13537 (permutation252 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13537step0 raw13537; decide +kernel
      have hl : raw13537step0Labels = raw13537Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13537 raw13537Labels permutation252 permutation7
    mixedMoment B raw13537step0 raw13537step0Labels = mixedMoment B raw13537step1 raw13537step1Labels := by
      have ha : raw13537step1 = -raw13537step0 := by apply Matrix.ext; change ∀ i j, raw13537step1 i j = -(raw13537step0 i j); unfold raw13537step1 raw13537step0; decide +kernel
      have hl : raw13537step1Labels = raw13537step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13537step1 raw13537step1Labels = mixedMoment B raw13537step2 raw13537step2Labels := by
      have ha : raw13537step2 = raw13537step1 := by apply Matrix.ext; unfold raw13537step2 raw13537step1; decide +kernel
      have hl : raw13537step1Labels = labelEmbedding1 ∘ raw13537step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13537step1 raw13537step1Labels raw13537step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

def raw13538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13538Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13538step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw13538step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13538step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw13538step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13538step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw13538step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13538 raw13538Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw13538 raw13538Labels = mixedMoment B raw13538step0 raw13538step0Labels := by
      have hz : ∀ j, raw13538 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13538step0 = (fun i j => raw13538 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13538step0 raw13538; decide +kernel
      have hl : raw13538step0Labels = raw13538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13538 raw13538Labels permutation346 hz
    mixedMoment B raw13538step0 raw13538step0Labels = mixedMoment B raw13538step1 raw13538step1Labels := by
      have ha : raw13538step1 = (fun i j => raw13538step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13538step1 raw13538step0; decide +kernel
      have hl : raw13538step1Labels = raw13538step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13538step0 raw13538step0Labels permutation34 permutation5
    mixedMoment B raw13538step1 raw13538step1Labels = mixedMoment B raw13538step2 raw13538step2Labels := by
      have ha : raw13538step2 = -raw13538step1 := by apply Matrix.ext; change ∀ i j, raw13538step2 i j = -(raw13538step1 i j); unfold raw13538step2 raw13538step1; decide +kernel
      have hl : raw13538step2Labels = raw13538step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13538step2 raw13538step2Labels = mixedMoment B raw13538step3 raw13538step3Labels := by
      have ha : raw13538step3 = raw13538step2 := by apply Matrix.ext; unfold raw13538step3 raw13538step2; decide +kernel
      have hl : raw13538step2Labels = labelEmbedding1 ∘ raw13538step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13538step2 raw13538step2Labels raw13538step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

def raw13539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13539Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13539step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw13539step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13539step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13539step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13539step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13539step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13539 raw13539Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw13539 raw13539Labels = mixedMoment B raw13539step0 raw13539step0Labels := by
      have hz : ∀ j, raw13539 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13539step0 = (fun i j => raw13539 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13539step0 raw13539; decide +kernel
      have hl : raw13539step0Labels = raw13539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13539 raw13539Labels permutation346 hz
    mixedMoment B raw13539step0 raw13539step0Labels = mixedMoment B raw13539step1 raw13539step1Labels := by
      have ha : raw13539step1 = (fun i j => raw13539step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13539step1 raw13539step0; decide +kernel
      have hl : raw13539step1Labels = raw13539step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13539step0 raw13539step0Labels permutation51 permutation7
    mixedMoment B raw13539step1 raw13539step1Labels = mixedMoment B raw13539step2 raw13539step2Labels := by
      have ha : raw13539step2 = -raw13539step1 := by apply Matrix.ext; change ∀ i j, raw13539step2 i j = -(raw13539step1 i j); unfold raw13539step2 raw13539step1; decide +kernel
      have hl : raw13539step2Labels = raw13539step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13539step2 raw13539step2Labels = mixedMoment B raw13539step3 raw13539step3Labels := by
      have ha : raw13539step3 = raw13539step2 := by apply Matrix.ext; unfold raw13539step3 raw13539step2; decide +kernel
      have hl : raw13539step2Labels = labelEmbedding1 ∘ raw13539step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13539step2 raw13539step2Labels raw13539step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

def raw13540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13540Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13540step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13540step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13540step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13540step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13540step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13540 raw13540Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw13540 raw13540Labels = mixedMoment B raw13540step0 raw13540step0Labels := by
      have ha : raw13540step0 = (fun i j => raw13540 (permutation253 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13540step0 raw13540; decide +kernel
      have hl : raw13540step0Labels = raw13540Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13540 raw13540Labels permutation253 permutation7
    mixedMoment B raw13540step0 raw13540step0Labels = mixedMoment B raw13540step1 raw13540step1Labels := by
      have ha : raw13540step1 = -raw13540step0 := by apply Matrix.ext; change ∀ i j, raw13540step1 i j = -(raw13540step0 i j); unfold raw13540step1 raw13540step0; decide +kernel
      have hl : raw13540step1Labels = raw13540step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13540step1 raw13540step1Labels = mixedMoment B raw13540step2 raw13540step2Labels := by
      have ha : raw13540step2 = raw13540step1 := by apply Matrix.ext; unfold raw13540step2 raw13540step1; decide +kernel
      have hl : raw13540step1Labels = labelEmbedding1 ∘ raw13540step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13540step1 raw13540step1Labels raw13540step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

def raw13541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13541Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13541step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw13541step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13541step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13541step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13541step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13541step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13541 raw13541Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw13541 raw13541Labels = mixedMoment B raw13541step0 raw13541step0Labels := by
      have hz : ∀ j, raw13541 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13541step0 = (fun i j => raw13541 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13541step0 raw13541; decide +kernel
      have hl : raw13541step0Labels = raw13541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13541 raw13541Labels permutation346 hz
    mixedMoment B raw13541step0 raw13541step0Labels = mixedMoment B raw13541step1 raw13541step1Labels := by
      have ha : raw13541step1 = (fun i j => raw13541step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13541step1 raw13541step0; decide +kernel
      have hl : raw13541step1Labels = raw13541step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13541step0 raw13541step0Labels permutation51 permutation7
    mixedMoment B raw13541step1 raw13541step1Labels = mixedMoment B raw13541step2 raw13541step2Labels := by
      have ha : raw13541step2 = -raw13541step1 := by apply Matrix.ext; change ∀ i j, raw13541step2 i j = -(raw13541step1 i j); unfold raw13541step2 raw13541step1; decide +kernel
      have hl : raw13541step2Labels = raw13541step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13541step2 raw13541step2Labels = mixedMoment B raw13541step3 raw13541step3Labels := by
      have ha : raw13541step3 = raw13541step2 := by apply Matrix.ext; unfold raw13541step3 raw13541step2; decide +kernel
      have hl : raw13541step2Labels = labelEmbedding1 ∘ raw13541step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13541step2 raw13541step2Labels raw13541step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3580 node3580Labels := by rfl

def raw13542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13542Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13542step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13542step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13542step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13542step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13542step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13542step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13542 raw13542Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw13542 raw13542Labels = mixedMoment B raw13542step0 raw13542step0Labels := by
      have hz : ∀ j, raw13542 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13542step0 = (fun i j => raw13542 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13542step0 raw13542; decide +kernel
      have hl : raw13542step0Labels = raw13542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13542 raw13542Labels permutation346 hz
    mixedMoment B raw13542step0 raw13542step0Labels = mixedMoment B raw13542step1 raw13542step1Labels := by
      have ha : raw13542step1 = (fun i j => raw13542step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13542step1 raw13542step0; decide +kernel
      have hl : raw13542step1Labels = raw13542step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13542step0 raw13542step0Labels permutation51 permutation7
    mixedMoment B raw13542step1 raw13542step1Labels = mixedMoment B raw13542step2 raw13542step2Labels := by
      have ha : raw13542step2 = -raw13542step1 := by apply Matrix.ext; change ∀ i j, raw13542step2 i j = -(raw13542step1 i j); unfold raw13542step2 raw13542step1; decide +kernel
      have hl : raw13542step2Labels = raw13542step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13542step2 raw13542step2Labels = mixedMoment B raw13542step3 raw13542step3Labels := by
      have ha : raw13542step3 = raw13542step2 := by apply Matrix.ext; unfold raw13542step3 raw13542step2; decide +kernel
      have hl : raw13542step2Labels = labelEmbedding1 ∘ raw13542step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13542step2 raw13542step2Labels raw13542step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw13543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13543Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13543step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw13543step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw13543step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13543step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw13543step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13543 raw13543Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw13543 raw13543Labels = mixedMoment B raw13543step0 raw13543step0Labels := by
      have hz : ∀ j, raw13543 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13543step0 = (fun i j => raw13543 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13543step0 raw13543; decide +kernel
      have hl : raw13543step0Labels = raw13543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13543 raw13543Labels permutation346 hz
    mixedMoment B raw13543step0 raw13543step0Labels = mixedMoment B raw13543step1 raw13543step1Labels := by
      have ha : raw13543step1 = (fun i j => raw13543step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13543step1 raw13543step0; decide +kernel
      have hl : raw13543step1Labels = raw13543step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13543step0 raw13543step0Labels permutation32 permutation5
    mixedMoment B raw13543step1 raw13543step1Labels = mixedMoment B raw13543step2 raw13543step2Labels := by
      have ha : raw13543step2 = -raw13543step1 := by apply Matrix.ext; change ∀ i j, raw13543step2 i j = -(raw13543step1 i j); unfold raw13543step2 raw13543step1; decide +kernel
      have hl : raw13543step2Labels = raw13543step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13543step2 raw13543step2Labels = mixedMoment B raw13543step3 raw13543step3Labels := by
      have ha : raw13543step3 = raw13543step2 := by apply Matrix.ext; unfold raw13543step3 raw13543step2; decide +kernel
      have hl : raw13543step2Labels = labelEmbedding1 ∘ raw13543step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13543step2 raw13543step2Labels raw13543step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

def raw13544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13544Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13544step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw13544step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13544step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13544step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13544step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13544step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13544 raw13544Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw13544 raw13544Labels = mixedMoment B raw13544step0 raw13544step0Labels := by
      have hz : ∀ j, raw13544 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13544step0 = (fun i j => raw13544 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13544step0 raw13544; decide +kernel
      have hl : raw13544step0Labels = raw13544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13544 raw13544Labels permutation346 hz
    mixedMoment B raw13544step0 raw13544step0Labels = mixedMoment B raw13544step1 raw13544step1Labels := by
      have ha : raw13544step1 = (fun i j => raw13544step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13544step1 raw13544step0; decide +kernel
      have hl : raw13544step1Labels = raw13544step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13544step0 raw13544step0Labels permutation50 permutation7
    mixedMoment B raw13544step1 raw13544step1Labels = mixedMoment B raw13544step2 raw13544step2Labels := by
      have ha : raw13544step2 = -raw13544step1 := by apply Matrix.ext; change ∀ i j, raw13544step2 i j = -(raw13544step1 i j); unfold raw13544step2 raw13544step1; decide +kernel
      have hl : raw13544step2Labels = raw13544step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13544step2 raw13544step2Labels = mixedMoment B raw13544step3 raw13544step3Labels := by
      have ha : raw13544step3 = raw13544step2 := by apply Matrix.ext; unfold raw13544step3 raw13544step2; decide +kernel
      have hl : raw13544step2Labels = labelEmbedding1 ∘ raw13544step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13544step2 raw13544step2Labels raw13544step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

def raw13545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13545Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13545step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13545step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13545step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13545step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13545 raw13545Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw13545 raw13545Labels = mixedMoment B raw13545step0 raw13545step0Labels := by
      have ha : raw13545step0 = (fun i j => raw13545 (permutation252 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13545step0 raw13545; decide +kernel
      have hl : raw13545step0Labels = raw13545Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13545 raw13545Labels permutation252 permutation7
    mixedMoment B raw13545step0 raw13545step0Labels = mixedMoment B raw13545step1 raw13545step1Labels := by
      have ha : raw13545step1 = -raw13545step0 := by apply Matrix.ext; change ∀ i j, raw13545step1 i j = -(raw13545step0 i j); unfold raw13545step1 raw13545step0; decide +kernel
      have hl : raw13545step1Labels = raw13545step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13545step1 raw13545step1Labels = mixedMoment B raw13545step2 raw13545step2Labels := by
      have ha : raw13545step2 = raw13545step1 := by apply Matrix.ext; unfold raw13545step2 raw13545step1; decide +kernel
      have hl : raw13545step1Labels = labelEmbedding1 ∘ raw13545step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13545step1 raw13545step1Labels raw13545step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

def raw13546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13546Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13546step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13546step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw13546step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13546step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13546step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13546step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13546step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13546 raw13546Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw13546 raw13546Labels = mixedMoment B raw13546step0 raw13546step0Labels := by
      have hz : ∀ j, raw13546 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13546step0 = (fun i j => raw13546 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13546step0 raw13546; decide +kernel
      have hl : raw13546step0Labels = raw13546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13546 raw13546Labels permutation346 hz
    mixedMoment B raw13546step0 raw13546step0Labels = mixedMoment B raw13546step1 raw13546step1Labels := by
      have ha : raw13546step1 = (fun i j => raw13546step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13546step1 raw13546step0; decide +kernel
      have hl : raw13546step1Labels = raw13546step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13546step0 raw13546step0Labels permutation50 permutation7
    mixedMoment B raw13546step1 raw13546step1Labels = mixedMoment B raw13546step2 raw13546step2Labels := by
      have ha : raw13546step2 = -raw13546step1 := by apply Matrix.ext; change ∀ i j, raw13546step2 i j = -(raw13546step1 i j); unfold raw13546step2 raw13546step1; decide +kernel
      have hl : raw13546step2Labels = raw13546step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13546step2 raw13546step2Labels = mixedMoment B raw13546step3 raw13546step3Labels := by
      have ha : raw13546step3 = raw13546step2 := by apply Matrix.ext; unfold raw13546step3 raw13546step2; decide +kernel
      have hl : raw13546step2Labels = labelEmbedding1 ∘ raw13546step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13546step2 raw13546step2Labels raw13546step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3580 node3580Labels := by rfl

def raw13547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw13547Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw13547step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13547step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13547step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13547step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13547step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13547step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13547step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13547 raw13547Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw13547 raw13547Labels = mixedMoment B raw13547step0 raw13547step0Labels := by
      have hz : ∀ j, raw13547 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13547step0 = (fun i j => raw13547 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13547step0 raw13547; decide +kernel
      have hl : raw13547step0Labels = raw13547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13547 raw13547Labels permutation346 hz
    mixedMoment B raw13547step0 raw13547step0Labels = mixedMoment B raw13547step1 raw13547step1Labels := by
      have ha : raw13547step1 = (fun i j => raw13547step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13547step1 raw13547step0; decide +kernel
      have hl : raw13547step1Labels = raw13547step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13547step0 raw13547step0Labels permutation50 permutation7
    mixedMoment B raw13547step1 raw13547step1Labels = mixedMoment B raw13547step2 raw13547step2Labels := by
      have ha : raw13547step2 = -raw13547step1 := by apply Matrix.ext; change ∀ i j, raw13547step2 i j = -(raw13547step1 i j); unfold raw13547step2 raw13547step1; decide +kernel
      have hl : raw13547step2Labels = raw13547step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13547step2 raw13547step2Labels = mixedMoment B raw13547step3 raw13547step3Labels := by
      have ha : raw13547step3 = raw13547step2 := by apply Matrix.ext; unfold raw13547step3 raw13547step2; decide +kernel
      have hl : raw13547step2Labels = labelEmbedding1 ∘ raw13547step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13547step2 raw13547step2Labels raw13547step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw13548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13548Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13548step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13548step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw13548step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13548step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw13548step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13548 raw13548Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw13548 raw13548Labels = mixedMoment B raw13548step0 raw13548step0Labels := by
      have hz : ∀ j, raw13548 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13548step0 = (fun i j => raw13548 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13548step0 raw13548; decide +kernel
      have hl : raw13548step0Labels = raw13548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13548 raw13548Labels permutation346 hz
    mixedMoment B raw13548step0 raw13548step0Labels = mixedMoment B raw13548step1 raw13548step1Labels := by
      have ha : raw13548step1 = (fun i j => raw13548step0 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13548step1 raw13548step0; decide +kernel
      have hl : raw13548step1Labels = raw13548step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13548step0 raw13548step0Labels permutation145 permutation5
    mixedMoment B raw13548step1 raw13548step1Labels = mixedMoment B raw13548step2 raw13548step2Labels := by
      have ha : raw13548step2 = raw13548step1 := by apply Matrix.ext; unfold raw13548step2 raw13548step1; decide +kernel
      have hl : raw13548step1Labels = labelEmbedding1 ∘ raw13548step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13548step1 raw13548step1Labels raw13548step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2702 node2702Labels := by rfl

def raw13549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13549Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13549step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw13549step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13549step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw13549step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13549 raw13549Labels = mixedMoment B node2706 node2706Labels := by
  calc
    mixedMoment B raw13549 raw13549Labels = mixedMoment B raw13549step0 raw13549step0Labels := by
      have hz : ∀ j, raw13549 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13549step0 = (fun i j => raw13549 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13549step0 raw13549; decide +kernel
      have hl : raw13549step0Labels = raw13549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13549 raw13549Labels permutation346 hz
    mixedMoment B raw13549step0 raw13549step0Labels = mixedMoment B raw13549step1 raw13549step1Labels := by
      have ha : raw13549step1 = (fun i j => raw13549step0 (permutation144 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13549step1 raw13549step0; decide +kernel
      have hl : raw13549step1Labels = raw13549step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13549step0 raw13549step0Labels permutation144 permutation5
    mixedMoment B raw13549step1 raw13549step1Labels = mixedMoment B raw13549step2 raw13549step2Labels := by
      have ha : raw13549step2 = raw13549step1 := by apply Matrix.ext; unfold raw13549step2 raw13549step1; decide +kernel
      have hl : raw13549step1Labels = labelEmbedding1 ∘ raw13549step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13549step1 raw13549step1Labels raw13549step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2706 node2706Labels := by rfl

def raw13550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13550Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw13550step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13550step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw13550step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13550 raw13550Labels = mixedMoment B node2700 node2700Labels := by
  calc
    mixedMoment B raw13550 raw13550Labels = mixedMoment B raw13550step0 raw13550step0Labels := by
      have ha : raw13550step0 = (fun i j => raw13550 (permutation662 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13550step0 raw13550; decide +kernel
      have hl : raw13550step0Labels = raw13550Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13550 raw13550Labels permutation662 permutation5
    mixedMoment B raw13550step0 raw13550step0Labels = mixedMoment B raw13550step1 raw13550step1Labels := by
      have ha : raw13550step1 = raw13550step0 := by apply Matrix.ext; unfold raw13550step1 raw13550step0; decide +kernel
      have hl : raw13550step0Labels = labelEmbedding1 ∘ raw13550step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13550step0 raw13550step0Labels raw13550step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2700 node2700Labels := by rfl

def raw13551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13551Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13551step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13551step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13551step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13551step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13551step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13551 raw13551Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw13551 raw13551Labels = mixedMoment B raw13551step0 raw13551step0Labels := by
      have hz : ∀ j, raw13551 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13551step0 = (fun i j => raw13551 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13551step0 raw13551; decide +kernel
      have hl : raw13551step0Labels = raw13551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13551 raw13551Labels permutation346 hz
    mixedMoment B raw13551step0 raw13551step0Labels = mixedMoment B raw13551step1 raw13551step1Labels := by
      have ha : raw13551step1 = (fun i j => raw13551step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13551step1 raw13551step0; decide +kernel
      have hl : raw13551step1Labels = raw13551step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13551step0 raw13551step0Labels permutation149 permutation5
    mixedMoment B raw13551step1 raw13551step1Labels = mixedMoment B raw13551step2 raw13551step2Labels := by
      have ha : raw13551step2 = raw13551step1 := by apply Matrix.ext; unfold raw13551step2 raw13551step1; decide +kernel
      have hl : raw13551step1Labels = labelEmbedding1 ∘ raw13551step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13551step1 raw13551step1Labels raw13551step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2738 node2738Labels := by rfl

def raw13552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw13552Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw13552step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13552step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13552step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13552 raw13552Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw13552 raw13552Labels = mixedMoment B raw13552step0 raw13552step0Labels := by
      have hz : ∀ j, raw13552 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13552step0 = (fun i j => raw13552 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13552step0 raw13552; decide +kernel
      have hl : raw13552step0Labels = raw13552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13552 raw13552Labels permutation346 hz
    mixedMoment B raw13552step0 raw13552step0Labels = mixedMoment B raw13552step1 raw13552step1Labels := by
      have ha : raw13552step1 = (fun i j => raw13552step0 (permutation143 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13552step1 raw13552step0; decide +kernel
      have hl : raw13552step1Labels = raw13552step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13552step0 raw13552step0Labels permutation143 permutation5
    mixedMoment B raw13552step1 raw13552step1Labels = mixedMoment B raw13552step2 raw13552step2Labels := by
      have ha : raw13552step2 = raw13552step1 := by apply Matrix.ext; unfold raw13552step2 raw13552step1; decide +kernel
      have hl : raw13552step1Labels = labelEmbedding1 ∘ raw13552step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13552step1 raw13552step1Labels raw13552step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2738 node2738Labels := by rfl

def raw13553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13553Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13553step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13553 raw13553Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw13553 raw13553Labels = mixedMoment B raw13553step0 raw13553step0Labels := by
      have hz : ∀ j, raw13553 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13553step0 = (fun i j => raw13553 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13553step0 raw13553; decide +kernel
      have hl : raw13553step0Labels = raw13553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13553 raw13553Labels permutation346 hz
    mixedMoment B raw13553step0 raw13553step0Labels = mixedMoment B raw13553step1 raw13553step1Labels := by
      have ha : raw13553step1 = (fun i j => raw13553step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13553step1 raw13553step0; decide +kernel
      have hl : raw13553step1Labels = raw13553step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13553step0 raw13553step0Labels permutation36 permutation2
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw13554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13554step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13554 raw13554Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw13554 raw13554Labels = mixedMoment B raw13554step0 raw13554step0Labels := by
      have hz : ∀ j, raw13554 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13554step0 = (fun i j => raw13554 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13554step0 raw13554; decide +kernel
      have hl : raw13554step0Labels = raw13554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13554 raw13554Labels permutation346 hz
    mixedMoment B raw13554step0 raw13554step0Labels = mixedMoment B raw13554step1 raw13554step1Labels := by
      have ha : raw13554step1 = (fun i j => raw13554step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13554step1 raw13554step0; decide +kernel
      have hl : raw13554step1Labels = raw13554step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13554step0 raw13554step0Labels permutation36 permutation2
    _ = mixedMoment B node3885 node3885Labels := by rfl

def raw13555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13555 raw13555Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw13555 raw13555Labels = mixedMoment B raw13555step0 raw13555step0Labels := by
      have ha : raw13555step0 = (fun i j => raw13555 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13555step0 raw13555; decide +kernel
      have hl : raw13555step0Labels = raw13555Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13555 raw13555Labels permutation180 permutation2
    _ = mixedMoment B node3849 node3849Labels := by rfl

def raw13556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13556step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13556step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13556 raw13556Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw13556 raw13556Labels = mixedMoment B raw13556step0 raw13556step0Labels := by
      have hz : ∀ j, raw13556 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13556step0 = (fun i j => raw13556 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13556step0 raw13556; decide +kernel
      have hl : raw13556step0Labels = raw13556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13556 raw13556Labels permutation346 hz
    mixedMoment B raw13556step0 raw13556step0Labels = mixedMoment B raw13556step1 raw13556step1Labels := by
      have ha : raw13556step1 = (fun i j => raw13556step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13556step1 raw13556step0; decide +kernel
      have hl : raw13556step1Labels = raw13556step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13556step0 raw13556step0Labels permutation33 permutation2
    _ = mixedMoment B node3910 node3910Labels := by rfl

def raw13557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13557step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13557step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13557 raw13557Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw13557 raw13557Labels = mixedMoment B raw13557step0 raw13557step0Labels := by
      have hz : ∀ j, raw13557 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13557step0 = (fun i j => raw13557 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13557step0 raw13557; decide +kernel
      have hl : raw13557step0Labels = raw13557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13557 raw13557Labels permutation346 hz
    mixedMoment B raw13557step0 raw13557step0Labels = mixedMoment B raw13557step1 raw13557step1Labels := by
      have ha : raw13557step1 = (fun i j => raw13557step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13557step1 raw13557step0; decide +kernel
      have hl : raw13557step1Labels = raw13557step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13557step0 raw13557step0Labels permutation35 permutation2
    _ = mixedMoment B node3910 node3910Labels := by rfl

def raw13558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw13558step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13558 raw13558Labels = mixedMoment B node3904 node3904Labels := by
  calc
    mixedMoment B raw13558 raw13558Labels = mixedMoment B raw13558step0 raw13558step0Labels := by
      have hz : ∀ j, raw13558 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13558step0 = (fun i j => raw13558 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13558step0 raw13558; decide +kernel
      have hl : raw13558step0Labels = raw13558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13558 raw13558Labels permutation346 hz
    mixedMoment B raw13558step0 raw13558step0Labels = mixedMoment B raw13558step1 raw13558step1Labels := by
      have ha : raw13558step1 = (fun i j => raw13558step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13558step1 raw13558step0; decide +kernel
      have hl : raw13558step1Labels = raw13558step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13558step0 raw13558step0Labels permutation50 permutation2
    _ = mixedMoment B node3904 node3904Labels := by rfl

def raw13559 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![1, -1], ![1, -1], ![-1, 1]]
def raw13559Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13559step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![-1, 1]]
def raw13559step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13559step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw13559step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical13559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13559 raw13559Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw13559 raw13559Labels = mixedMoment B raw13559step0 raw13559step0Labels := by
      have hz : ∀ j, raw13559 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13559step0 = (fun i j => raw13559 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13559step0 raw13559; decide +kernel
      have hl : raw13559step0Labels = raw13559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13559 raw13559Labels permutation346 hz
    mixedMoment B raw13559step0 raw13559step0Labels = mixedMoment B raw13559step1 raw13559step1Labels := by
      have ha : raw13559step1 = (fun i j => raw13559step0 (permutation50 i) (permutation0 j)) := by apply Matrix.ext; unfold raw13559step1 raw13559step0; decide +kernel
      have hl : raw13559step1Labels = raw13559step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13559step0 raw13559step0Labels permutation50 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw13560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13560step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13560 raw13560Labels = mixedMoment B node1293 node1293Labels := by
  calc
    mixedMoment B raw13560 raw13560Labels = mixedMoment B raw13560step0 raw13560step0Labels := by
      have hz : ∀ j, raw13560 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13560step0 = (fun i j => raw13560 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13560step0 raw13560; decide +kernel
      have hl : raw13560step0Labels = raw13560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13560 raw13560Labels permutation346 hz
    mixedMoment B raw13560step0 raw13560step0Labels = mixedMoment B raw13560step1 raw13560step1Labels := by
      have ha : raw13560step1 = (fun i j => raw13560step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13560step1 raw13560step0; decide +kernel
      have hl : raw13560step1Labels = raw13560step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13560step0 raw13560step0Labels permutation50 permutation2
    _ = mixedMoment B node1293 node1293Labels := by rfl

def raw13561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13561Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13561 raw13561Labels = mixedMoment B node1260 node1260Labels := by
  calc
    mixedMoment B raw13561 raw13561Labels = mixedMoment B raw13561step0 raw13561step0Labels := by
      have ha : raw13561step0 = (fun i j => raw13561 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13561step0 raw13561; decide +kernel
      have hl : raw13561step0Labels = raw13561Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13561 raw13561Labels permutation170 permutation2
    _ = mixedMoment B node1260 node1260Labels := by rfl

def raw13562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13562Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13562step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13562step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13562 raw13562Labels = mixedMoment B node1262 node1262Labels := by
  calc
    mixedMoment B raw13562 raw13562Labels = mixedMoment B raw13562step0 raw13562step0Labels := by
      have hz : ∀ j, raw13562 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13562step0 = (fun i j => raw13562 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13562step0 raw13562; decide +kernel
      have hl : raw13562step0Labels = raw13562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13562 raw13562Labels permutation346 hz
    mixedMoment B raw13562step0 raw13562step0Labels = mixedMoment B raw13562step1 raw13562step1Labels := by
      have ha : raw13562step1 = (fun i j => raw13562step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13562step1 raw13562step0; decide +kernel
      have hl : raw13562step1Labels = raw13562step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13562step0 raw13562step0Labels permutation37 permutation2
    _ = mixedMoment B node1262 node1262Labels := by rfl

def raw13563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13563Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw13563step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13563step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13563step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13563 raw13563Labels = mixedMoment B node1262 node1262Labels := by
  calc
    mixedMoment B raw13563 raw13563Labels = mixedMoment B raw13563step0 raw13563step0Labels := by
      have hz : ∀ j, raw13563 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13563step0 = (fun i j => raw13563 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13563step0 raw13563; decide +kernel
      have hl : raw13563step0Labels = raw13563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13563 raw13563Labels permutation346 hz
    mixedMoment B raw13563step0 raw13563step0Labels = mixedMoment B raw13563step1 raw13563step1Labels := by
      have ha : raw13563step1 = (fun i j => raw13563step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13563step1 raw13563step0; decide +kernel
      have hl : raw13563step1Labels = raw13563step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13563step0 raw13563step0Labels permutation36 permutation2
    _ = mixedMoment B node1262 node1262Labels := by rfl

def raw13564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13564Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw13564step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13564 raw13564Labels = mixedMoment B node1270 node1270Labels := by
  calc
    mixedMoment B raw13564 raw13564Labels = mixedMoment B raw13564step0 raw13564step0Labels := by
      have hz : ∀ j, raw13564 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13564step0 = (fun i j => raw13564 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13564step0 raw13564; decide +kernel
      have hl : raw13564step0Labels = raw13564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13564 raw13564Labels permutation346 hz
    _ = mixedMoment B node1270 node1270Labels := by rfl

def raw13565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13565Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13565step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13565 raw13565Labels = mixedMoment B node2589 node2589Labels := by
  calc
    mixedMoment B raw13565 raw13565Labels = mixedMoment B raw13565step0 raw13565step0Labels := by
      have ha : raw13565step0 = (fun i j => raw13565 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13565step0 raw13565; decide +kernel
      have hl : raw13565step0Labels = raw13565Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13565 raw13565Labels permutation194 permutation2
    _ = mixedMoment B node2589 node2589Labels := by rfl

def raw13566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13566Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw13566step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13566step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13566 raw13566Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw13566 raw13566Labels = mixedMoment B raw13566step0 raw13566step0Labels := by
      have hz : ∀ j, raw13566 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13566step0 = (fun i j => raw13566 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13566step0 raw13566; decide +kernel
      have hl : raw13566step0Labels = raw13566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13566 raw13566Labels permutation346 hz
    mixedMoment B raw13566step0 raw13566step0Labels = mixedMoment B raw13566step1 raw13566step1Labels := by
      have ha : raw13566step1 = (fun i j => raw13566step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13566step1 raw13566step0; decide +kernel
      have hl : raw13566step1Labels = raw13566step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13566step0 raw13566step0Labels permutation42 permutation2
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw13567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13567Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw13567step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13567step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13567 raw13567Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw13567 raw13567Labels = mixedMoment B raw13567step0 raw13567step0Labels := by
      have hz : ∀ j, raw13567 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw13567step0 = (fun i j => raw13567 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw13567step0 raw13567; decide +kernel
      have hl : raw13567step0Labels = raw13567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13567 raw13567Labels permutation346 hz
    mixedMoment B raw13567step0 raw13567step0Labels = mixedMoment B raw13567step1 raw13567step1Labels := by
      have ha : raw13567step1 = (fun i j => raw13567step0 (permutation48 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13567step1 raw13567step0; decide +kernel
      have hl : raw13567step1Labels = raw13567step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13567step0 raw13567step0Labels permutation48 permutation2
    _ = mixedMoment B node2764 node2764Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
