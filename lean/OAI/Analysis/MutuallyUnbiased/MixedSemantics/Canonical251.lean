import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw32128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32128step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32128 raw32128Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw32128 raw32128Labels = mixedMoment B raw32128step0 raw32128step0Labels := by
      have hz : ∀ j, raw32128 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32128step0 = (fun i j => raw32128 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32128step0 raw32128; decide +kernel
      have hl : raw32128step0Labels = raw32128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32128 raw32128Labels permutation346 hz
    mixedMoment B raw32128step0 raw32128step0Labels = mixedMoment B raw32128step1 raw32128step1Labels := by
      have ha : raw32128step1 = (fun i j => raw32128step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32128step1 raw32128step0; decide +kernel
      have hl : raw32128step1Labels = raw32128step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32128step0 raw32128step0Labels permutation34 permutation2
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw32129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32129step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32129step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32129step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32129step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32129 raw32129Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw32129 raw32129Labels = mixedMoment B raw32129step0 raw32129step0Labels := by
      have hz : ∀ j, raw32129 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32129step0 = (fun i j => raw32129 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32129step0 raw32129; decide +kernel
      have hl : raw32129step0Labels = raw32129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32129 raw32129Labels permutation346 hz
    mixedMoment B raw32129step0 raw32129step0Labels = mixedMoment B raw32129step1 raw32129step1Labels := by
      have ha : raw32129step1 = (fun i j => raw32129step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32129step1 raw32129step0; decide +kernel
      have hl : raw32129step1Labels = raw32129step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32129step0 raw32129step0Labels permutation32 permutation3
    mixedMoment B raw32129step1 raw32129step1Labels = mixedMoment B raw32129step2 raw32129step2Labels := by
      have ha : raw32129step2 = raw32129step1 := by apply Matrix.ext; unfold raw32129step2 raw32129step1; decide +kernel
      have hl : raw32129step1Labels = labelEmbedding6 ∘ raw32129step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32129step1 raw32129step1Labels raw32129step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4459 node4459Labels := by rfl

def raw32130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32130step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32130step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32130step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32130step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32130 raw32130Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw32130 raw32130Labels = mixedMoment B raw32130step0 raw32130step0Labels := by
      have ha : raw32130step0 = (fun i j => raw32130 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32130step0 raw32130; decide +kernel
      have hl : raw32130step0Labels = raw32130Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32130 raw32130Labels permutation176 permutation3
    mixedMoment B raw32130step0 raw32130step0Labels = mixedMoment B raw32130step1 raw32130step1Labels := by
      have ha : raw32130step1 = raw32130step0 := by apply Matrix.ext; unfold raw32130step1 raw32130step0; decide +kernel
      have hl : raw32130step0Labels = labelEmbedding6 ∘ raw32130step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32130step0 raw32130step0Labels raw32130step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5074 node5074Labels := by rfl

def raw32131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32131step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32131step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32131step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32131step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32131 raw32131Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw32131 raw32131Labels = mixedMoment B raw32131step0 raw32131step0Labels := by
      have hz : ∀ j, raw32131 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32131step0 = (fun i j => raw32131 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32131step0 raw32131; decide +kernel
      have hl : raw32131step0Labels = raw32131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32131 raw32131Labels permutation346 hz
    mixedMoment B raw32131step0 raw32131step0Labels = mixedMoment B raw32131step1 raw32131step1Labels := by
      have ha : raw32131step1 = (fun i j => raw32131step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32131step1 raw32131step0; decide +kernel
      have hl : raw32131step1Labels = raw32131step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32131step0 raw32131step0Labels permutation38 permutation3
    mixedMoment B raw32131step1 raw32131step1Labels = mixedMoment B raw32131step2 raw32131step2Labels := by
      have ha : raw32131step2 = raw32131step1 := by apply Matrix.ext; unfold raw32131step2 raw32131step1; decide +kernel
      have hl : raw32131step1Labels = labelEmbedding6 ∘ raw32131step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32131step1 raw32131step1Labels raw32131step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw32132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32132step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw32132step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32132step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw32132step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32132 raw32132Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw32132 raw32132Labels = mixedMoment B raw32132step0 raw32132step0Labels := by
      have hz : ∀ j, raw32132 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32132step0 = (fun i j => raw32132 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32132step0 raw32132; decide +kernel
      have hl : raw32132step0Labels = raw32132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32132 raw32132Labels permutation346 hz
    mixedMoment B raw32132step0 raw32132step0Labels = mixedMoment B raw32132step1 raw32132step1Labels := by
      have ha : raw32132step1 = (fun i j => raw32132step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32132step1 raw32132step0; decide +kernel
      have hl : raw32132step1Labels = raw32132step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32132step0 raw32132step0Labels permutation34 permutation3
    mixedMoment B raw32132step1 raw32132step1Labels = mixedMoment B raw32132step2 raw32132step2Labels := by
      have ha : raw32132step2 = raw32132step1 := by apply Matrix.ext; unfold raw32132step2 raw32132step1; decide +kernel
      have hl : raw32132step1Labels = labelEmbedding6 ∘ raw32132step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32132step1 raw32132step1Labels raw32132step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw32133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32133step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw32133step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32133step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw32133step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32133 raw32133Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw32133 raw32133Labels = mixedMoment B raw32133step0 raw32133step0Labels := by
      have hz : ∀ j, raw32133 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32133step0 = (fun i j => raw32133 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32133step0 raw32133; decide +kernel
      have hl : raw32133step0Labels = raw32133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32133 raw32133Labels permutation346 hz
    mixedMoment B raw32133step0 raw32133step0Labels = mixedMoment B raw32133step1 raw32133step1Labels := by
      have ha : raw32133step1 = (fun i j => raw32133step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32133step1 raw32133step0; decide +kernel
      have hl : raw32133step1Labels = raw32133step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32133step0 raw32133step0Labels permutation36 permutation3
    mixedMoment B raw32133step1 raw32133step1Labels = mixedMoment B raw32133step2 raw32133step2Labels := by
      have ha : raw32133step2 = raw32133step1 := by apply Matrix.ext; unfold raw32133step2 raw32133step1; decide +kernel
      have hl : raw32133step1Labels = labelEmbedding6 ∘ raw32133step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32133step1 raw32133step1Labels raw32133step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw32134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32134step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32134step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32134step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32134 raw32134Labels = mixedMoment B node4345 node4345Labels := by
  calc
    mixedMoment B raw32134 raw32134Labels = mixedMoment B raw32134step0 raw32134step0Labels := by
      have ha : raw32134step0 = (fun i j => raw32134 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32134step0 raw32134; decide +kernel
      have hl : raw32134step0Labels = raw32134Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32134 raw32134Labels permutation158 permutation3
    mixedMoment B raw32134step0 raw32134step0Labels = mixedMoment B raw32134step1 raw32134step1Labels := by
      have ha : raw32134step1 = raw32134step0 := by apply Matrix.ext; unfold raw32134step1 raw32134step0; decide +kernel
      have hl : raw32134step0Labels = labelEmbedding6 ∘ raw32134step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32134step0 raw32134step0Labels raw32134step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4345 node4345Labels := by rfl

def raw32135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32135step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32135step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32135step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32135step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32135 raw32135Labels = mixedMoment B node4942 node4942Labels := by
  calc
    mixedMoment B raw32135 raw32135Labels = mixedMoment B raw32135step0 raw32135step0Labels := by
      have ha : raw32135step0 = (fun i j => raw32135 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32135step0 raw32135; decide +kernel
      have hl : raw32135step0Labels = raw32135Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32135 raw32135Labels permutation158 permutation3
    mixedMoment B raw32135step0 raw32135step0Labels = mixedMoment B raw32135step1 raw32135step1Labels := by
      have ha : raw32135step1 = raw32135step0 := by apply Matrix.ext; unfold raw32135step1 raw32135step0; decide +kernel
      have hl : raw32135step0Labels = labelEmbedding6 ∘ raw32135step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32135step0 raw32135step0Labels raw32135step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4942 node4942Labels := by rfl

def raw32136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32136step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32136step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32136 raw32136Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw32136 raw32136Labels = mixedMoment B raw32136step0 raw32136step0Labels := by
      have ha : raw32136step0 = (fun i j => raw32136 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32136step0 raw32136; decide +kernel
      have hl : raw32136step0Labels = raw32136Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32136 raw32136Labels permutation158 permutation3
    mixedMoment B raw32136step0 raw32136step0Labels = mixedMoment B raw32136step1 raw32136step1Labels := by
      have ha : raw32136step1 = raw32136step0 := by apply Matrix.ext; unfold raw32136step1 raw32136step0; decide +kernel
      have hl : raw32136step0Labels = labelEmbedding6 ∘ raw32136step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32136step0 raw32136step0Labels raw32136step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5138 node5138Labels := by rfl

def raw32137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32137step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32137step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32137step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32137 raw32137Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw32137 raw32137Labels = mixedMoment B raw32137step0 raw32137step0Labels := by
      have ha : raw32137step0 = (fun i j => raw32137 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32137step0 raw32137; decide +kernel
      have hl : raw32137step0Labels = raw32137Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32137 raw32137Labels permutation166 permutation3
    mixedMoment B raw32137step0 raw32137step0Labels = mixedMoment B raw32137step1 raw32137step1Labels := by
      have ha : raw32137step1 = raw32137step0 := by apply Matrix.ext; unfold raw32137step1 raw32137step0; decide +kernel
      have hl : raw32137step0Labels = labelEmbedding6 ∘ raw32137step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32137step0 raw32137step0Labels raw32137step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw32138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32138step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32138step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32138step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32138step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32138 raw32138Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw32138 raw32138Labels = mixedMoment B raw32138step0 raw32138step0Labels := by
      have ha : raw32138step0 = (fun i j => raw32138 (permutation172 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32138step0 raw32138; decide +kernel
      have hl : raw32138step0Labels = raw32138Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32138 raw32138Labels permutation172 permutation3
    mixedMoment B raw32138step0 raw32138step0Labels = mixedMoment B raw32138step1 raw32138step1Labels := by
      have ha : raw32138step1 = raw32138step0 := by apply Matrix.ext; unfold raw32138step1 raw32138step0; decide +kernel
      have hl : raw32138step0Labels = labelEmbedding6 ∘ raw32138step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32138step0 raw32138step0Labels raw32138step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw32139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw32139step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32139step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw32139step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32139 raw32139Labels = mixedMoment B node4357 node4357Labels := by
  calc
    mixedMoment B raw32139 raw32139Labels = mixedMoment B raw32139step0 raw32139step0Labels := by
      have hz : ∀ j, raw32139 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32139step0 = (fun i j => raw32139 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32139step0 raw32139; decide +kernel
      have hl : raw32139step0Labels = raw32139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32139 raw32139Labels permutation346 hz
    mixedMoment B raw32139step0 raw32139step0Labels = mixedMoment B raw32139step1 raw32139step1Labels := by
      have ha : raw32139step1 = (fun i j => raw32139step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32139step1 raw32139step0; decide +kernel
      have hl : raw32139step1Labels = raw32139step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32139step0 raw32139step0Labels permutation35 permutation3
    mixedMoment B raw32139step1 raw32139step1Labels = mixedMoment B raw32139step2 raw32139step2Labels := by
      have ha : raw32139step2 = raw32139step1 := by apply Matrix.ext; unfold raw32139step2 raw32139step1; decide +kernel
      have hl : raw32139step1Labels = labelEmbedding6 ∘ raw32139step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32139step1 raw32139step1Labels raw32139step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4357 node4357Labels := by rfl

def raw32140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw32140step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw32140step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32140 raw32140Labels = mixedMoment B node4951 node4951Labels := by
  calc
    mixedMoment B raw32140 raw32140Labels = mixedMoment B raw32140step0 raw32140step0Labels := by
      have hz : ∀ j, raw32140 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32140step0 = (fun i j => raw32140 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32140step0 raw32140; decide +kernel
      have hl : raw32140step0Labels = raw32140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32140 raw32140Labels permutation346 hz
    mixedMoment B raw32140step0 raw32140step0Labels = mixedMoment B raw32140step1 raw32140step1Labels := by
      have ha : raw32140step1 = (fun i j => raw32140step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32140step1 raw32140step0; decide +kernel
      have hl : raw32140step1Labels = raw32140step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32140step0 raw32140step0Labels permutation35 permutation3
    mixedMoment B raw32140step1 raw32140step1Labels = mixedMoment B raw32140step2 raw32140step2Labels := by
      have ha : raw32140step2 = raw32140step1 := by apply Matrix.ext; unfold raw32140step2 raw32140step1; decide +kernel
      have hl : raw32140step1Labels = labelEmbedding6 ∘ raw32140step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32140step1 raw32140step1Labels raw32140step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4951 node4951Labels := by rfl

def raw32141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw32141step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw32141step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32141 raw32141Labels = mixedMoment B node5040 node5040Labels := by
  calc
    mixedMoment B raw32141 raw32141Labels = mixedMoment B raw32141step0 raw32141step0Labels := by
      have ha : raw32141step0 = (fun i j => raw32141 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32141step0 raw32141; decide +kernel
      have hl : raw32141step0Labels = raw32141Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32141 raw32141Labels permutation179 permutation3
    mixedMoment B raw32141step0 raw32141step0Labels = mixedMoment B raw32141step1 raw32141step1Labels := by
      have ha : raw32141step1 = raw32141step0 := by apply Matrix.ext; unfold raw32141step1 raw32141step0; decide +kernel
      have hl : raw32141step0Labels = labelEmbedding6 ∘ raw32141step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32141step0 raw32141step0Labels raw32141step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5040 node5040Labels := by rfl

def raw32142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32142step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32142step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32142 raw32142Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw32142 raw32142Labels = mixedMoment B raw32142step0 raw32142step0Labels := by
      have hz : ∀ j, raw32142 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32142step0 = (fun i j => raw32142 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32142step0 raw32142; decide +kernel
      have hl : raw32142step0Labels = raw32142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32142 raw32142Labels permutation346 hz
    mixedMoment B raw32142step0 raw32142step0Labels = mixedMoment B raw32142step1 raw32142step1Labels := by
      have ha : raw32142step1 = (fun i j => raw32142step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32142step1 raw32142step0; decide +kernel
      have hl : raw32142step1Labels = raw32142step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32142step0 raw32142step0Labels permutation35 permutation3
    mixedMoment B raw32142step1 raw32142step1Labels = mixedMoment B raw32142step2 raw32142step2Labels := by
      have ha : raw32142step2 = raw32142step1 := by apply Matrix.ext; unfold raw32142step2 raw32142step1; decide +kernel
      have hl : raw32142step1Labels = labelEmbedding6 ∘ raw32142step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32142step1 raw32142step1Labels raw32142step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw32143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32143step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32143step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32143 raw32143Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw32143 raw32143Labels = mixedMoment B raw32143step0 raw32143step0Labels := by
      have hz : ∀ j, raw32143 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32143step0 = (fun i j => raw32143 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32143step0 raw32143; decide +kernel
      have hl : raw32143step0Labels = raw32143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32143 raw32143Labels permutation346 hz
    mixedMoment B raw32143step0 raw32143step0Labels = mixedMoment B raw32143step1 raw32143step1Labels := by
      have ha : raw32143step1 = (fun i j => raw32143step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32143step1 raw32143step0; decide +kernel
      have hl : raw32143step1Labels = raw32143step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32143step0 raw32143step0Labels permutation37 permutation3
    mixedMoment B raw32143step1 raw32143step1Labels = mixedMoment B raw32143step2 raw32143step2Labels := by
      have ha : raw32143step2 = raw32143step1 := by apply Matrix.ext; unfold raw32143step2 raw32143step1; decide +kernel
      have hl : raw32143step1Labels = labelEmbedding6 ∘ raw32143step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32143step1 raw32143step1Labels raw32143step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5164 node5164Labels := by rfl

def raw32144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw32144step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32144step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw32144step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32144 raw32144Labels = mixedMoment B node4348 node4348Labels := by
  calc
    mixedMoment B raw32144 raw32144Labels = mixedMoment B raw32144step0 raw32144step0Labels := by
      have hz : ∀ j, raw32144 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32144step0 = (fun i j => raw32144 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32144step0 raw32144; decide +kernel
      have hl : raw32144step0Labels = raw32144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32144 raw32144Labels permutation346 hz
    mixedMoment B raw32144step0 raw32144step0Labels = mixedMoment B raw32144step1 raw32144step1Labels := by
      have ha : raw32144step1 = (fun i j => raw32144step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32144step1 raw32144step0; decide +kernel
      have hl : raw32144step1Labels = raw32144step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32144step0 raw32144step0Labels permutation33 permutation3
    mixedMoment B raw32144step1 raw32144step1Labels = mixedMoment B raw32144step2 raw32144step2Labels := by
      have ha : raw32144step2 = raw32144step1 := by apply Matrix.ext; unfold raw32144step2 raw32144step1; decide +kernel
      have hl : raw32144step1Labels = labelEmbedding6 ∘ raw32144step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32144step1 raw32144step1Labels raw32144step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4348 node4348Labels := by rfl

def raw32145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw32145step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32145step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw32145step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32145 raw32145Labels = mixedMoment B node4945 node4945Labels := by
  calc
    mixedMoment B raw32145 raw32145Labels = mixedMoment B raw32145step0 raw32145step0Labels := by
      have hz : ∀ j, raw32145 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32145step0 = (fun i j => raw32145 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32145step0 raw32145; decide +kernel
      have hl : raw32145step0Labels = raw32145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32145 raw32145Labels permutation346 hz
    mixedMoment B raw32145step0 raw32145step0Labels = mixedMoment B raw32145step1 raw32145step1Labels := by
      have ha : raw32145step1 = (fun i j => raw32145step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32145step1 raw32145step0; decide +kernel
      have hl : raw32145step1Labels = raw32145step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32145step0 raw32145step0Labels permutation33 permutation3
    mixedMoment B raw32145step1 raw32145step1Labels = mixedMoment B raw32145step2 raw32145step2Labels := by
      have ha : raw32145step2 = raw32145step1 := by apply Matrix.ext; unfold raw32145step2 raw32145step1; decide +kernel
      have hl : raw32145step1Labels = labelEmbedding6 ∘ raw32145step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32145step1 raw32145step1Labels raw32145step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4945 node4945Labels := by rfl

def raw32146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw32146step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32146step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw32146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32146 raw32146Labels = mixedMoment B node5035 node5035Labels := by
  calc
    mixedMoment B raw32146 raw32146Labels = mixedMoment B raw32146step0 raw32146step0Labels := by
      have ha : raw32146step0 = (fun i j => raw32146 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32146step0 raw32146; decide +kernel
      have hl : raw32146step0Labels = raw32146Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32146 raw32146Labels permutation177 permutation3
    mixedMoment B raw32146step0 raw32146step0Labels = mixedMoment B raw32146step1 raw32146step1Labels := by
      have ha : raw32146step1 = raw32146step0 := by apply Matrix.ext; unfold raw32146step1 raw32146step0; decide +kernel
      have hl : raw32146step0Labels = labelEmbedding6 ∘ raw32146step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32146step0 raw32146step0Labels raw32146step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5035 node5035Labels := by rfl

def raw32147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw32147step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw32147step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32147 raw32147Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw32147 raw32147Labels = mixedMoment B raw32147step0 raw32147step0Labels := by
      have hz : ∀ j, raw32147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32147step0 = (fun i j => raw32147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32147step0 raw32147; decide +kernel
      have hl : raw32147step0Labels = raw32147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32147 raw32147Labels permutation346 hz
    mixedMoment B raw32147step0 raw32147step0Labels = mixedMoment B raw32147step1 raw32147step1Labels := by
      have ha : raw32147step1 = (fun i j => raw32147step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32147step1 raw32147step0; decide +kernel
      have hl : raw32147step1Labels = raw32147step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32147step0 raw32147step0Labels permutation33 permutation3
    mixedMoment B raw32147step1 raw32147step1Labels = mixedMoment B raw32147step2 raw32147step2Labels := by
      have ha : raw32147step2 = raw32147step1 := by apply Matrix.ext; unfold raw32147step2 raw32147step1; decide +kernel
      have hl : raw32147step1Labels = labelEmbedding6 ∘ raw32147step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32147step1 raw32147step1Labels raw32147step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5140 node5140Labels := by rfl

def raw32148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw32148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw32148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw32148step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw32148step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32148 raw32148Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw32148 raw32148Labels = mixedMoment B raw32148step0 raw32148step0Labels := by
      have hz : ∀ j, raw32148 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32148step0 = (fun i j => raw32148 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32148step0 raw32148; decide +kernel
      have hl : raw32148step0Labels = raw32148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32148 raw32148Labels permutation346 hz
    mixedMoment B raw32148step0 raw32148step0Labels = mixedMoment B raw32148step1 raw32148step1Labels := by
      have ha : raw32148step1 = (fun i j => raw32148step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32148step1 raw32148step0; decide +kernel
      have hl : raw32148step1Labels = raw32148step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32148step0 raw32148step0Labels permutation36 permutation3
    mixedMoment B raw32148step1 raw32148step1Labels = mixedMoment B raw32148step2 raw32148step2Labels := by
      have ha : raw32148step2 = raw32148step1 := by apply Matrix.ext; unfold raw32148step2 raw32148step1; decide +kernel
      have hl : raw32148step1Labels = labelEmbedding6 ∘ raw32148step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32148step1 raw32148step1Labels raw32148step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5161 node5161Labels := by rfl

def raw32149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw32149step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32149step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw32149step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32149 raw32149Labels = mixedMoment B node4347 node4347Labels := by
  calc
    mixedMoment B raw32149 raw32149Labels = mixedMoment B raw32149step0 raw32149step0Labels := by
      have hz : ∀ j, raw32149 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32149step0 = (fun i j => raw32149 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32149step0 raw32149; decide +kernel
      have hl : raw32149step0Labels = raw32149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32149 raw32149Labels permutation346 hz
    mixedMoment B raw32149step0 raw32149step0Labels = mixedMoment B raw32149step1 raw32149step1Labels := by
      have ha : raw32149step1 = (fun i j => raw32149step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32149step1 raw32149step0; decide +kernel
      have hl : raw32149step1Labels = raw32149step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32149step0 raw32149step0Labels permutation32 permutation3
    mixedMoment B raw32149step1 raw32149step1Labels = mixedMoment B raw32149step2 raw32149step2Labels := by
      have ha : raw32149step2 = raw32149step1 := by apply Matrix.ext; unfold raw32149step2 raw32149step1; decide +kernel
      have hl : raw32149step1Labels = labelEmbedding6 ∘ raw32149step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32149step1 raw32149step1Labels raw32149step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4347 node4347Labels := by rfl

def raw32150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw32150step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw32150step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32150 raw32150Labels = mixedMoment B node4944 node4944Labels := by
  calc
    mixedMoment B raw32150 raw32150Labels = mixedMoment B raw32150step0 raw32150step0Labels := by
      have hz : ∀ j, raw32150 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32150step0 = (fun i j => raw32150 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32150step0 raw32150; decide +kernel
      have hl : raw32150step0Labels = raw32150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32150 raw32150Labels permutation346 hz
    mixedMoment B raw32150step0 raw32150step0Labels = mixedMoment B raw32150step1 raw32150step1Labels := by
      have ha : raw32150step1 = (fun i j => raw32150step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32150step1 raw32150step0; decide +kernel
      have hl : raw32150step1Labels = raw32150step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32150step0 raw32150step0Labels permutation32 permutation3
    mixedMoment B raw32150step1 raw32150step1Labels = mixedMoment B raw32150step2 raw32150step2Labels := by
      have ha : raw32150step2 = raw32150step1 := by apply Matrix.ext; unfold raw32150step2 raw32150step1; decide +kernel
      have hl : raw32150step1Labels = labelEmbedding6 ∘ raw32150step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32150step1 raw32150step1Labels raw32150step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4944 node4944Labels := by rfl

def raw32151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw32151step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32151step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw32151step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32151 raw32151Labels = mixedMoment B node5034 node5034Labels := by
  calc
    mixedMoment B raw32151 raw32151Labels = mixedMoment B raw32151step0 raw32151step0Labels := by
      have ha : raw32151step0 = (fun i j => raw32151 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32151step0 raw32151; decide +kernel
      have hl : raw32151step0Labels = raw32151Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32151 raw32151Labels permutation176 permutation3
    mixedMoment B raw32151step0 raw32151step0Labels = mixedMoment B raw32151step1 raw32151step1Labels := by
      have ha : raw32151step1 = raw32151step0 := by apply Matrix.ext; unfold raw32151step1 raw32151step0; decide +kernel
      have hl : raw32151step0Labels = labelEmbedding6 ∘ raw32151step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32151step0 raw32151step0Labels raw32151step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5034 node5034Labels := by rfl

def raw32152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw32152step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw32152step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32152 raw32152Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw32152 raw32152Labels = mixedMoment B raw32152step0 raw32152step0Labels := by
      have hz : ∀ j, raw32152 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32152step0 = (fun i j => raw32152 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32152step0 raw32152; decide +kernel
      have hl : raw32152step0Labels = raw32152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32152 raw32152Labels permutation346 hz
    mixedMoment B raw32152step0 raw32152step0Labels = mixedMoment B raw32152step1 raw32152step1Labels := by
      have ha : raw32152step1 = (fun i j => raw32152step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32152step1 raw32152step0; decide +kernel
      have hl : raw32152step1Labels = raw32152step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32152step0 raw32152step0Labels permutation32 permutation3
    mixedMoment B raw32152step1 raw32152step1Labels = mixedMoment B raw32152step2 raw32152step2Labels := by
      have ha : raw32152step2 = raw32152step1 := by apply Matrix.ext; unfold raw32152step2 raw32152step1; decide +kernel
      have hl : raw32152step1Labels = labelEmbedding6 ∘ raw32152step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32152step1 raw32152step1Labels raw32152step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5139 node5139Labels := by rfl

def raw32153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw32153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw32153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw32153step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32153step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32153step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32153 raw32153Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw32153 raw32153Labels = mixedMoment B raw32153step0 raw32153step0Labels := by
      have hz : ∀ j, raw32153 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32153step0 = (fun i j => raw32153 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32153step0 raw32153; decide +kernel
      have hl : raw32153step0Labels = raw32153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32153 raw32153Labels permutation346 hz
    mixedMoment B raw32153step0 raw32153step0Labels = mixedMoment B raw32153step1 raw32153step1Labels := by
      have ha : raw32153step1 = (fun i j => raw32153step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32153step1 raw32153step0; decide +kernel
      have hl : raw32153step1Labels = raw32153step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32153step0 raw32153step0Labels permutation145 permutation2
    mixedMoment B raw32153step1 raw32153step1Labels = mixedMoment B raw32153step2 raw32153step2Labels := by
      have ha : raw32153step2 = -raw32153step1 := by apply Matrix.ext; change ∀ i j, raw32153step2 i j = -(raw32153step1 i j); unfold raw32153step2 raw32153step1; decide +kernel
      have hl : raw32153step2Labels = raw32153step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw32154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32154Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32154step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32154step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32154step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32154step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32154 raw32154Labels = mixedMoment B node3815 node3815Labels := by
  calc
    mixedMoment B raw32154 raw32154Labels = mixedMoment B raw32154step0 raw32154step0Labels := by
      have hz : ∀ j, raw32154 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32154step0 = (fun i j => raw32154 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32154step0 raw32154; decide +kernel
      have hl : raw32154step0Labels = raw32154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32154 raw32154Labels permutation346 hz
    mixedMoment B raw32154step0 raw32154step0Labels = mixedMoment B raw32154step1 raw32154step1Labels := by
      have ha : raw32154step1 = (fun i j => raw32154step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32154step1 raw32154step0; decide +kernel
      have hl : raw32154step1Labels = raw32154step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32154step0 raw32154step0Labels permutation144 permutation7
    mixedMoment B raw32154step1 raw32154step1Labels = mixedMoment B raw32154step2 raw32154step2Labels := by
      have ha : raw32154step2 = raw32154step1 := by apply Matrix.ext; unfold raw32154step2 raw32154step1; decide +kernel
      have hl : raw32154step1Labels = labelEmbedding1 ∘ raw32154step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32154step1 raw32154step1Labels raw32154step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3815 node3815Labels := by rfl

def raw32155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32155Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32155step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32155step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32155step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32155 raw32155Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw32155 raw32155Labels = mixedMoment B raw32155step0 raw32155step0Labels := by
      have ha : raw32155step0 = (fun i j => raw32155 (permutation658 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32155step0 raw32155; decide +kernel
      have hl : raw32155step0Labels = raw32155Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32155 raw32155Labels permutation658 permutation7
    mixedMoment B raw32155step0 raw32155step0Labels = mixedMoment B raw32155step1 raw32155step1Labels := by
      have ha : raw32155step1 = raw32155step0 := by apply Matrix.ext; unfold raw32155step1 raw32155step0; decide +kernel
      have hl : raw32155step0Labels = labelEmbedding1 ∘ raw32155step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32155step0 raw32155step0Labels raw32155step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

def raw32156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32156Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32156step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32156step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32156step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32156step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32156 raw32156Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw32156 raw32156Labels = mixedMoment B raw32156step0 raw32156step0Labels := by
      have hz : ∀ j, raw32156 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32156step0 = (fun i j => raw32156 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32156step0 raw32156; decide +kernel
      have hl : raw32156step0Labels = raw32156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32156 raw32156Labels permutation346 hz
    mixedMoment B raw32156step0 raw32156step0Labels = mixedMoment B raw32156step1 raw32156step1Labels := by
      have ha : raw32156step1 = (fun i j => raw32156step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32156step1 raw32156step0; decide +kernel
      have hl : raw32156step1Labels = raw32156step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32156step0 raw32156step0Labels permutation145 permutation7
    mixedMoment B raw32156step1 raw32156step1Labels = mixedMoment B raw32156step2 raw32156step2Labels := by
      have ha : raw32156step2 = raw32156step1 := by apply Matrix.ext; unfold raw32156step2 raw32156step1; decide +kernel
      have hl : raw32156step1Labels = labelEmbedding1 ∘ raw32156step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32156step1 raw32156step1Labels raw32156step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3857 node3857Labels := by rfl

def raw32157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32157Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32157step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32157step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32157step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32157step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32157step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32157 raw32157Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw32157 raw32157Labels = mixedMoment B raw32157step0 raw32157step0Labels := by
      have hz : ∀ j, raw32157 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32157step0 = (fun i j => raw32157 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32157step0 raw32157; decide +kernel
      have hl : raw32157step0Labels = raw32157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32157 raw32157Labels permutation346 hz
    mixedMoment B raw32157step0 raw32157step0Labels = mixedMoment B raw32157step1 raw32157step1Labels := by
      have ha : raw32157step1 = (fun i j => raw32157step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32157step1 raw32157step0; decide +kernel
      have hl : raw32157step1Labels = raw32157step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32157step0 raw32157step0Labels permutation145 permutation7
    mixedMoment B raw32157step1 raw32157step1Labels = mixedMoment B raw32157step2 raw32157step2Labels := by
      have ha : raw32157step2 = raw32157step1 := by apply Matrix.ext; unfold raw32157step2 raw32157step1; decide +kernel
      have hl : raw32157step1Labels = labelEmbedding1 ∘ raw32157step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32157step1 raw32157step1Labels raw32157step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

def raw32158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32158Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32158step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32158step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32158step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw32158step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32158 raw32158Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw32158 raw32158Labels = mixedMoment B raw32158step0 raw32158step0Labels := by
      have hz : ∀ j, raw32158 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32158step0 = (fun i j => raw32158 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32158step0 raw32158; decide +kernel
      have hl : raw32158step0Labels = raw32158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32158 raw32158Labels permutation346 hz
    mixedMoment B raw32158step0 raw32158step0Labels = mixedMoment B raw32158step1 raw32158step1Labels := by
      have ha : raw32158step1 = (fun i j => raw32158step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32158step1 raw32158step0; decide +kernel
      have hl : raw32158step1Labels = raw32158step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32158step0 raw32158step0Labels permutation145 permutation7
    mixedMoment B raw32158step1 raw32158step1Labels = mixedMoment B raw32158step2 raw32158step2Labels := by
      have ha : raw32158step2 = raw32158step1 := by apply Matrix.ext; unfold raw32158step2 raw32158step1; decide +kernel
      have hl : raw32158step1Labels = labelEmbedding1 ∘ raw32158step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32158step1 raw32158step1Labels raw32158step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw32159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32159Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32159step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw32159step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32159step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32159step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32159step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32159step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32159 raw32159Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw32159 raw32159Labels = mixedMoment B raw32159step0 raw32159step0Labels := by
      have hz : ∀ j, raw32159 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32159step0 = (fun i j => raw32159 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32159step0 raw32159; decide +kernel
      have hl : raw32159step0Labels = raw32159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32159 raw32159Labels permutation346 hz
    mixedMoment B raw32159step0 raw32159step0Labels = mixedMoment B raw32159step1 raw32159step1Labels := by
      have ha : raw32159step1 = (fun i j => raw32159step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32159step1 raw32159step0; decide +kernel
      have hl : raw32159step1Labels = raw32159step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32159step0 raw32159step0Labels permutation42 permutation5
    mixedMoment B raw32159step1 raw32159step1Labels = mixedMoment B raw32159step2 raw32159step2Labels := by
      have ha : raw32159step2 = -raw32159step1 := by apply Matrix.ext; change ∀ i j, raw32159step2 i j = -(raw32159step1 i j); unfold raw32159step2 raw32159step1; decide +kernel
      have hl : raw32159step2Labels = raw32159step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32159step2 raw32159step2Labels = mixedMoment B raw32159step3 raw32159step3Labels := by
      have ha : raw32159step3 = raw32159step2 := by apply Matrix.ext; unfold raw32159step3 raw32159step2; decide +kernel
      have hl : raw32159step2Labels = labelEmbedding1 ∘ raw32159step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32159step2 raw32159step2Labels raw32159step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

def raw32160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32160Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw32160step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32160step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32160step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32160step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32160step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32160 raw32160Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw32160 raw32160Labels = mixedMoment B raw32160step0 raw32160step0Labels := by
      have ha : raw32160step0 = (fun i j => raw32160 (permutation186 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32160step0 raw32160; decide +kernel
      have hl : raw32160step0Labels = raw32160Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32160 raw32160Labels permutation186 permutation5
    mixedMoment B raw32160step0 raw32160step0Labels = mixedMoment B raw32160step1 raw32160step1Labels := by
      have ha : raw32160step1 = -raw32160step0 := by apply Matrix.ext; change ∀ i j, raw32160step1 i j = -(raw32160step0 i j); unfold raw32160step1 raw32160step0; decide +kernel
      have hl : raw32160step1Labels = raw32160step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32160step1 raw32160step1Labels = mixedMoment B raw32160step2 raw32160step2Labels := by
      have ha : raw32160step2 = raw32160step1 := by apply Matrix.ext; unfold raw32160step2 raw32160step1; decide +kernel
      have hl : raw32160step1Labels = labelEmbedding1 ∘ raw32160step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32160step1 raw32160step1Labels raw32160step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

def raw32161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32161Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32161step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw32161step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32161step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32161step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32161step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32161step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32161 raw32161Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw32161 raw32161Labels = mixedMoment B raw32161step0 raw32161step0Labels := by
      have hz : ∀ j, raw32161 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32161step0 = (fun i j => raw32161 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32161step0 raw32161; decide +kernel
      have hl : raw32161step0Labels = raw32161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32161 raw32161Labels permutation346 hz
    mixedMoment B raw32161step0 raw32161step0Labels = mixedMoment B raw32161step1 raw32161step1Labels := by
      have ha : raw32161step1 = (fun i j => raw32161step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32161step1 raw32161step0; decide +kernel
      have hl : raw32161step1Labels = raw32161step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32161step0 raw32161step0Labels permutation42 permutation5
    mixedMoment B raw32161step1 raw32161step1Labels = mixedMoment B raw32161step2 raw32161step2Labels := by
      have ha : raw32161step2 = -raw32161step1 := by apply Matrix.ext; change ∀ i j, raw32161step2 i j = -(raw32161step1 i j); unfold raw32161step2 raw32161step1; decide +kernel
      have hl : raw32161step2Labels = raw32161step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32161step2 raw32161step2Labels = mixedMoment B raw32161step3 raw32161step3Labels := by
      have ha : raw32161step3 = raw32161step2 := by apply Matrix.ext; unfold raw32161step3 raw32161step2; decide +kernel
      have hl : raw32161step2Labels = labelEmbedding1 ∘ raw32161step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32161step2 raw32161step2Labels raw32161step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw32162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32162Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32162step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw32162step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw32162step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32162step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw32162step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32162 raw32162Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw32162 raw32162Labels = mixedMoment B raw32162step0 raw32162step0Labels := by
      have hz : ∀ j, raw32162 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32162step0 = (fun i j => raw32162 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32162step0 raw32162; decide +kernel
      have hl : raw32162step0Labels = raw32162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32162 raw32162Labels permutation346 hz
    mixedMoment B raw32162step0 raw32162step0Labels = mixedMoment B raw32162step1 raw32162step1Labels := by
      have ha : raw32162step1 = (fun i j => raw32162step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32162step1 raw32162step0; decide +kernel
      have hl : raw32162step1Labels = raw32162step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32162step0 raw32162step0Labels permutation42 permutation5
    mixedMoment B raw32162step1 raw32162step1Labels = mixedMoment B raw32162step2 raw32162step2Labels := by
      have ha : raw32162step2 = -raw32162step1 := by apply Matrix.ext; change ∀ i j, raw32162step2 i j = -(raw32162step1 i j); unfold raw32162step2 raw32162step1; decide +kernel
      have hl : raw32162step2Labels = raw32162step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32162step2 raw32162step2Labels = mixedMoment B raw32162step3 raw32162step3Labels := by
      have ha : raw32162step3 = raw32162step2 := by apply Matrix.ext; unfold raw32162step3 raw32162step2; decide +kernel
      have hl : raw32162step2Labels = labelEmbedding1 ∘ raw32162step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32162step2 raw32162step2Labels raw32162step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

def raw32163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32163Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32163step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw32163step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32163step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32163step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32163step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32163step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32163 raw32163Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw32163 raw32163Labels = mixedMoment B raw32163step0 raw32163step0Labels := by
      have hz : ∀ j, raw32163 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32163step0 = (fun i j => raw32163 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32163step0 raw32163; decide +kernel
      have hl : raw32163step0Labels = raw32163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32163 raw32163Labels permutation346 hz
    mixedMoment B raw32163step0 raw32163step0Labels = mixedMoment B raw32163step1 raw32163step1Labels := by
      have ha : raw32163step1 = (fun i j => raw32163step0 (permutation52 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32163step1 raw32163step0; decide +kernel
      have hl : raw32163step1Labels = raw32163step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32163step0 raw32163step0Labels permutation52 permutation5
    mixedMoment B raw32163step1 raw32163step1Labels = mixedMoment B raw32163step2 raw32163step2Labels := by
      have ha : raw32163step2 = -raw32163step1 := by apply Matrix.ext; change ∀ i j, raw32163step2 i j = -(raw32163step1 i j); unfold raw32163step2 raw32163step1; decide +kernel
      have hl : raw32163step2Labels = raw32163step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32163step2 raw32163step2Labels = mixedMoment B raw32163step3 raw32163step3Labels := by
      have ha : raw32163step3 = raw32163step2 := by apply Matrix.ext; unfold raw32163step3 raw32163step2; decide +kernel
      have hl : raw32163step2Labels = labelEmbedding1 ∘ raw32163step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32163step2 raw32163step2Labels raw32163step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw32164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32164Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw32164step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32164step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32164step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32164step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32164step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32164 raw32164Labels = mixedMoment B node1668 node1668Labels := by
  calc
    mixedMoment B raw32164 raw32164Labels = mixedMoment B raw32164step0 raw32164step0Labels := by
      have ha : raw32164step0 = (fun i j => raw32164 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32164step0 raw32164; decide +kernel
      have hl : raw32164step0Labels = raw32164Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32164 raw32164Labels permutation162 permutation5
    mixedMoment B raw32164step0 raw32164step0Labels = mixedMoment B raw32164step1 raw32164step1Labels := by
      have ha : raw32164step1 = -raw32164step0 := by apply Matrix.ext; change ∀ i j, raw32164step1 i j = -(raw32164step0 i j); unfold raw32164step1 raw32164step0; decide +kernel
      have hl : raw32164step1Labels = raw32164step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32164step1 raw32164step1Labels = mixedMoment B raw32164step2 raw32164step2Labels := by
      have ha : raw32164step2 = raw32164step1 := by apply Matrix.ext; unfold raw32164step2 raw32164step1; decide +kernel
      have hl : raw32164step1Labels = labelEmbedding1 ∘ raw32164step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32164step1 raw32164step1Labels raw32164step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1668 node1668Labels := by rfl

def raw32165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32165Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32165step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw32165step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32165step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32165step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32165step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32165step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32165 raw32165Labels = mixedMoment B node3407 node3407Labels := by
  calc
    mixedMoment B raw32165 raw32165Labels = mixedMoment B raw32165step0 raw32165step0Labels := by
      have ha : raw32165step0 = (fun i j => raw32165 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32165step0 raw32165; decide +kernel
      have hl : raw32165step0Labels = raw32165Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32165 raw32165Labels permutation162 permutation5
    mixedMoment B raw32165step0 raw32165step0Labels = mixedMoment B raw32165step1 raw32165step1Labels := by
      have ha : raw32165step1 = -raw32165step0 := by apply Matrix.ext; change ∀ i j, raw32165step1 i j = -(raw32165step0 i j); unfold raw32165step1 raw32165step0; decide +kernel
      have hl : raw32165step1Labels = raw32165step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32165step1 raw32165step1Labels = mixedMoment B raw32165step2 raw32165step2Labels := by
      have ha : raw32165step2 = raw32165step1 := by apply Matrix.ext; unfold raw32165step2 raw32165step1; decide +kernel
      have hl : raw32165step1Labels = labelEmbedding1 ∘ raw32165step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32165step1 raw32165step1Labels raw32165step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3407 node3407Labels := by rfl

def raw32166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32166Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw32166step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32166step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32166step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32166step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw32166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32166 raw32166Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw32166 raw32166Labels = mixedMoment B raw32166step0 raw32166step0Labels := by
      have ha : raw32166step0 = (fun i j => raw32166 (permutation204 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32166step0 raw32166; decide +kernel
      have hl : raw32166step0Labels = raw32166Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32166 raw32166Labels permutation204 permutation5
    mixedMoment B raw32166step0 raw32166step0Labels = mixedMoment B raw32166step1 raw32166step1Labels := by
      have ha : raw32166step1 = -raw32166step0 := by apply Matrix.ext; change ∀ i j, raw32166step1 i j = -(raw32166step0 i j); unfold raw32166step1 raw32166step0; decide +kernel
      have hl : raw32166step1Labels = raw32166step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32166step1 raw32166step1Labels = mixedMoment B raw32166step2 raw32166step2Labels := by
      have ha : raw32166step2 = raw32166step1 := by apply Matrix.ext; unfold raw32166step2 raw32166step1; decide +kernel
      have hl : raw32166step1Labels = labelEmbedding1 ∘ raw32166step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32166step1 raw32166step1Labels raw32166step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3517 node3517Labels := by rfl

def raw32167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32167Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32167step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw32167step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32167step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw32167step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32167step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw32167step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32167 raw32167Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw32167 raw32167Labels = mixedMoment B raw32167step0 raw32167step0Labels := by
      have ha : raw32167step0 = (fun i j => raw32167 (permutation163 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32167step0 raw32167; decide +kernel
      have hl : raw32167step0Labels = raw32167Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32167 raw32167Labels permutation163 permutation5
    mixedMoment B raw32167step0 raw32167step0Labels = mixedMoment B raw32167step1 raw32167step1Labels := by
      have ha : raw32167step1 = -raw32167step0 := by apply Matrix.ext; change ∀ i j, raw32167step1 i j = -(raw32167step0 i j); unfold raw32167step1 raw32167step0; decide +kernel
      have hl : raw32167step1Labels = raw32167step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32167step1 raw32167step1Labels = mixedMoment B raw32167step2 raw32167step2Labels := by
      have ha : raw32167step2 = raw32167step1 := by apply Matrix.ext; unfold raw32167step2 raw32167step1; decide +kernel
      have hl : raw32167step1Labels = labelEmbedding1 ∘ raw32167step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32167step1 raw32167step1Labels raw32167step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

def raw32168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32168Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32168step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32168step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32168step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32168step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32168step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32168 raw32168Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw32168 raw32168Labels = mixedMoment B raw32168step0 raw32168step0Labels := by
      have ha : raw32168step0 = (fun i j => raw32168 (permutation248 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32168step0 raw32168; decide +kernel
      have hl : raw32168step0Labels = raw32168Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32168 raw32168Labels permutation248 permutation5
    mixedMoment B raw32168step0 raw32168step0Labels = mixedMoment B raw32168step1 raw32168step1Labels := by
      have ha : raw32168step1 = -raw32168step0 := by apply Matrix.ext; change ∀ i j, raw32168step1 i j = -(raw32168step0 i j); unfold raw32168step1 raw32168step0; decide +kernel
      have hl : raw32168step1Labels = raw32168step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32168step1 raw32168step1Labels = mixedMoment B raw32168step2 raw32168step2Labels := by
      have ha : raw32168step2 = raw32168step1 := by apply Matrix.ext; unfold raw32168step2 raw32168step1; decide +kernel
      have hl : raw32168step1Labels = labelEmbedding1 ∘ raw32168step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32168step1 raw32168step1Labels raw32168step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

def raw32169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32169Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32169step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw32169step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw32169step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32169step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw32169step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32169 raw32169Labels = mixedMoment B node1682 node1682Labels := by
  calc
    mixedMoment B raw32169 raw32169Labels = mixedMoment B raw32169step0 raw32169step0Labels := by
      have hz : ∀ j, raw32169 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32169step0 = (fun i j => raw32169 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32169step0 raw32169; decide +kernel
      have hl : raw32169step0Labels = raw32169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32169 raw32169Labels permutation346 hz
    mixedMoment B raw32169step0 raw32169step0Labels = mixedMoment B raw32169step1 raw32169step1Labels := by
      have ha : raw32169step1 = (fun i j => raw32169step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32169step1 raw32169step0; decide +kernel
      have hl : raw32169step1Labels = raw32169step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32169step0 raw32169step0Labels permutation36 permutation5
    mixedMoment B raw32169step1 raw32169step1Labels = mixedMoment B raw32169step2 raw32169step2Labels := by
      have ha : raw32169step2 = -raw32169step1 := by apply Matrix.ext; change ∀ i j, raw32169step2 i j = -(raw32169step1 i j); unfold raw32169step2 raw32169step1; decide +kernel
      have hl : raw32169step2Labels = raw32169step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32169step2 raw32169step2Labels = mixedMoment B raw32169step3 raw32169step3Labels := by
      have ha : raw32169step3 = raw32169step2 := by apply Matrix.ext; unfold raw32169step3 raw32169step2; decide +kernel
      have hl : raw32169step2Labels = labelEmbedding1 ∘ raw32169step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32169step2 raw32169step2Labels raw32169step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1682 node1682Labels := by rfl

def raw32170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32170Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32170step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw32170step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32170step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw32170step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32170step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw32170step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32170 raw32170Labels = mixedMoment B node3418 node3418Labels := by
  calc
    mixedMoment B raw32170 raw32170Labels = mixedMoment B raw32170step0 raw32170step0Labels := by
      have hz : ∀ j, raw32170 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32170step0 = (fun i j => raw32170 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32170step0 raw32170; decide +kernel
      have hl : raw32170step0Labels = raw32170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32170 raw32170Labels permutation346 hz
    mixedMoment B raw32170step0 raw32170step0Labels = mixedMoment B raw32170step1 raw32170step1Labels := by
      have ha : raw32170step1 = (fun i j => raw32170step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32170step1 raw32170step0; decide +kernel
      have hl : raw32170step1Labels = raw32170step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32170step0 raw32170step0Labels permutation36 permutation5
    mixedMoment B raw32170step1 raw32170step1Labels = mixedMoment B raw32170step2 raw32170step2Labels := by
      have ha : raw32170step2 = -raw32170step1 := by apply Matrix.ext; change ∀ i j, raw32170step2 i j = -(raw32170step1 i j); unfold raw32170step2 raw32170step1; decide +kernel
      have hl : raw32170step2Labels = raw32170step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32170step2 raw32170step2Labels = mixedMoment B raw32170step3 raw32170step3Labels := by
      have ha : raw32170step3 = raw32170step2 := by apply Matrix.ext; unfold raw32170step3 raw32170step2; decide +kernel
      have hl : raw32170step2Labels = labelEmbedding1 ∘ raw32170step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32170step2 raw32170step2Labels raw32170step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3418 node3418Labels := by rfl

def raw32171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32171Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32171step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw32171step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32171step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw32171step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32171step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw32171step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32171 raw32171Labels = mixedMoment B node3454 node3454Labels := by
  calc
    mixedMoment B raw32171 raw32171Labels = mixedMoment B raw32171step0 raw32171step0Labels := by
      have ha : raw32171step0 = (fun i j => raw32171 (permutation180 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32171step0 raw32171; decide +kernel
      have hl : raw32171step0Labels = raw32171Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32171 raw32171Labels permutation180 permutation5
    mixedMoment B raw32171step0 raw32171step0Labels = mixedMoment B raw32171step1 raw32171step1Labels := by
      have ha : raw32171step1 = -raw32171step0 := by apply Matrix.ext; change ∀ i j, raw32171step1 i j = -(raw32171step0 i j); unfold raw32171step1 raw32171step0; decide +kernel
      have hl : raw32171step1Labels = raw32171step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32171step1 raw32171step1Labels = mixedMoment B raw32171step2 raw32171step2Labels := by
      have ha : raw32171step2 = raw32171step1 := by apply Matrix.ext; unfold raw32171step2 raw32171step1; decide +kernel
      have hl : raw32171step1Labels = labelEmbedding1 ∘ raw32171step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32171step1 raw32171step1Labels raw32171step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3454 node3454Labels := by rfl

def raw32172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32172Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32172step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw32172step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32172step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw32172step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32172step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw32172step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32172 raw32172Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw32172 raw32172Labels = mixedMoment B raw32172step0 raw32172step0Labels := by
      have hz : ∀ j, raw32172 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32172step0 = (fun i j => raw32172 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32172step0 raw32172; decide +kernel
      have hl : raw32172step0Labels = raw32172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32172 raw32172Labels permutation346 hz
    mixedMoment B raw32172step0 raw32172step0Labels = mixedMoment B raw32172step1 raw32172step1Labels := by
      have ha : raw32172step1 = (fun i j => raw32172step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32172step1 raw32172step0; decide +kernel
      have hl : raw32172step1Labels = raw32172step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32172step0 raw32172step0Labels permutation37 permutation5
    mixedMoment B raw32172step1 raw32172step1Labels = mixedMoment B raw32172step2 raw32172step2Labels := by
      have ha : raw32172step2 = -raw32172step1 := by apply Matrix.ext; change ∀ i j, raw32172step2 i j = -(raw32172step1 i j); unfold raw32172step2 raw32172step1; decide +kernel
      have hl : raw32172step2Labels = raw32172step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32172step2 raw32172step2Labels = mixedMoment B raw32172step3 raw32172step3Labels := by
      have ha : raw32172step3 = raw32172step2 := by apply Matrix.ext; unfold raw32172step3 raw32172step2; decide +kernel
      have hl : raw32172step2Labels = labelEmbedding1 ∘ raw32172step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32172step2 raw32172step2Labels raw32172step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3612 node3612Labels := by rfl

def raw32173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32173Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32173step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw32173step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32173step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32173step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32173step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32173step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32173 raw32173Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw32173 raw32173Labels = mixedMoment B raw32173step0 raw32173step0Labels := by
      have hz : ∀ j, raw32173 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32173step0 = (fun i j => raw32173 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32173step0 raw32173; decide +kernel
      have hl : raw32173step0Labels = raw32173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32173 raw32173Labels permutation346 hz
    mixedMoment B raw32173step0 raw32173step0Labels = mixedMoment B raw32173step1 raw32173step1Labels := by
      have ha : raw32173step1 = (fun i j => raw32173step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32173step1 raw32173step0; decide +kernel
      have hl : raw32173step1Labels = raw32173step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32173step0 raw32173step0Labels permutation50 permutation5
    mixedMoment B raw32173step1 raw32173step1Labels = mixedMoment B raw32173step2 raw32173step2Labels := by
      have ha : raw32173step2 = -raw32173step1 := by apply Matrix.ext; change ∀ i j, raw32173step2 i j = -(raw32173step1 i j); unfold raw32173step2 raw32173step1; decide +kernel
      have hl : raw32173step2Labels = raw32173step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32173step2 raw32173step2Labels = mixedMoment B raw32173step3 raw32173step3Labels := by
      have ha : raw32173step3 = raw32173step2 := by apply Matrix.ext; unfold raw32173step3 raw32173step2; decide +kernel
      have hl : raw32173step2Labels = labelEmbedding1 ∘ raw32173step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32173step2 raw32173step2Labels raw32173step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3565 node3565Labels := by rfl

def raw32174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32174Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32174step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw32174step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw32174step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32174step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw32174step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32174 raw32174Labels = mixedMoment B node1669 node1669Labels := by
  calc
    mixedMoment B raw32174 raw32174Labels = mixedMoment B raw32174step0 raw32174step0Labels := by
      have hz : ∀ j, raw32174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32174step0 = (fun i j => raw32174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32174step0 raw32174; decide +kernel
      have hl : raw32174step0Labels = raw32174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32174 raw32174Labels permutation346 hz
    mixedMoment B raw32174step0 raw32174step0Labels = mixedMoment B raw32174step1 raw32174step1Labels := by
      have ha : raw32174step1 = (fun i j => raw32174step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32174step1 raw32174step0; decide +kernel
      have hl : raw32174step1Labels = raw32174step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32174step0 raw32174step0Labels permutation33 permutation5
    mixedMoment B raw32174step1 raw32174step1Labels = mixedMoment B raw32174step2 raw32174step2Labels := by
      have ha : raw32174step2 = -raw32174step1 := by apply Matrix.ext; change ∀ i j, raw32174step2 i j = -(raw32174step1 i j); unfold raw32174step2 raw32174step1; decide +kernel
      have hl : raw32174step2Labels = raw32174step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32174step2 raw32174step2Labels = mixedMoment B raw32174step3 raw32174step3Labels := by
      have ha : raw32174step3 = raw32174step2 := by apply Matrix.ext; unfold raw32174step3 raw32174step2; decide +kernel
      have hl : raw32174step2Labels = labelEmbedding1 ∘ raw32174step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32174step2 raw32174step2Labels raw32174step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1669 node1669Labels := by rfl

def raw32175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32175Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32175step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw32175step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32175step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw32175step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32175 raw32175Labels = mixedMoment B node2658 node2658Labels := by
  calc
    mixedMoment B raw32175 raw32175Labels = mixedMoment B raw32175step0 raw32175step0Labels := by
      have hz : ∀ j, raw32175 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32175step0 = (fun i j => raw32175 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32175step0 raw32175; decide +kernel
      have hl : raw32175step0Labels = raw32175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32175 raw32175Labels permutation346 hz
    mixedMoment B raw32175step0 raw32175step0Labels = mixedMoment B raw32175step1 raw32175step1Labels := by
      have ha : raw32175step1 = (fun i j => raw32175step0 (permutation127 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32175step1 raw32175step0; decide +kernel
      have hl : raw32175step1Labels = raw32175step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32175step0 raw32175step0Labels permutation127 permutation5
    mixedMoment B raw32175step1 raw32175step1Labels = mixedMoment B raw32175step2 raw32175step2Labels := by
      have ha : raw32175step2 = raw32175step1 := by apply Matrix.ext; unfold raw32175step2 raw32175step1; decide +kernel
      have hl : raw32175step1Labels = labelEmbedding1 ∘ raw32175step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32175step1 raw32175step1Labels raw32175step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2658 node2658Labels := by rfl

def raw32176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw32176step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32176step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw32176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32176 raw32176Labels = mixedMoment B node2652 node2652Labels := by
  calc
    mixedMoment B raw32176 raw32176Labels = mixedMoment B raw32176step0 raw32176step0Labels := by
      have ha : raw32176step0 = (fun i j => raw32176 (permutation587 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32176step0 raw32176; decide +kernel
      have hl : raw32176step0Labels = raw32176Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32176 raw32176Labels permutation587 permutation5
    mixedMoment B raw32176step0 raw32176step0Labels = mixedMoment B raw32176step1 raw32176step1Labels := by
      have ha : raw32176step1 = raw32176step0 := by apply Matrix.ext; unfold raw32176step1 raw32176step0; decide +kernel
      have hl : raw32176step0Labels = labelEmbedding1 ∘ raw32176step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32176step0 raw32176step0Labels raw32176step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2652 node2652Labels := by rfl

def raw32177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32177Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32177step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw32177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32177step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw32177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32177 raw32177Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw32177 raw32177Labels = mixedMoment B raw32177step0 raw32177step0Labels := by
      have hz : ∀ j, raw32177 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32177step0 = (fun i j => raw32177 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32177step0 raw32177; decide +kernel
      have hl : raw32177step0Labels = raw32177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32177 raw32177Labels permutation346 hz
    mixedMoment B raw32177step0 raw32177step0Labels = mixedMoment B raw32177step1 raw32177step1Labels := by
      have ha : raw32177step1 = (fun i j => raw32177step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32177step1 raw32177step0; decide +kernel
      have hl : raw32177step1Labels = raw32177step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32177step0 raw32177step0Labels permutation125 permutation5
    mixedMoment B raw32177step1 raw32177step1Labels = mixedMoment B raw32177step2 raw32177step2Labels := by
      have ha : raw32177step2 = raw32177step1 := by apply Matrix.ext; unfold raw32177step2 raw32177step1; decide +kernel
      have hl : raw32177step1Labels = labelEmbedding1 ∘ raw32177step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32177step1 raw32177step1Labels raw32177step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2670 node2670Labels := by rfl

def raw32178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw32178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw32178step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32178step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32178 raw32178Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw32178 raw32178Labels = mixedMoment B raw32178step0 raw32178step0Labels := by
      have hz : ∀ j, raw32178 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32178step0 = (fun i j => raw32178 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32178step0 raw32178; decide +kernel
      have hl : raw32178step0Labels = raw32178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32178 raw32178Labels permutation346 hz
    mixedMoment B raw32178step0 raw32178step0Labels = mixedMoment B raw32178step1 raw32178step1Labels := by
      have ha : raw32178step1 = (fun i j => raw32178step0 (permutation119 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32178step1 raw32178step0; decide +kernel
      have hl : raw32178step1Labels = raw32178step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32178step0 raw32178step0Labels permutation119 permutation5
    mixedMoment B raw32178step1 raw32178step1Labels = mixedMoment B raw32178step2 raw32178step2Labels := by
      have ha : raw32178step2 = raw32178step1 := by apply Matrix.ext; unfold raw32178step2 raw32178step1; decide +kernel
      have hl : raw32178step1Labels = labelEmbedding1 ∘ raw32178step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32178step1 raw32178step1Labels raw32178step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

def raw32179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32179Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32179step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw32179step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32179step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw32179step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32179step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw32179step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32179 raw32179Labels = mixedMoment B node1676 node1676Labels := by
  calc
    mixedMoment B raw32179 raw32179Labels = mixedMoment B raw32179step0 raw32179step0Labels := by
      have hz : ∀ j, raw32179 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32179step0 = (fun i j => raw32179 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32179step0 raw32179; decide +kernel
      have hl : raw32179step0Labels = raw32179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32179 raw32179Labels permutation346 hz
    mixedMoment B raw32179step0 raw32179step0Labels = mixedMoment B raw32179step1 raw32179step1Labels := by
      have ha : raw32179step1 = (fun i j => raw32179step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32179step1 raw32179step0; decide +kernel
      have hl : raw32179step1Labels = raw32179step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32179step0 raw32179step0Labels permutation33 permutation5
    mixedMoment B raw32179step1 raw32179step1Labels = mixedMoment B raw32179step2 raw32179step2Labels := by
      have ha : raw32179step2 = -raw32179step1 := by apply Matrix.ext; change ∀ i j, raw32179step2 i j = -(raw32179step1 i j); unfold raw32179step2 raw32179step1; decide +kernel
      have hl : raw32179step2Labels = raw32179step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32179step2 raw32179step2Labels = mixedMoment B raw32179step3 raw32179step3Labels := by
      have ha : raw32179step3 = raw32179step2 := by apply Matrix.ext; unfold raw32179step3 raw32179step2; decide +kernel
      have hl : raw32179step2Labels = labelEmbedding1 ∘ raw32179step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32179step2 raw32179step2Labels raw32179step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1676 node1676Labels := by rfl

def raw32180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32180step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw32180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw32180step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32180step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw32180step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32180 raw32180Labels = mixedMoment B node3413 node3413Labels := by
  calc
    mixedMoment B raw32180 raw32180Labels = mixedMoment B raw32180step0 raw32180step0Labels := by
      have hz : ∀ j, raw32180 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32180step0 = (fun i j => raw32180 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32180step0 raw32180; decide +kernel
      have hl : raw32180step0Labels = raw32180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32180 raw32180Labels permutation346 hz
    mixedMoment B raw32180step0 raw32180step0Labels = mixedMoment B raw32180step1 raw32180step1Labels := by
      have ha : raw32180step1 = (fun i j => raw32180step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32180step1 raw32180step0; decide +kernel
      have hl : raw32180step1Labels = raw32180step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32180step0 raw32180step0Labels permutation33 permutation5
    mixedMoment B raw32180step1 raw32180step1Labels = mixedMoment B raw32180step2 raw32180step2Labels := by
      have ha : raw32180step2 = -raw32180step1 := by apply Matrix.ext; change ∀ i j, raw32180step2 i j = -(raw32180step1 i j); unfold raw32180step2 raw32180step1; decide +kernel
      have hl : raw32180step2Labels = raw32180step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32180step2 raw32180step2Labels = mixedMoment B raw32180step3 raw32180step3Labels := by
      have ha : raw32180step3 = raw32180step2 := by apply Matrix.ext; unfold raw32180step3 raw32180step2; decide +kernel
      have hl : raw32180step2Labels = labelEmbedding1 ∘ raw32180step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32180step2 raw32180step2Labels raw32180step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3413 node3413Labels := by rfl

def raw32181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw32181step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw32181step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32181step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw32181step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32181 raw32181Labels = mixedMoment B node3451 node3451Labels := by
  calc
    mixedMoment B raw32181 raw32181Labels = mixedMoment B raw32181step0 raw32181step0Labels := by
      have ha : raw32181step0 = (fun i j => raw32181 (permutation177 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32181step0 raw32181; decide +kernel
      have hl : raw32181step0Labels = raw32181Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32181 raw32181Labels permutation177 permutation5
    mixedMoment B raw32181step0 raw32181step0Labels = mixedMoment B raw32181step1 raw32181step1Labels := by
      have ha : raw32181step1 = -raw32181step0 := by apply Matrix.ext; change ∀ i j, raw32181step1 i j = -(raw32181step0 i j); unfold raw32181step1 raw32181step0; decide +kernel
      have hl : raw32181step1Labels = raw32181step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32181step1 raw32181step1Labels = mixedMoment B raw32181step2 raw32181step2Labels := by
      have ha : raw32181step2 = raw32181step1 := by apply Matrix.ext; unfold raw32181step2 raw32181step1; decide +kernel
      have hl : raw32181step1Labels = labelEmbedding1 ∘ raw32181step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32181step1 raw32181step1Labels raw32181step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3451 node3451Labels := by rfl

def raw32182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32182step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw32182step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32182step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw32182step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32182step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw32182step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32182 raw32182Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw32182 raw32182Labels = mixedMoment B raw32182step0 raw32182step0Labels := by
      have hz : ∀ j, raw32182 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32182step0 = (fun i j => raw32182 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32182step0 raw32182; decide +kernel
      have hl : raw32182step0Labels = raw32182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32182 raw32182Labels permutation346 hz
    mixedMoment B raw32182step0 raw32182step0Labels = mixedMoment B raw32182step1 raw32182step1Labels := by
      have ha : raw32182step1 = (fun i j => raw32182step0 (permutation39 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32182step1 raw32182step0; decide +kernel
      have hl : raw32182step1Labels = raw32182step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32182step0 raw32182step0Labels permutation39 permutation5
    mixedMoment B raw32182step1 raw32182step1Labels = mixedMoment B raw32182step2 raw32182step2Labels := by
      have ha : raw32182step2 = -raw32182step1 := by apply Matrix.ext; change ∀ i j, raw32182step2 i j = -(raw32182step1 i j); unfold raw32182step2 raw32182step1; decide +kernel
      have hl : raw32182step2Labels = raw32182step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32182step2 raw32182step2Labels = mixedMoment B raw32182step3 raw32182step3Labels := by
      have ha : raw32182step3 = raw32182step2 := by apply Matrix.ext; unfold raw32182step3 raw32182step2; decide +kernel
      have hl : raw32182step2Labels = labelEmbedding1 ∘ raw32182step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32182step2 raw32182step2Labels raw32182step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

def raw32183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw32183Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw32183step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32183step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32183step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32183 raw32183Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw32183 raw32183Labels = mixedMoment B raw32183step0 raw32183step0Labels := by
      have hz : ∀ j, raw32183 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32183step0 = (fun i j => raw32183 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32183step0 raw32183; decide +kernel
      have hl : raw32183step0Labels = raw32183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32183 raw32183Labels permutation346 hz
    mixedMoment B raw32183step0 raw32183step0Labels = mixedMoment B raw32183step1 raw32183step1Labels := by
      have ha : raw32183step1 = (fun i j => raw32183step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32183step1 raw32183step0; decide +kernel
      have hl : raw32183step1Labels = raw32183step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32183step0 raw32183step0Labels permutation145 permutation7
    mixedMoment B raw32183step1 raw32183step1Labels = mixedMoment B raw32183step2 raw32183step2Labels := by
      have ha : raw32183step2 = raw32183step1 := by apply Matrix.ext; unfold raw32183step2 raw32183step1; decide +kernel
      have hl : raw32183step1Labels = labelEmbedding1 ∘ raw32183step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32183step1 raw32183step1Labels raw32183step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

def raw32184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32184 raw32184Labels = mixedMoment B node4971 node4971Labels := by
  calc
    _ = mixedMoment B node4971 node4971Labels := by rfl

def raw32185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32185step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32185step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32185 raw32185Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw32185 raw32185Labels = mixedMoment B raw32185step0 raw32185step0Labels := by
      have ha : raw32185step0 = (fun i j => raw32185 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32185step0 raw32185; decide +kernel
      have hl : raw32185step0Labels = raw32185Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32185 raw32185Labels permutation164 permutation2
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw32186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32186step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32186 raw32186Labels = mixedMoment B node4977 node4977Labels := by
  calc
    mixedMoment B raw32186 raw32186Labels = mixedMoment B raw32186step0 raw32186step0Labels := by
      have hz : ∀ j, raw32186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32186step0 = (fun i j => raw32186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32186step0 raw32186; decide +kernel
      have hl : raw32186step0Labels = raw32186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32186 raw32186Labels permutation346 hz
    mixedMoment B raw32186step0 raw32186step0Labels = mixedMoment B raw32186step1 raw32186step1Labels := by
      have ha : raw32186step1 = (fun i j => raw32186step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32186step1 raw32186step0; decide +kernel
      have hl : raw32186step1Labels = raw32186step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32186step0 raw32186step0Labels permutation35 permutation2
    _ = mixedMoment B node4977 node4977Labels := by rfl

def raw32187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32187step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32187 raw32187Labels = mixedMoment B node5117 node5117Labels := by
  calc
    mixedMoment B raw32187 raw32187Labels = mixedMoment B raw32187step0 raw32187step0Labels := by
      have ha : raw32187step0 = (fun i j => raw32187 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32187step0 raw32187; decide +kernel
      have hl : raw32187step0Labels = raw32187Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32187 raw32187Labels permutation155 permutation2
    _ = mixedMoment B node5117 node5117Labels := by rfl

def raw32188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32188step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32188step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32188 raw32188Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw32188 raw32188Labels = mixedMoment B raw32188step0 raw32188step0Labels := by
      have hz : ∀ j, raw32188 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32188step0 = (fun i j => raw32188 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32188step0 raw32188; decide +kernel
      have hl : raw32188step0Labels = raw32188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32188 raw32188Labels permutation346 hz
    mixedMoment B raw32188step0 raw32188step0Labels = mixedMoment B raw32188step1 raw32188step1Labels := by
      have ha : raw32188step1 = (fun i j => raw32188step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32188step1 raw32188step0; decide +kernel
      have hl : raw32188step1Labels = raw32188step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32188step0 raw32188step0Labels permutation35 permutation2
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw32189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32189step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32189step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32189 raw32189Labels = mixedMoment B node4977 node4977Labels := by
  calc
    mixedMoment B raw32189 raw32189Labels = mixedMoment B raw32189step0 raw32189step0Labels := by
      have hz : ∀ j, raw32189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32189step0 = (fun i j => raw32189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32189step0 raw32189; decide +kernel
      have hl : raw32189step0Labels = raw32189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32189 raw32189Labels permutation346 hz
    mixedMoment B raw32189step0 raw32189step0Labels = mixedMoment B raw32189step1 raw32189step1Labels := by
      have ha : raw32189step1 = (fun i j => raw32189step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32189step1 raw32189step0; decide +kernel
      have hl : raw32189step1Labels = raw32189step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32189step0 raw32189step0Labels permutation33 permutation2
    _ = mixedMoment B node4977 node4977Labels := by rfl

def raw32190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32190step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32190step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32190 raw32190Labels = mixedMoment B node5117 node5117Labels := by
  calc
    mixedMoment B raw32190 raw32190Labels = mixedMoment B raw32190step0 raw32190step0Labels := by
      have ha : raw32190step0 = (fun i j => raw32190 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32190step0 raw32190; decide +kernel
      have hl : raw32190step0Labels = raw32190Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32190 raw32190Labels permutation153 permutation2
    _ = mixedMoment B node5117 node5117Labels := by rfl

def raw32191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32191Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32191step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32191step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32191 raw32191Labels = mixedMoment B node2807 node2807Labels := by
  calc
    mixedMoment B raw32191 raw32191Labels = mixedMoment B raw32191step0 raw32191step0Labels := by
      have ha : raw32191step0 = (fun i j => raw32191 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32191step0 raw32191; decide +kernel
      have hl : raw32191step0Labels = raw32191Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32191 raw32191Labels permutation160 permutation3
    _ = mixedMoment B node2807 node2807Labels := by rfl

def raw32192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32192Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32192step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32192 raw32192Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw32192 raw32192Labels = mixedMoment B raw32192step0 raw32192step0Labels := by
      have ha : raw32192step0 = (fun i j => raw32192 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32192step0 raw32192; decide +kernel
      have hl : raw32192step0Labels = raw32192Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32192 raw32192Labels permutation166 permutation3
    _ = mixedMoment B node2924 node2924Labels := by rfl

def raw32193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw32193Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32193step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32193 raw32193Labels = mixedMoment B node2958 node2958Labels := by
  calc
    mixedMoment B raw32193 raw32193Labels = mixedMoment B raw32193step0 raw32193step0Labels := by
      have ha : raw32193step0 = (fun i j => raw32193 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32193step0 raw32193; decide +kernel
      have hl : raw32193step0Labels = raw32193Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32193 raw32193Labels permutation160 permutation3
    _ = mixedMoment B node2958 node2958Labels := by rfl

def raw32194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32194Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32194step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32194step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32194 raw32194Labels = mixedMoment B node2813 node2813Labels := by
  calc
    mixedMoment B raw32194 raw32194Labels = mixedMoment B raw32194step0 raw32194step0Labels := by
      have hz : ∀ j, raw32194 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32194step0 = (fun i j => raw32194 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32194step0 raw32194; decide +kernel
      have hl : raw32194step0Labels = raw32194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32194 raw32194Labels permutation346 hz
    mixedMoment B raw32194step0 raw32194step0Labels = mixedMoment B raw32194step1 raw32194step1Labels := by
      have ha : raw32194step1 = (fun i j => raw32194step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32194step1 raw32194step0; decide +kernel
      have hl : raw32194step1Labels = raw32194step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32194step0 raw32194step0Labels permutation34 permutation3
    _ = mixedMoment B node2813 node2813Labels := by rfl

def raw32195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32195Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32195step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32195step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32195 raw32195Labels = mixedMoment B node2893 node2893Labels := by
  calc
    mixedMoment B raw32195 raw32195Labels = mixedMoment B raw32195step0 raw32195step0Labels := by
      have ha : raw32195step0 = (fun i j => raw32195 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32195step0 raw32195; decide +kernel
      have hl : raw32195step0Labels = raw32195Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32195 raw32195Labels permutation154 permutation3
    _ = mixedMoment B node2893 node2893Labels := by rfl

def raw32196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32196Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw32196step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32196step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32196step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32196 raw32196Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw32196 raw32196Labels = mixedMoment B raw32196step0 raw32196step0Labels := by
      have hz : ∀ j, raw32196 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32196step0 = (fun i j => raw32196 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32196step0 raw32196; decide +kernel
      have hl : raw32196step0Labels = raw32196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32196 raw32196Labels permutation346 hz
    mixedMoment B raw32196step0 raw32196step0Labels = mixedMoment B raw32196step1 raw32196step1Labels := by
      have ha : raw32196step1 = (fun i j => raw32196step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32196step1 raw32196step0; decide +kernel
      have hl : raw32196step1Labels = raw32196step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32196step0 raw32196step0Labels permutation34 permutation3
    _ = mixedMoment B node2931 node2931Labels := by rfl

def raw32197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw32197Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw32197step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32197step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32197 raw32197Labels = mixedMoment B node2960 node2960Labels := by
  calc
    mixedMoment B raw32197 raw32197Labels = mixedMoment B raw32197step0 raw32197step0Labels := by
      have hz : ∀ j, raw32197 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32197step0 = (fun i j => raw32197 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32197step0 raw32197; decide +kernel
      have hl : raw32197step0Labels = raw32197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32197 raw32197Labels permutation346 hz
    mixedMoment B raw32197step0 raw32197step0Labels = mixedMoment B raw32197step1 raw32197step1Labels := by
      have ha : raw32197step1 = (fun i j => raw32197step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32197step1 raw32197step0; decide +kernel
      have hl : raw32197step1Labels = raw32197step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32197step0 raw32197step0Labels permutation35 permutation3
    _ = mixedMoment B node2960 node2960Labels := by rfl

def raw32198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32198Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32198step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32198step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32198 raw32198Labels = mixedMoment B node2813 node2813Labels := by
  calc
    mixedMoment B raw32198 raw32198Labels = mixedMoment B raw32198step0 raw32198step0Labels := by
      have hz : ∀ j, raw32198 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32198step0 = (fun i j => raw32198 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32198step0 raw32198; decide +kernel
      have hl : raw32198step0Labels = raw32198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32198 raw32198Labels permutation346 hz
    mixedMoment B raw32198step0 raw32198step0Labels = mixedMoment B raw32198step1 raw32198step1Labels := by
      have ha : raw32198step1 = (fun i j => raw32198step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32198step1 raw32198step0; decide +kernel
      have hl : raw32198step1Labels = raw32198step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32198step0 raw32198step0Labels permutation32 permutation3
    _ = mixedMoment B node2813 node2813Labels := by rfl

def raw32199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32199Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32199step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32199 raw32199Labels = mixedMoment B node2893 node2893Labels := by
  calc
    mixedMoment B raw32199 raw32199Labels = mixedMoment B raw32199step0 raw32199step0Labels := by
      have ha : raw32199step0 = (fun i j => raw32199 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32199step0 raw32199; decide +kernel
      have hl : raw32199step0Labels = raw32199Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32199 raw32199Labels permutation152 permutation3
    _ = mixedMoment B node2893 node2893Labels := by rfl

def raw32200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw32200Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw32200step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32200step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32200 raw32200Labels = mixedMoment B node2960 node2960Labels := by
  calc
    mixedMoment B raw32200 raw32200Labels = mixedMoment B raw32200step0 raw32200step0Labels := by
      have hz : ∀ j, raw32200 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32200step0 = (fun i j => raw32200 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32200step0 raw32200; decide +kernel
      have hl : raw32200step0Labels = raw32200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32200 raw32200Labels permutation346 hz
    mixedMoment B raw32200step0 raw32200step0Labels = mixedMoment B raw32200step1 raw32200step1Labels := by
      have ha : raw32200step1 = (fun i j => raw32200step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32200step1 raw32200step0; decide +kernel
      have hl : raw32200step1Labels = raw32200step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32200step0 raw32200step0Labels permutation33 permutation3
    _ = mixedMoment B node2960 node2960Labels := by rfl

def raw32201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32201step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32201step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32201step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32201 raw32201Labels = mixedMoment B node4947 node4947Labels := by
  calc
    mixedMoment B raw32201 raw32201Labels = mixedMoment B raw32201step0 raw32201step0Labels := by
      have ha : raw32201step0 = (fun i j => raw32201 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32201step0 raw32201; decide +kernel
      have hl : raw32201step0Labels = raw32201Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32201 raw32201Labels permutation152 permutation3
    mixedMoment B raw32201step0 raw32201step0Labels = mixedMoment B raw32201step1 raw32201step1Labels := by
      have ha : raw32201step1 = raw32201step0 := by apply Matrix.ext; unfold raw32201step1 raw32201step0; decide +kernel
      have hl : raw32201step0Labels = labelEmbedding6 ∘ raw32201step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32201step0 raw32201step0Labels raw32201step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4947 node4947Labels := by rfl

def raw32202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw32202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32202step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32202step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32202 raw32202Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw32202 raw32202Labels = mixedMoment B raw32202step0 raw32202step0Labels := by
      have hz : ∀ j, raw32202 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32202step0 = (fun i j => raw32202 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32202step0 raw32202; decide +kernel
      have hl : raw32202step0Labels = raw32202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32202 raw32202Labels permutation520 hz
    mixedMoment B raw32202step0 raw32202step0Labels = mixedMoment B raw32202step1 raw32202step1Labels := by
      have ha : raw32202step1 = (fun i j => raw32202step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32202step1 raw32202step0; decide +kernel
      have hl : raw32202step1Labels = raw32202step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32202step0 raw32202step0Labels permutation32 permutation3
    mixedMoment B raw32202step1 raw32202step1Labels = mixedMoment B raw32202step2 raw32202step2Labels := by
      have ha : raw32202step2 = raw32202step1 := by apply Matrix.ext; unfold raw32202step2 raw32202step1; decide +kernel
      have hl : raw32202step1Labels = labelEmbedding6 ∘ raw32202step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32202step1 raw32202step1Labels raw32202step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5172 node5172Labels := by rfl

def raw32203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32203step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32203step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32203 raw32203Labels = mixedMoment B node4949 node4949Labels := by
  calc
    mixedMoment B raw32203 raw32203Labels = mixedMoment B raw32203step0 raw32203step0Labels := by
      have hz : ∀ j, raw32203 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32203step0 = (fun i j => raw32203 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32203step0 raw32203; decide +kernel
      have hl : raw32203step0Labels = raw32203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32203 raw32203Labels permutation346 hz
    mixedMoment B raw32203step0 raw32203step0Labels = mixedMoment B raw32203step1 raw32203step1Labels := by
      have ha : raw32203step1 = (fun i j => raw32203step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32203step1 raw32203step0; decide +kernel
      have hl : raw32203step1Labels = raw32203step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32203step0 raw32203step0Labels permutation35 permutation3
    mixedMoment B raw32203step1 raw32203step1Labels = mixedMoment B raw32203step2 raw32203step2Labels := by
      have ha : raw32203step2 = raw32203step1 := by apply Matrix.ext; unfold raw32203step2 raw32203step1; decide +kernel
      have hl : raw32203step1Labels = labelEmbedding6 ∘ raw32203step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32203step1 raw32203step1Labels raw32203step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4949 node4949Labels := by rfl

def raw32204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32204step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32204step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32204step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32204 raw32204Labels = mixedMoment B node5038 node5038Labels := by
  calc
    mixedMoment B raw32204 raw32204Labels = mixedMoment B raw32204step0 raw32204step0Labels := by
      have ha : raw32204step0 = (fun i j => raw32204 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32204step0 raw32204; decide +kernel
      have hl : raw32204step0Labels = raw32204Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32204 raw32204Labels permutation179 permutation3
    mixedMoment B raw32204step0 raw32204step0Labels = mixedMoment B raw32204step1 raw32204step1Labels := by
      have ha : raw32204step1 = raw32204step0 := by apply Matrix.ext; unfold raw32204step1 raw32204step0; decide +kernel
      have hl : raw32204step0Labels = labelEmbedding6 ∘ raw32204step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32204step0 raw32204step0Labels raw32204step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5038 node5038Labels := by rfl

def raw32205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw32205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32205step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw32205step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32205step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32205step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32205step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32205step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32205 raw32205Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw32205 raw32205Labels = mixedMoment B raw32205step0 raw32205step0Labels := by
      have hz : ∀ j, raw32205 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32205step0 = (fun i j => raw32205 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32205step0 raw32205; decide +kernel
      have hl : raw32205step0Labels = raw32205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32205 raw32205Labels permutation520 hz
    mixedMoment B raw32205step0 raw32205step0Labels = mixedMoment B raw32205step1 raw32205step1Labels := by
      have hz : ∀ j, raw32205step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32205step1 = (fun i j => raw32205step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32205step1 raw32205step0; decide +kernel
      have hl : raw32205step1Labels = raw32205step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32205step0 raw32205step0Labels permutation80 hz
    mixedMoment B raw32205step1 raw32205step1Labels = mixedMoment B raw32205step2 raw32205step2Labels := by
      have ha : raw32205step2 = (fun i j => raw32205step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32205step2 raw32205step1; decide +kernel
      have hl : raw32205step2Labels = raw32205step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32205step1 raw32205step1Labels permutation9 permutation3
    mixedMoment B raw32205step2 raw32205step2Labels = mixedMoment B raw32205step3 raw32205step3Labels := by
      have ha : raw32205step3 = raw32205step2 := by apply Matrix.ext; unfold raw32205step3 raw32205step2; decide +kernel
      have hl : raw32205step2Labels = labelEmbedding6 ∘ raw32205step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32205step2 raw32205step2Labels raw32205step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5176 node5176Labels := by rfl

def raw32206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32206step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32206step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32206step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32206step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32206 raw32206Labels = mixedMoment B node4949 node4949Labels := by
  calc
    mixedMoment B raw32206 raw32206Labels = mixedMoment B raw32206step0 raw32206step0Labels := by
      have hz : ∀ j, raw32206 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32206step0 = (fun i j => raw32206 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32206step0 raw32206; decide +kernel
      have hl : raw32206step0Labels = raw32206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32206 raw32206Labels permutation346 hz
    mixedMoment B raw32206step0 raw32206step0Labels = mixedMoment B raw32206step1 raw32206step1Labels := by
      have ha : raw32206step1 = (fun i j => raw32206step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32206step1 raw32206step0; decide +kernel
      have hl : raw32206step1Labels = raw32206step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32206step0 raw32206step0Labels permutation33 permutation3
    mixedMoment B raw32206step1 raw32206step1Labels = mixedMoment B raw32206step2 raw32206step2Labels := by
      have ha : raw32206step2 = raw32206step1 := by apply Matrix.ext; unfold raw32206step2 raw32206step1; decide +kernel
      have hl : raw32206step1Labels = labelEmbedding6 ∘ raw32206step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32206step1 raw32206step1Labels raw32206step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4949 node4949Labels := by rfl

def raw32207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32207step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32207step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32207step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32207 raw32207Labels = mixedMoment B node5038 node5038Labels := by
  calc
    mixedMoment B raw32207 raw32207Labels = mixedMoment B raw32207step0 raw32207step0Labels := by
      have ha : raw32207step0 = (fun i j => raw32207 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32207step0 raw32207; decide +kernel
      have hl : raw32207step0Labels = raw32207Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32207 raw32207Labels permutation177 permutation3
    mixedMoment B raw32207step0 raw32207step0Labels = mixedMoment B raw32207step1 raw32207step1Labels := by
      have ha : raw32207step1 = raw32207step0 := by apply Matrix.ext; unfold raw32207step1 raw32207step0; decide +kernel
      have hl : raw32207step0Labels = labelEmbedding6 ∘ raw32207step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32207step0 raw32207step0Labels raw32207step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5038 node5038Labels := by rfl

def raw32208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32208step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32208step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32208 raw32208Labels = mixedMoment B node4948 node4948Labels := by
  calc
    mixedMoment B raw32208 raw32208Labels = mixedMoment B raw32208step0 raw32208step0Labels := by
      have hz : ∀ j, raw32208 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32208step0 = (fun i j => raw32208 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32208step0 raw32208; decide +kernel
      have hl : raw32208step0Labels = raw32208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32208 raw32208Labels permutation346 hz
    mixedMoment B raw32208step0 raw32208step0Labels = mixedMoment B raw32208step1 raw32208step1Labels := by
      have ha : raw32208step1 = (fun i j => raw32208step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32208step1 raw32208step0; decide +kernel
      have hl : raw32208step1Labels = raw32208step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32208step0 raw32208step0Labels permutation32 permutation3
    mixedMoment B raw32208step1 raw32208step1Labels = mixedMoment B raw32208step2 raw32208step2Labels := by
      have ha : raw32208step2 = raw32208step1 := by apply Matrix.ext; unfold raw32208step2 raw32208step1; decide +kernel
      have hl : raw32208step1Labels = labelEmbedding6 ∘ raw32208step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32208step1 raw32208step1Labels raw32208step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4948 node4948Labels := by rfl

def raw32209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32209step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32209step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32209step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32209 raw32209Labels = mixedMoment B node5037 node5037Labels := by
  calc
    mixedMoment B raw32209 raw32209Labels = mixedMoment B raw32209step0 raw32209step0Labels := by
      have ha : raw32209step0 = (fun i j => raw32209 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32209step0 raw32209; decide +kernel
      have hl : raw32209step0Labels = raw32209Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32209 raw32209Labels permutation176 permutation3
    mixedMoment B raw32209step0 raw32209step0Labels = mixedMoment B raw32209step1 raw32209step1Labels := by
      have ha : raw32209step1 = raw32209step0 := by apply Matrix.ext; unfold raw32209step1 raw32209step0; decide +kernel
      have hl : raw32209step0Labels = labelEmbedding6 ∘ raw32209step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32209step0 raw32209step0Labels raw32209step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5037 node5037Labels := by rfl

def raw32210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw32210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32210step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32210step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw32210step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32210step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw32210step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32210step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32210step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32210 raw32210Labels = mixedMoment B node5174 node5174Labels := by
  calc
    mixedMoment B raw32210 raw32210Labels = mixedMoment B raw32210step0 raw32210step0Labels := by
      have hz : ∀ j, raw32210 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32210step0 = (fun i j => raw32210 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32210step0 raw32210; decide +kernel
      have hl : raw32210step0Labels = raw32210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32210 raw32210Labels permutation520 hz
    mixedMoment B raw32210step0 raw32210step0Labels = mixedMoment B raw32210step1 raw32210step1Labels := by
      have hz : ∀ j, raw32210step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32210step1 = (fun i j => raw32210step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32210step1 raw32210step0; decide +kernel
      have hl : raw32210step1Labels = raw32210step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32210step0 raw32210step0Labels permutation80 hz
    mixedMoment B raw32210step1 raw32210step1Labels = mixedMoment B raw32210step2 raw32210step2Labels := by
      have ha : raw32210step2 = (fun i j => raw32210step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32210step2 raw32210step1; decide +kernel
      have hl : raw32210step2Labels = raw32210step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32210step1 raw32210step1Labels permutation31 permutation2
    mixedMoment B raw32210step2 raw32210step2Labels = mixedMoment B raw32210step3 raw32210step3Labels := by
      have ha : raw32210step3 = -raw32210step2 := by apply Matrix.ext; change ∀ i j, raw32210step3 i j = -(raw32210step2 i j); unfold raw32210step3 raw32210step2; decide +kernel
      have hl : raw32210step3Labels = raw32210step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5174 node5174Labels := by rfl

def raw32211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32211Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32211step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32211step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32211 raw32211Labels = mixedMoment B node3933 node3933Labels := by
  calc
    mixedMoment B raw32211 raw32211Labels = mixedMoment B raw32211step0 raw32211step0Labels := by
      have hz : ∀ j, raw32211 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32211step0 = (fun i j => raw32211 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32211step0 raw32211; decide +kernel
      have hl : raw32211step0Labels = raw32211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32211 raw32211Labels permutation346 hz
    mixedMoment B raw32211step0 raw32211step0Labels = mixedMoment B raw32211step1 raw32211step1Labels := by
      have ha : raw32211step1 = (fun i j => raw32211step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32211step1 raw32211step0; decide +kernel
      have hl : raw32211step1Labels = raw32211step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32211step0 raw32211step0Labels permutation32 permutation3
    _ = mixedMoment B node3933 node3933Labels := by rfl

def raw32212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32212Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32212step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32212 raw32212Labels = mixedMoment B node3967 node3967Labels := by
  calc
    mixedMoment B raw32212 raw32212Labels = mixedMoment B raw32212step0 raw32212step0Labels := by
      have ha : raw32212step0 = (fun i j => raw32212 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32212step0 raw32212; decide +kernel
      have hl : raw32212step0Labels = raw32212Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32212 raw32212Labels permutation176 permutation3
    _ = mixedMoment B node3967 node3967Labels := by rfl

def raw32213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw32213Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32213step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32213step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32213step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32213step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32213 raw32213Labels = mixedMoment B node4001 node4001Labels := by
  calc
    mixedMoment B raw32213 raw32213Labels = mixedMoment B raw32213step0 raw32213step0Labels := by
      have hz : ∀ j, raw32213 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32213step0 = (fun i j => raw32213 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32213step0 raw32213; decide +kernel
      have hl : raw32213step0Labels = raw32213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32213 raw32213Labels permutation520 hz
    mixedMoment B raw32213step0 raw32213step0Labels = mixedMoment B raw32213step1 raw32213step1Labels := by
      have hz : ∀ j, raw32213step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32213step1 = (fun i j => raw32213step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32213step1 raw32213step0; decide +kernel
      have hl : raw32213step1Labels = raw32213step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32213step0 raw32213step0Labels permutation80 hz
    mixedMoment B raw32213step1 raw32213step1Labels = mixedMoment B raw32213step2 raw32213step2Labels := by
      have ha : raw32213step2 = (fun i j => raw32213step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32213step2 raw32213step1; decide +kernel
      have hl : raw32213step2Labels = raw32213step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32213step1 raw32213step1Labels permutation8 permutation3
    _ = mixedMoment B node4001 node4001Labels := by rfl

def raw32214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32214Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32214step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32214 raw32214Labels = mixedMoment B node2338 node2338Labels := by
  calc
    mixedMoment B raw32214 raw32214Labels = mixedMoment B raw32214step0 raw32214step0Labels := by
      have ha : raw32214step0 = (fun i j => raw32214 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32214step0 raw32214; decide +kernel
      have hl : raw32214step0Labels = raw32214Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32214 raw32214Labels permutation152 permutation3
    _ = mixedMoment B node2338 node2338Labels := by rfl

def raw32215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32215Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32215step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32215step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32215 raw32215Labels = mixedMoment B node2599 node2599Labels := by
  calc
    mixedMoment B raw32215 raw32215Labels = mixedMoment B raw32215step0 raw32215step0Labels := by
      have hz : ∀ j, raw32215 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32215step0 = (fun i j => raw32215 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32215step0 raw32215; decide +kernel
      have hl : raw32215step0Labels = raw32215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32215 raw32215Labels permutation434 hz
    mixedMoment B raw32215step0 raw32215step0Labels = mixedMoment B raw32215step1 raw32215step1Labels := by
      have ha : raw32215step1 = (fun i j => raw32215step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32215step1 raw32215step0; decide +kernel
      have hl : raw32215step1Labels = raw32215step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32215step0 raw32215step0Labels permutation32 permutation3
    _ = mixedMoment B node2599 node2599Labels := by rfl

def raw32216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw32216Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32216step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32216step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32216 raw32216Labels = mixedMoment B node2599 node2599Labels := by
  calc
    mixedMoment B raw32216 raw32216Labels = mixedMoment B raw32216step0 raw32216step0Labels := by
      have hz : ∀ j, raw32216 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32216step0 = (fun i j => raw32216 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32216step0 raw32216; decide +kernel
      have hl : raw32216step0Labels = raw32216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32216 raw32216Labels permutation520 hz
    mixedMoment B raw32216step0 raw32216step0Labels = mixedMoment B raw32216step1 raw32216step1Labels := by
      have ha : raw32216step1 = (fun i j => raw32216step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32216step1 raw32216step0; decide +kernel
      have hl : raw32216step1Labels = raw32216step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32216step0 raw32216step0Labels permutation32 permutation3
    _ = mixedMoment B node2599 node2599Labels := by rfl

def raw32217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32217Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32217step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32217step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32217 raw32217Labels = mixedMoment B node2341 node2341Labels := by
  calc
    mixedMoment B raw32217 raw32217Labels = mixedMoment B raw32217step0 raw32217step0Labels := by
      have hz : ∀ j, raw32217 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32217step0 = (fun i j => raw32217 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32217step0 raw32217; decide +kernel
      have hl : raw32217step0Labels = raw32217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32217 raw32217Labels permutation346 hz
    mixedMoment B raw32217step0 raw32217step0Labels = mixedMoment B raw32217step1 raw32217step1Labels := by
      have ha : raw32217step1 = (fun i j => raw32217step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32217step1 raw32217step0; decide +kernel
      have hl : raw32217step1Labels = raw32217step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32217step0 raw32217step0Labels permutation35 permutation3
    _ = mixedMoment B node2341 node2341Labels := by rfl

def raw32218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32218Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32218 raw32218Labels = mixedMoment B node2431 node2431Labels := by
  calc
    mixedMoment B raw32218 raw32218Labels = mixedMoment B raw32218step0 raw32218step0Labels := by
      have ha : raw32218step0 = (fun i j => raw32218 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32218step0 raw32218; decide +kernel
      have hl : raw32218step0Labels = raw32218Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32218 raw32218Labels permutation179 permutation3
    _ = mixedMoment B node2431 node2431Labels := by rfl

def raw32219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw32219Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32219step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32219step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw32219step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32219step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32219step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32219 raw32219Labels = mixedMoment B node2604 node2604Labels := by
  calc
    mixedMoment B raw32219 raw32219Labels = mixedMoment B raw32219step0 raw32219step0Labels := by
      have hz : ∀ j, raw32219 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32219step0 = (fun i j => raw32219 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32219step0 raw32219; decide +kernel
      have hl : raw32219step0Labels = raw32219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32219 raw32219Labels permutation520 hz
    mixedMoment B raw32219step0 raw32219step0Labels = mixedMoment B raw32219step1 raw32219step1Labels := by
      have hz : ∀ j, raw32219step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32219step1 = (fun i j => raw32219step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32219step1 raw32219step0; decide +kernel
      have hl : raw32219step1Labels = raw32219step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32219step0 raw32219step0Labels permutation80 hz
    mixedMoment B raw32219step1 raw32219step1Labels = mixedMoment B raw32219step2 raw32219step2Labels := by
      have ha : raw32219step2 = (fun i j => raw32219step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32219step2 raw32219step1; decide +kernel
      have hl : raw32219step2Labels = raw32219step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32219step1 raw32219step1Labels permutation9 permutation3
    _ = mixedMoment B node2604 node2604Labels := by rfl

def raw32220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32220Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32220step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32220step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32220 raw32220Labels = mixedMoment B node2341 node2341Labels := by
  calc
    mixedMoment B raw32220 raw32220Labels = mixedMoment B raw32220step0 raw32220step0Labels := by
      have hz : ∀ j, raw32220 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32220step0 = (fun i j => raw32220 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32220step0 raw32220; decide +kernel
      have hl : raw32220step0Labels = raw32220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32220 raw32220Labels permutation346 hz
    mixedMoment B raw32220step0 raw32220step0Labels = mixedMoment B raw32220step1 raw32220step1Labels := by
      have ha : raw32220step1 = (fun i j => raw32220step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32220step1 raw32220step0; decide +kernel
      have hl : raw32220step1Labels = raw32220step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32220step0 raw32220step0Labels permutation33 permutation3
    _ = mixedMoment B node2341 node2341Labels := by rfl

def raw32221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw32221Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32221step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32221 raw32221Labels = mixedMoment B node2431 node2431Labels := by
  calc
    mixedMoment B raw32221 raw32221Labels = mixedMoment B raw32221step0 raw32221step0Labels := by
      have ha : raw32221step0 = (fun i j => raw32221 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32221step0 raw32221; decide +kernel
      have hl : raw32221step0Labels = raw32221Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32221 raw32221Labels permutation177 permutation3
    _ = mixedMoment B node2431 node2431Labels := by rfl

def raw32222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32222Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32222step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32222step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32222 raw32222Labels = mixedMoment B node2339 node2339Labels := by
  calc
    mixedMoment B raw32222 raw32222Labels = mixedMoment B raw32222step0 raw32222step0Labels := by
      have hz : ∀ j, raw32222 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32222step0 = (fun i j => raw32222 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32222step0 raw32222; decide +kernel
      have hl : raw32222step0Labels = raw32222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32222 raw32222Labels permutation346 hz
    mixedMoment B raw32222step0 raw32222step0Labels = mixedMoment B raw32222step1 raw32222step1Labels := by
      have ha : raw32222step1 = (fun i j => raw32222step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32222step1 raw32222step0; decide +kernel
      have hl : raw32222step1Labels = raw32222step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32222step0 raw32222step0Labels permutation32 permutation3
    _ = mixedMoment B node2339 node2339Labels := by rfl

def raw32223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32223Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32223step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32223step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32223 raw32223Labels = mixedMoment B node2429 node2429Labels := by
  calc
    mixedMoment B raw32223 raw32223Labels = mixedMoment B raw32223step0 raw32223step0Labels := by
      have ha : raw32223step0 = (fun i j => raw32223 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32223step0 raw32223; decide +kernel
      have hl : raw32223step0Labels = raw32223Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32223 raw32223Labels permutation176 permutation3
    _ = mixedMoment B node2429 node2429Labels := by rfl

def raw32224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw32224Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw32224step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32224step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw32224step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32224step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw32224step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32224 raw32224Labels = mixedMoment B node2601 node2601Labels := by
  calc
    mixedMoment B raw32224 raw32224Labels = mixedMoment B raw32224step0 raw32224step0Labels := by
      have hz : ∀ j, raw32224 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32224step0 = (fun i j => raw32224 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32224step0 raw32224; decide +kernel
      have hl : raw32224step0Labels = raw32224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32224 raw32224Labels permutation520 hz
    mixedMoment B raw32224step0 raw32224step0Labels = mixedMoment B raw32224step1 raw32224step1Labels := by
      have hz : ∀ j, raw32224step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw32224step1 = (fun i j => raw32224step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw32224step1 raw32224step0; decide +kernel
      have hl : raw32224step1Labels = raw32224step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32224step0 raw32224step0Labels permutation80 hz
    mixedMoment B raw32224step1 raw32224step1Labels = mixedMoment B raw32224step2 raw32224step2Labels := by
      have ha : raw32224step2 = (fun i j => raw32224step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32224step2 raw32224step1; decide +kernel
      have hl : raw32224step2Labels = raw32224step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32224step1 raw32224step1Labels permutation8 permutation3
    _ = mixedMoment B node2601 node2601Labels := by rfl

def raw32225 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32225step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32225step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32225step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32225step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32225 raw32225Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw32225 raw32225Labels = mixedMoment B raw32225step0 raw32225step0Labels := by
      have hz : ∀ j, raw32225 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32225step0 = (fun i j => raw32225 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32225step0 raw32225; decide +kernel
      have hl : raw32225step0Labels = raw32225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32225 raw32225Labels permutation346 hz
    mixedMoment B raw32225step0 raw32225step0Labels = mixedMoment B raw32225step1 raw32225step1Labels := by
      have ha : raw32225step1 = (fun i j => raw32225step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32225step1 raw32225step0; decide +kernel
      have hl : raw32225step1Labels = raw32225step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32225step0 raw32225step0Labels permutation32 permutation7
    mixedMoment B raw32225step1 raw32225step1Labels = mixedMoment B raw32225step2 raw32225step2Labels := by
      have ha : raw32225step2 = raw32225step1 := by apply Matrix.ext; unfold raw32225step2 raw32225step1; decide +kernel
      have hl : raw32225step1Labels = labelEmbedding10 ∘ raw32225step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32225step1 raw32225step1Labels raw32225step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5168 node5168Labels := by rfl

def raw32226 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32226step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32226step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32226step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32226 raw32226Labels = mixedMoment B node5072 node5072Labels := by
  calc
    mixedMoment B raw32226 raw32226Labels = mixedMoment B raw32226step0 raw32226step0Labels := by
      have ha : raw32226step0 = (fun i j => raw32226 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32226step0 raw32226; decide +kernel
      have hl : raw32226step0Labels = raw32226Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32226 raw32226Labels permutation152 permutation7
    mixedMoment B raw32226step0 raw32226step0Labels = mixedMoment B raw32226step1 raw32226step1Labels := by
      have ha : raw32226step1 = raw32226step0 := by apply Matrix.ext; unfold raw32226step1 raw32226step0; decide +kernel
      have hl : raw32226step0Labels = labelEmbedding10 ∘ raw32226step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32226step0 raw32226step0Labels raw32226step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5072 node5072Labels := by rfl

def raw32227 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32227step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32227step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32227step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32227 raw32227Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw32227 raw32227Labels = mixedMoment B raw32227step0 raw32227step0Labels := by
      have hz : ∀ j, raw32227 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32227step0 = (fun i j => raw32227 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32227step0 raw32227; decide +kernel
      have hl : raw32227step0Labels = raw32227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32227 raw32227Labels permutation346 hz
    mixedMoment B raw32227step0 raw32227step0Labels = mixedMoment B raw32227step1 raw32227step1Labels := by
      have ha : raw32227step1 = (fun i j => raw32227step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32227step1 raw32227step0; decide +kernel
      have hl : raw32227step1Labels = raw32227step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32227step0 raw32227step0Labels permutation34 permutation7
    mixedMoment B raw32227step1 raw32227step1Labels = mixedMoment B raw32227step2 raw32227step2Labels := by
      have ha : raw32227step2 = raw32227step1 := by apply Matrix.ext; unfold raw32227step2 raw32227step1; decide +kernel
      have hl : raw32227step1Labels = labelEmbedding10 ∘ raw32227step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32227step1 raw32227step1Labels raw32227step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5101 node5101Labels := by rfl

def raw32228 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32228step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32228step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32228step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32228 raw32228Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw32228 raw32228Labels = mixedMoment B raw32228step0 raw32228step0Labels := by
      have hz : ∀ j, raw32228 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32228step0 = (fun i j => raw32228 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32228step0 raw32228; decide +kernel
      have hl : raw32228step0Labels = raw32228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32228 raw32228Labels permutation346 hz
    mixedMoment B raw32228step0 raw32228step0Labels = mixedMoment B raw32228step1 raw32228step1Labels := by
      have ha : raw32228step1 = (fun i j => raw32228step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32228step1 raw32228step0; decide +kernel
      have hl : raw32228step1Labels = raw32228step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32228step0 raw32228step0Labels permutation32 permutation7
    mixedMoment B raw32228step1 raw32228step1Labels = mixedMoment B raw32228step2 raw32228step2Labels := by
      have ha : raw32228step2 = raw32228step1 := by apply Matrix.ext; unfold raw32228step2 raw32228step1; decide +kernel
      have hl : raw32228step1Labels = labelEmbedding10 ∘ raw32228step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32228step1 raw32228step1Labels raw32228step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5101 node5101Labels := by rfl

def raw32229 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw32229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw32229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32229step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32229step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw32229step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32229 raw32229Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw32229 raw32229Labels = mixedMoment B raw32229step0 raw32229step0Labels := by
      have hz : ∀ j, raw32229 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32229step0 = (fun i j => raw32229 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32229step0 raw32229; decide +kernel
      have hl : raw32229step0Labels = raw32229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32229 raw32229Labels permutation346 hz
    mixedMoment B raw32229step0 raw32229step0Labels = mixedMoment B raw32229step1 raw32229step1Labels := by
      have ha : raw32229step1 = (fun i j => raw32229step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32229step1 raw32229step0; decide +kernel
      have hl : raw32229step1Labels = raw32229step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32229step0 raw32229step0Labels permutation32 permutation7
    mixedMoment B raw32229step1 raw32229step1Labels = mixedMoment B raw32229step2 raw32229step2Labels := by
      have ha : raw32229step2 = raw32229step1 := by apply Matrix.ext; unfold raw32229step2 raw32229step1; decide +kernel
      have hl : raw32229step1Labels = labelEmbedding10 ∘ raw32229step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32229step1 raw32229step1Labels raw32229step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5099 node5099Labels := by rfl

def raw32230 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32230step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32230step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32230step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32230 raw32230Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw32230 raw32230Labels = mixedMoment B raw32230step0 raw32230step0Labels := by
      have hz : ∀ j, raw32230 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32230step0 = (fun i j => raw32230 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32230step0 raw32230; decide +kernel
      have hl : raw32230step0Labels = raw32230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32230 raw32230Labels permutation346 hz
    mixedMoment B raw32230step0 raw32230step0Labels = mixedMoment B raw32230step1 raw32230step1Labels := by
      have ha : raw32230step1 = (fun i j => raw32230step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32230step1 raw32230step0; decide +kernel
      have hl : raw32230step1Labels = raw32230step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32230step0 raw32230step0Labels permutation32 permutation6
    mixedMoment B raw32230step1 raw32230step1Labels = mixedMoment B raw32230step2 raw32230step2Labels := by
      have ha : raw32230step2 = raw32230step1 := by apply Matrix.ext; unfold raw32230step2 raw32230step1; decide +kernel
      have hl : raw32230step1Labels = labelEmbedding9 ∘ raw32230step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32230step1 raw32230step1Labels raw32230step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

def raw32231 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32231step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32231step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32231step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32231 raw32231Labels = mixedMoment B node5187 node5187Labels := by
  calc
    mixedMoment B raw32231 raw32231Labels = mixedMoment B raw32231step0 raw32231step0Labels := by
      have ha : raw32231step0 = (fun i j => raw32231 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32231step0 raw32231; decide +kernel
      have hl : raw32231step0Labels = raw32231Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32231 raw32231Labels permutation152 permutation6
    mixedMoment B raw32231step0 raw32231step0Labels = mixedMoment B raw32231step1 raw32231step1Labels := by
      have ha : raw32231step1 = raw32231step0 := by apply Matrix.ext; unfold raw32231step1 raw32231step0; decide +kernel
      have hl : raw32231step0Labels = labelEmbedding9 ∘ raw32231step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32231step0 raw32231step0Labels raw32231step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5187 node5187Labels := by rfl

def raw32232 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32232step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32232step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32232step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32232 raw32232Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw32232 raw32232Labels = mixedMoment B raw32232step0 raw32232step0Labels := by
      have hz : ∀ j, raw32232 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32232step0 = (fun i j => raw32232 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32232step0 raw32232; decide +kernel
      have hl : raw32232step0Labels = raw32232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32232 raw32232Labels permutation346 hz
    mixedMoment B raw32232step0 raw32232step0Labels = mixedMoment B raw32232step1 raw32232step1Labels := by
      have ha : raw32232step1 = (fun i j => raw32232step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32232step1 raw32232step0; decide +kernel
      have hl : raw32232step1Labels = raw32232step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32232step0 raw32232step0Labels permutation32 permutation6
    mixedMoment B raw32232step1 raw32232step1Labels = mixedMoment B raw32232step2 raw32232step2Labels := by
      have ha : raw32232step2 = raw32232step1 := by apply Matrix.ext; unfold raw32232step2 raw32232step1; decide +kernel
      have hl : raw32232step1Labels = labelEmbedding9 ∘ raw32232step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32232step1 raw32232step1Labels raw32232step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw32233 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32233step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32233step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32233step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32233 raw32233Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw32233 raw32233Labels = mixedMoment B raw32233step0 raw32233step0Labels := by
      have hz : ∀ j, raw32233 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32233step0 = (fun i j => raw32233 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32233step0 raw32233; decide +kernel
      have hl : raw32233step0Labels = raw32233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32233 raw32233Labels permutation346 hz
    mixedMoment B raw32233step0 raw32233step0Labels = mixedMoment B raw32233step1 raw32233step1Labels := by
      have ha : raw32233step1 = (fun i j => raw32233step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32233step1 raw32233step0; decide +kernel
      have hl : raw32233step1Labels = raw32233step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32233step0 raw32233step0Labels permutation34 permutation6
    mixedMoment B raw32233step1 raw32233step1Labels = mixedMoment B raw32233step2 raw32233step2Labels := by
      have ha : raw32233step2 = raw32233step1 := by apply Matrix.ext; unfold raw32233step2 raw32233step1; decide +kernel
      have hl : raw32233step1Labels = labelEmbedding9 ∘ raw32233step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32233step1 raw32233step1Labels raw32233step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw32234 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw32234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw32234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw32234step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32234step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw32234step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32234 raw32234Labels = mixedMoment B node5205 node5205Labels := by
  calc
    mixedMoment B raw32234 raw32234Labels = mixedMoment B raw32234step0 raw32234step0Labels := by
      have hz : ∀ j, raw32234 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32234step0 = (fun i j => raw32234 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32234step0 raw32234; decide +kernel
      have hl : raw32234step0Labels = raw32234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32234 raw32234Labels permutation346 hz
    mixedMoment B raw32234step0 raw32234step0Labels = mixedMoment B raw32234step1 raw32234step1Labels := by
      have ha : raw32234step1 = (fun i j => raw32234step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32234step1 raw32234step0; decide +kernel
      have hl : raw32234step1Labels = raw32234step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32234step0 raw32234step0Labels permutation32 permutation6
    mixedMoment B raw32234step1 raw32234step1Labels = mixedMoment B raw32234step2 raw32234step2Labels := by
      have ha : raw32234step2 = raw32234step1 := by apply Matrix.ext; unfold raw32234step2 raw32234step1; decide +kernel
      have hl : raw32234step1Labels = labelEmbedding9 ∘ raw32234step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32234step1 raw32234step1Labels raw32234step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5205 node5205Labels := by rfl

def raw32235 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32235step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32235step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32235step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32235 raw32235Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw32235 raw32235Labels = mixedMoment B raw32235step0 raw32235step0Labels := by
      have ha : raw32235step0 = (fun i j => raw32235 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32235step0 raw32235; decide +kernel
      have hl : raw32235step0Labels = raw32235Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32235 raw32235Labels permutation152 permutation6
    mixedMoment B raw32235step0 raw32235step0Labels = mixedMoment B raw32235step1 raw32235step1Labels := by
      have ha : raw32235step1 = raw32235step0 := by apply Matrix.ext; unfold raw32235step1 raw32235step0; decide +kernel
      have hl : raw32235step0Labels = labelEmbedding9 ∘ raw32235step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32235step0 raw32235step0Labels raw32235step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

def raw32236 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32236step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32236step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32236 raw32236Labels = mixedMoment B node5076 node5076Labels := by
  calc
    mixedMoment B raw32236 raw32236Labels = mixedMoment B raw32236step0 raw32236step0Labels := by
      have ha : raw32236step0 = (fun i j => raw32236 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32236step0 raw32236; decide +kernel
      have hl : raw32236step0Labels = raw32236Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32236 raw32236Labels permutation152 permutation6
    mixedMoment B raw32236step0 raw32236step0Labels = mixedMoment B raw32236step1 raw32236step1Labels := by
      have ha : raw32236step1 = raw32236step0 := by apply Matrix.ext; unfold raw32236step1 raw32236step0; decide +kernel
      have hl : raw32236step0Labels = labelEmbedding9 ∘ raw32236step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32236step0 raw32236step0Labels raw32236step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5076 node5076Labels := by rfl

def raw32237 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32237step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32237step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32237step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32237 raw32237Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw32237 raw32237Labels = mixedMoment B raw32237step0 raw32237step0Labels := by
      have ha : raw32237step0 = (fun i j => raw32237 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32237step0 raw32237; decide +kernel
      have hl : raw32237step0Labels = raw32237Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32237 raw32237Labels permutation152 permutation6
    mixedMoment B raw32237step0 raw32237step0Labels = mixedMoment B raw32237step1 raw32237step1Labels := by
      have ha : raw32237step1 = raw32237step0 := by apply Matrix.ext; unfold raw32237step1 raw32237step0; decide +kernel
      have hl : raw32237step0Labels = labelEmbedding9 ∘ raw32237step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32237step0 raw32237step0Labels raw32237step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw32238 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32238step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32238step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32238 raw32238Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw32238 raw32238Labels = mixedMoment B raw32238step0 raw32238step0Labels := by
      have ha : raw32238step0 = (fun i j => raw32238 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32238step0 raw32238; decide +kernel
      have hl : raw32238step0Labels = raw32238Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32238 raw32238Labels permutation154 permutation6
    mixedMoment B raw32238step0 raw32238step0Labels = mixedMoment B raw32238step1 raw32238step1Labels := by
      have ha : raw32238step1 = raw32238step0 := by apply Matrix.ext; unfold raw32238step1 raw32238step0; decide +kernel
      have hl : raw32238step0Labels = labelEmbedding9 ∘ raw32238step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32238step0 raw32238step0Labels raw32238step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw32239 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw32239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw32239step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32239step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw32239step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32239 raw32239Labels = mixedMoment B node5150 node5150Labels := by
  calc
    mixedMoment B raw32239 raw32239Labels = mixedMoment B raw32239step0 raw32239step0Labels := by
      have ha : raw32239step0 = (fun i j => raw32239 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32239step0 raw32239; decide +kernel
      have hl : raw32239step0Labels = raw32239Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32239 raw32239Labels permutation152 permutation6
    mixedMoment B raw32239step0 raw32239step0Labels = mixedMoment B raw32239step1 raw32239step1Labels := by
      have ha : raw32239step1 = raw32239step0 := by apply Matrix.ext; unfold raw32239step1 raw32239step0; decide +kernel
      have hl : raw32239step0Labels = labelEmbedding9 ∘ raw32239step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32239step0 raw32239step0Labels raw32239step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5150 node5150Labels := by rfl

def raw32240 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32240step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32240step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32240step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32240 raw32240Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw32240 raw32240Labels = mixedMoment B raw32240step0 raw32240step0Labels := by
      have hz : ∀ j, raw32240 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32240step0 = (fun i j => raw32240 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32240step0 raw32240; decide +kernel
      have hl : raw32240step0Labels = raw32240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32240 raw32240Labels permutation346 hz
    mixedMoment B raw32240step0 raw32240step0Labels = mixedMoment B raw32240step1 raw32240step1Labels := by
      have ha : raw32240step1 = (fun i j => raw32240step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32240step1 raw32240step0; decide +kernel
      have hl : raw32240step1Labels = raw32240step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32240step0 raw32240step0Labels permutation34 permutation6
    mixedMoment B raw32240step1 raw32240step1Labels = mixedMoment B raw32240step2 raw32240step2Labels := by
      have ha : raw32240step2 = raw32240step1 := by apply Matrix.ext; unfold raw32240step2 raw32240step1; decide +kernel
      have hl : raw32240step1Labels = labelEmbedding9 ∘ raw32240step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32240step1 raw32240step1Labels raw32240step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw32241 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32241step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32241step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32241step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32241 raw32241Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw32241 raw32241Labels = mixedMoment B raw32241step0 raw32241step0Labels := by
      have hz : ∀ j, raw32241 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32241step0 = (fun i j => raw32241 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32241step0 raw32241; decide +kernel
      have hl : raw32241step0Labels = raw32241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32241 raw32241Labels permutation346 hz
    mixedMoment B raw32241step0 raw32241step0Labels = mixedMoment B raw32241step1 raw32241step1Labels := by
      have ha : raw32241step1 = (fun i j => raw32241step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32241step1 raw32241step0; decide +kernel
      have hl : raw32241step1Labels = raw32241step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32241step0 raw32241step0Labels permutation34 permutation6
    mixedMoment B raw32241step1 raw32241step1Labels = mixedMoment B raw32241step2 raw32241step2Labels := by
      have ha : raw32241step2 = raw32241step1 := by apply Matrix.ext; unfold raw32241step2 raw32241step1; decide +kernel
      have hl : raw32241step1Labels = labelEmbedding9 ∘ raw32241step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32241step1 raw32241step1Labels raw32241step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw32242 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw32242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32242step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32242step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32242step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32242step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32242 raw32242Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw32242 raw32242Labels = mixedMoment B raw32242step0 raw32242step0Labels := by
      have ha : raw32242step0 = (fun i j => raw32242 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32242step0 raw32242; decide +kernel
      have hl : raw32242step0Labels = raw32242Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32242 raw32242Labels permutation154 permutation6
    mixedMoment B raw32242step0 raw32242step0Labels = mixedMoment B raw32242step1 raw32242step1Labels := by
      have ha : raw32242step1 = raw32242step0 := by apply Matrix.ext; unfold raw32242step1 raw32242step0; decide +kernel
      have hl : raw32242step0Labels = labelEmbedding9 ∘ raw32242step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32242step0 raw32242step0Labels raw32242step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5138 node5138Labels := by rfl

def raw32243 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32243step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32243step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32243step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32243 raw32243Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw32243 raw32243Labels = mixedMoment B raw32243step0 raw32243step0Labels := by
      have hz : ∀ j, raw32243 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32243step0 = (fun i j => raw32243 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32243step0 raw32243; decide +kernel
      have hl : raw32243step0Labels = raw32243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32243 raw32243Labels permutation346 hz
    mixedMoment B raw32243step0 raw32243step0Labels = mixedMoment B raw32243step1 raw32243step1Labels := by
      have ha : raw32243step1 = (fun i j => raw32243step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32243step1 raw32243step0; decide +kernel
      have hl : raw32243step1Labels = raw32243step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32243step0 raw32243step0Labels permutation34 permutation6
    mixedMoment B raw32243step1 raw32243step1Labels = mixedMoment B raw32243step2 raw32243step2Labels := by
      have ha : raw32243step2 = raw32243step1 := by apply Matrix.ext; unfold raw32243step2 raw32243step1; decide +kernel
      have hl : raw32243step1Labels = labelEmbedding9 ∘ raw32243step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32243step1 raw32243step1Labels raw32243step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw32244 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw32244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw32244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw32244step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32244step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw32244step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32244 raw32244Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw32244 raw32244Labels = mixedMoment B raw32244step0 raw32244step0Labels := by
      have hz : ∀ j, raw32244 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32244step0 = (fun i j => raw32244 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32244step0 raw32244; decide +kernel
      have hl : raw32244step0Labels = raw32244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32244 raw32244Labels permutation346 hz
    mixedMoment B raw32244step0 raw32244step0Labels = mixedMoment B raw32244step1 raw32244step1Labels := by
      have ha : raw32244step1 = (fun i j => raw32244step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32244step1 raw32244step0; decide +kernel
      have hl : raw32244step1Labels = raw32244step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32244step0 raw32244step0Labels permutation34 permutation6
    mixedMoment B raw32244step1 raw32244step1Labels = mixedMoment B raw32244step2 raw32244step2Labels := by
      have ha : raw32244step2 = raw32244step1 := by apply Matrix.ext; unfold raw32244step2 raw32244step1; decide +kernel
      have hl : raw32244step1Labels = labelEmbedding9 ∘ raw32244step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32244step1 raw32244step1Labels raw32244step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

def raw32245 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw32245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw32245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32245step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32245step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32245step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32245 raw32245Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw32245 raw32245Labels = mixedMoment B raw32245step0 raw32245step0Labels := by
      have hz : ∀ j, raw32245 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32245step0 = (fun i j => raw32245 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32245step0 raw32245; decide +kernel
      have hl : raw32245step0Labels = raw32245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32245 raw32245Labels permutation346 hz
    mixedMoment B raw32245step0 raw32245step0Labels = mixedMoment B raw32245step1 raw32245step1Labels := by
      have ha : raw32245step1 = (fun i j => raw32245step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32245step1 raw32245step0; decide +kernel
      have hl : raw32245step1Labels = raw32245step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32245step0 raw32245step0Labels permutation32 permutation6
    mixedMoment B raw32245step1 raw32245step1Labels = mixedMoment B raw32245step2 raw32245step2Labels := by
      have ha : raw32245step2 = raw32245step1 := by apply Matrix.ext; unfold raw32245step2 raw32245step1; decide +kernel
      have hl : raw32245step1Labels = labelEmbedding9 ∘ raw32245step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32245step1 raw32245step1Labels raw32245step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw32246 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw32246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw32246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32246step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32246step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32246step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32246 raw32246Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw32246 raw32246Labels = mixedMoment B raw32246step0 raw32246step0Labels := by
      have hz : ∀ j, raw32246 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32246step0 = (fun i j => raw32246 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32246step0 raw32246; decide +kernel
      have hl : raw32246step0Labels = raw32246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32246 raw32246Labels permutation346 hz
    mixedMoment B raw32246step0 raw32246step0Labels = mixedMoment B raw32246step1 raw32246step1Labels := by
      have ha : raw32246step1 = (fun i j => raw32246step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32246step1 raw32246step0; decide +kernel
      have hl : raw32246step1Labels = raw32246step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32246step0 raw32246step0Labels permutation32 permutation6
    mixedMoment B raw32246step1 raw32246step1Labels = mixedMoment B raw32246step2 raw32246step2Labels := by
      have ha : raw32246step2 = raw32246step1 := by apply Matrix.ext; unfold raw32246step2 raw32246step1; decide +kernel
      have hl : raw32246step1Labels = labelEmbedding9 ∘ raw32246step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32246step1 raw32246step1Labels raw32246step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw32247 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw32247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32247step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32247step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32247 raw32247Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw32247 raw32247Labels = mixedMoment B raw32247step0 raw32247step0Labels := by
      have ha : raw32247step0 = (fun i j => raw32247 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32247step0 raw32247; decide +kernel
      have hl : raw32247step0Labels = raw32247Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32247 raw32247Labels permutation152 permutation6
    mixedMoment B raw32247step0 raw32247step0Labels = mixedMoment B raw32247step1 raw32247step1Labels := by
      have ha : raw32247step1 = raw32247step0 := by apply Matrix.ext; unfold raw32247step1 raw32247step0; decide +kernel
      have hl : raw32247step0Labels = labelEmbedding9 ∘ raw32247step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32247step0 raw32247step0Labels raw32247step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5138 node5138Labels := by rfl

def raw32248 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw32248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw32248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32248step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32248step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32248step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32248 raw32248Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw32248 raw32248Labels = mixedMoment B raw32248step0 raw32248step0Labels := by
      have hz : ∀ j, raw32248 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32248step0 = (fun i j => raw32248 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32248step0 raw32248; decide +kernel
      have hl : raw32248step0Labels = raw32248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32248 raw32248Labels permutation346 hz
    mixedMoment B raw32248step0 raw32248step0Labels = mixedMoment B raw32248step1 raw32248step1Labels := by
      have ha : raw32248step1 = (fun i j => raw32248step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32248step1 raw32248step0; decide +kernel
      have hl : raw32248step1Labels = raw32248step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32248step0 raw32248step0Labels permutation32 permutation6
    mixedMoment B raw32248step1 raw32248step1Labels = mixedMoment B raw32248step2 raw32248step2Labels := by
      have ha : raw32248step2 = raw32248step1 := by apply Matrix.ext; unfold raw32248step2 raw32248step1; decide +kernel
      have hl : raw32248step1Labels = labelEmbedding9 ∘ raw32248step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32248step1 raw32248step1Labels raw32248step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw32249 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw32249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw32249step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw32249step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32249step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw32249step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32249 raw32249Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw32249 raw32249Labels = mixedMoment B raw32249step0 raw32249step0Labels := by
      have hz : ∀ j, raw32249 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32249step0 = (fun i j => raw32249 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32249step0 raw32249; decide +kernel
      have hl : raw32249step0Labels = raw32249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32249 raw32249Labels permutation346 hz
    mixedMoment B raw32249step0 raw32249step0Labels = mixedMoment B raw32249step1 raw32249step1Labels := by
      have ha : raw32249step1 = (fun i j => raw32249step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32249step1 raw32249step0; decide +kernel
      have hl : raw32249step1Labels = raw32249step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32249step0 raw32249step0Labels permutation32 permutation6
    mixedMoment B raw32249step1 raw32249step1Labels = mixedMoment B raw32249step2 raw32249step2Labels := by
      have ha : raw32249step2 = raw32249step1 := by apply Matrix.ext; unfold raw32249step2 raw32249step1; decide +kernel
      have hl : raw32249step1Labels = labelEmbedding9 ∘ raw32249step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32249step1 raw32249step1Labels raw32249step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

def raw32250 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32250step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32250step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32250step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32250 raw32250Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw32250 raw32250Labels = mixedMoment B raw32250step0 raw32250step0Labels := by
      have hz : ∀ j, raw32250 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32250step0 = (fun i j => raw32250 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32250step0 raw32250; decide +kernel
      have hl : raw32250step0Labels = raw32250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32250 raw32250Labels permutation346 hz
    mixedMoment B raw32250step0 raw32250step0Labels = mixedMoment B raw32250step1 raw32250step1Labels := by
      have ha : raw32250step1 = (fun i j => raw32250step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32250step1 raw32250step0; decide +kernel
      have hl : raw32250step1Labels = raw32250step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32250step0 raw32250step0Labels permutation32 permutation6
    mixedMoment B raw32250step1 raw32250step1Labels = mixedMoment B raw32250step2 raw32250step2Labels := by
      have ha : raw32250step2 = raw32250step1 := by apply Matrix.ext; unfold raw32250step2 raw32250step1; decide +kernel
      have hl : raw32250step1Labels = labelEmbedding9 ∘ raw32250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32250step1 raw32250step1Labels raw32250step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4838 node4838Labels := by rfl

def raw32251 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32251step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32251step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32251step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32251 raw32251Labels = mixedMoment B node5104 node5104Labels := by
  calc
    mixedMoment B raw32251 raw32251Labels = mixedMoment B raw32251step0 raw32251step0Labels := by
      have hz : ∀ j, raw32251 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32251step0 = (fun i j => raw32251 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32251step0 raw32251; decide +kernel
      have hl : raw32251step0Labels = raw32251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32251 raw32251Labels permutation346 hz
    mixedMoment B raw32251step0 raw32251step0Labels = mixedMoment B raw32251step1 raw32251step1Labels := by
      have ha : raw32251step1 = (fun i j => raw32251step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32251step1 raw32251step0; decide +kernel
      have hl : raw32251step1Labels = raw32251step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32251step0 raw32251step0Labels permutation32 permutation6
    mixedMoment B raw32251step1 raw32251step1Labels = mixedMoment B raw32251step2 raw32251step2Labels := by
      have ha : raw32251step2 = raw32251step1 := by apply Matrix.ext; unfold raw32251step2 raw32251step1; decide +kernel
      have hl : raw32251step1Labels = labelEmbedding9 ∘ raw32251step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32251step1 raw32251step1Labels raw32251step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5104 node5104Labels := by rfl

def raw32252 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32252step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32252step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32252step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32252step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32252 raw32252Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw32252 raw32252Labels = mixedMoment B raw32252step0 raw32252step0Labels := by
      have ha : raw32252step0 = (fun i j => raw32252 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32252step0 raw32252; decide +kernel
      have hl : raw32252step0Labels = raw32252Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32252 raw32252Labels permutation152 permutation6
    mixedMoment B raw32252step0 raw32252step0Labels = mixedMoment B raw32252step1 raw32252step1Labels := by
      have ha : raw32252step1 = raw32252step0 := by apply Matrix.ext; unfold raw32252step1 raw32252step0; decide +kernel
      have hl : raw32252step0Labels = labelEmbedding9 ∘ raw32252step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32252step0 raw32252step0Labels raw32252step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5137 node5137Labels := by rfl

def raw32253 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32253step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32253step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32253step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32253 raw32253Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw32253 raw32253Labels = mixedMoment B raw32253step0 raw32253step0Labels := by
      have hz : ∀ j, raw32253 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32253step0 = (fun i j => raw32253 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32253step0 raw32253; decide +kernel
      have hl : raw32253step0Labels = raw32253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32253 raw32253Labels permutation346 hz
    mixedMoment B raw32253step0 raw32253step0Labels = mixedMoment B raw32253step1 raw32253step1Labels := by
      have ha : raw32253step1 = (fun i j => raw32253step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32253step1 raw32253step0; decide +kernel
      have hl : raw32253step1Labels = raw32253step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32253step0 raw32253step0Labels permutation32 permutation6
    mixedMoment B raw32253step1 raw32253step1Labels = mixedMoment B raw32253step2 raw32253step2Labels := by
      have ha : raw32253step2 = raw32253step1 := by apply Matrix.ext; unfold raw32253step2 raw32253step1; decide +kernel
      have hl : raw32253step1Labels = labelEmbedding9 ∘ raw32253step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32253step1 raw32253step1Labels raw32253step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw32254 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32254step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32254step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32254step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32254step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32254 raw32254Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw32254 raw32254Labels = mixedMoment B raw32254step0 raw32254step0Labels := by
      have hz : ∀ j, raw32254 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32254step0 = (fun i j => raw32254 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32254step0 raw32254; decide +kernel
      have hl : raw32254step0Labels = raw32254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32254 raw32254Labels permutation346 hz
    mixedMoment B raw32254step0 raw32254step0Labels = mixedMoment B raw32254step1 raw32254step1Labels := by
      have ha : raw32254step1 = (fun i j => raw32254step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32254step1 raw32254step0; decide +kernel
      have hl : raw32254step1Labels = raw32254step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32254step0 raw32254step0Labels permutation34 permutation6
    mixedMoment B raw32254step1 raw32254step1Labels = mixedMoment B raw32254step2 raw32254step2Labels := by
      have ha : raw32254step2 = raw32254step1 := by apply Matrix.ext; unfold raw32254step2 raw32254step1; decide +kernel
      have hl : raw32254step1Labels = labelEmbedding9 ∘ raw32254step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32254step1 raw32254step1Labels raw32254step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw32255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32255Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32255step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32255 raw32255Labels = mixedMoment B node1156 node1156Labels := by
  calc
    mixedMoment B raw32255 raw32255Labels = mixedMoment B raw32255step0 raw32255step0Labels := by
      have ha : raw32255step0 = (fun i j => raw32255 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32255step0 raw32255; decide +kernel
      have hl : raw32255step0Labels = raw32255Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32255 raw32255Labels permutation160 permutation2
    _ = mixedMoment B node1156 node1156Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
